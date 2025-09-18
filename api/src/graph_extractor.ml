open Tactician_ltac1_record_plugin
open Graph_def
open Names
open Declarations
open Context
open Ltac_plugin
open Tacexpr

let declare_bool_option ~name ~default =
  let key = ["Tactician"; "Neural"; name] in
  Goptions.declare_bool_option_and_ref
    ~depr:false ~name:(String.concat " " key)
    ~key ~value:default

let declare_int_option ~name ~default =
  let open Goptions in
  let key = ["Tactician"; "Neural"; name] in
  let r_opt = ref default in
  let optwrite v = r_opt := match v with | None -> default | Some v -> v in
  let optread () = Some !r_opt in
  let _ = declare_int_option {
      optdepr = false;
      optname = String.concat " " key;
      optkey = key;
      optread; optwrite
    } in
  fun () -> !r_opt

let declare_string_option ~name ~default =
  let open Goptions in
  let key = ["Tactician"; "Neural"; name] in
  let r_opt = ref default in
  let optwrite v = r_opt := v in
  let optread () = !r_opt in
  let _ = declare_string_option {
      optdepr = false;
      optname = String.concat " " key;
      optkey = key;
      optread; optwrite
    } in
  optread

let tactic_arguments_option = declare_bool_option ~name:"TacticArguments" ~default:true

type analyzed_tactic =
  { anonymized_tactic : glob_tactic_expr
  ; base_tactic : glob_tactic_expr
  ; interm_tactic : glob_tactic_expr
  ; args : Tactic_one_variable.var_type list
  ; tactic_exact : bool }

let analyze_tactic tac =
    let anonymized_tactic = Tactic_name_remove.tactic_name_remove tac in
    let tac = Tactic_normalize.tactic_normalize @@ Tactic_normalize.tactic_strict anonymized_tactic in
    let (args, tactic_exact), interm_tactic =
      if tactic_arguments_option () then
        Tactic_one_variable.tactic_one_variable tac
      else ([], true), tac in
    let base_tactic =
      if tactic_arguments_option () then
        Tactic_one_variable.tactic_strip tac
      else tac in
    { anonymized_tactic; base_tactic; interm_tactic; args; tactic_exact }

module ProjMap = CMap.Make(Projection.Repr)

let map_named f = function
  | Named.Declaration.LocalAssum (id, ty) ->
    let ty' = f ty in Named.Declaration.LocalAssum (id, ty')
  | Named.Declaration.LocalDef (id, v, ty) ->
    let v' = f v in
    let ty' = f ty in Named.Declaration.LocalDef (id, v', ty')

let with_depth f =
  let old = Topfmt.get_depth_boxes () in
  Fun.protect ~finally:(fun () -> Topfmt.set_depth_boxes old)
    (fun () -> Topfmt.set_depth_boxes (Some 32); f ())

let constr_str env evar_map t = Pp.string_of_ppcmds (Sexpr.format_oneline (
    Printer.pr_constr_env env evar_map t))

let hyp_to_string_safe env evar_map =
  let id_str id = Names.Id.to_string id.binder_name in
  function
  | Named.Declaration.LocalAssum (id, typ) ->
    id_str id ^ " : " ^ constr_str env evar_map typ
  | Named.Declaration.LocalDef (id, term, typ) ->
    id_str id ^ " := " ^ constr_str env evar_map term ^ " : " ^ constr_str env evar_map typ

(* Safe version of Learner_helper.proof_state_to_string *)
let proof_state_to_string_safe (hyps, concl) env evar_map =
  let goal = constr_str env evar_map concl in
  let hyps = List.rev hyps in
  let hyps = List.map (hyp_to_string_safe env evar_map) hyps in
  String.concat ", " hyps ^ " |- " ^ goal

type single_proof_state = (Constr.t, Constr.t) Named.Declaration.pt list * Constr.t * Evar.t
type proof_state = Evd.evar_map * (Evar.t -> single_proof_state) * single_proof_state
type outcome = proof_state * Constr.t * Evd.evar_map * (Evar.t -> single_proof_state) * proof_state list
type tactical_proof = (outcome list * glob_tactic_expr option) list
type env_extra = tactical_proof Id.Map.t * tactical_proof Cmap.t

(* TODO: All this conversion of proof states, sigmas and other things is really convoluted *)
let sigma_to_proof_state_lookup sigma (e : Evar.t) : single_proof_state =
  let info = Evd.find_undefined sigma e in
  List.map (map_named (EConstr.to_constr ~abort_on_undefined_evars:false sigma)) @@ Evd.evar_filtered_context info,
  EConstr.to_constr ~abort_on_undefined_evars:false sigma info.evar_concl,
  e

module type CICGraphMonadType = sig

  include Monad.Def
  type node
  type node_label
  type edge_label
  type children = (edge_label * node) list
  type 'a repr_t

  (** Graph drawing primitives *)
  val mk_node : node_label -> children -> node t
  val with_delayed_node : ?definition:bool -> (node -> ('a * node_label * children) t) -> 'a t
  val with_delayed_nodes : ?definition:bool ->int -> (node list -> ('a * (node_label * children) list) t) -> 'a t

  (** Registering and lookup of definitions *)
  type status =
    | NActual
    | NDischarged
    | NSubstituted
  type node_status = status * node

  val register_constant : Constant.t -> node -> unit t
  val find_constant : Constant.t -> node_status option t

  val register_inductive : inductive -> node -> unit t
  val find_inductive : inductive -> node_status option t

  val register_constructor : constructor -> node -> unit t
  val find_constructor : constructor -> node_status option t

  val register_projection : Projection.Repr.t -> node -> unit t
  val find_projection : Projection.Repr.t -> node_status option t

  val register_section_variable : Id.t -> node -> unit t
  val find_section_variable : Id.t -> node option t

  val get_previous_definition : node option t
  val drain_external_previous_definitions : node list t

  val find_evar     : Evar.t -> (node * node option array) option t
  val register_evar : Evar.t -> node -> node option array -> unit t

  (** Managing the local context *)
  val lookup_relative     : int -> node t
  val lookup_relative_opt : int -> node option t
  val lookup_named        : Id.t -> node t
      (* The array is the local context associated with the section, in the same ordering as would be given
        by an Evar node. If an element in the node is None, it is a section variable. *)
  val lookup_named_map    : node Id.Map.t t
  val lookup_def_depth    : int option t
  val lookup_env          : Environ.env t
  val lookup_env_extra    : env_extra t
  val lookup_include_metadata : bool t
  val lookup_include_opaque : bool t
  val lookup_proof_state  : Evar.t -> single_proof_state t

  val with_relative       : node -> 'a t -> 'a t
  val with_relatives      : node list -> 'a t -> 'a t
  val with_named          : Id.t -> node -> 'a t -> 'a t
  val with_empty_evars    : 'a t -> 'a t
  val with_empty_contexts : 'a t -> 'a t
  val with_decremented_def_depth : 'a t -> 'a t
  val with_env            : Environ.env -> 'a t -> 'a t
  val with_env_extra      : env_extra -> 'a t -> 'a t
  val with_evar_map       : (Evar.t -> single_proof_state) -> 'a t -> 'a t

  type definitions =
    { constants            : node_status Cmap.t
    ; inductives           : node_status Indmap.t
    ; constructors         : node_status Constrmap.t
    ; projections          : node_status ProjMap.t }
  type state =
    { previous : node option
    ; external_previous : node list
    ; section_nodes : node Id.Map.t
    ; definition_nodes : definitions}

  val run :
    ?include_metadata:bool -> ?include_opaque:bool -> ?def_depth:int -> state:state ->
    'a t -> (state * 'a) repr_t
  val run_empty :
    ?include_metadata:bool -> ?include_opaque:bool -> ?def_depth:int ->
    'a t -> (state * 'a) repr_t
end
module CICGraphMonad (G : GraphMonadType) : CICGraphMonadType
  with type node = G.node
   and type node_label = G.node_label
   and type edge_label = G.edge_label
   and type 'a repr_t = 'a G.repr_t = struct

  include G

  type status =
    | NActual
    | NDischarged
    | NSubstituted
  type node_status = status * node
  type definitions =
    { constants            : node_status Cmap.t
    ; inductives           : node_status Indmap.t
    ; constructors         : node_status Constrmap.t
    ; projections          : node_status ProjMap.t }
  type context =
    { relative     : node list
    ; named        : node Id.Map.t
    ; def_depth    : int option
    ; env          : Environ.env option
    ; env_extra    : env_extra option
    ; metadata     : bool
    ; opaque       : bool
    ; evar_map     : Evar.t -> single_proof_state }
  type state =
    { previous : node option
    ; external_previous : node list
    ; section_nodes : node Id.Map.t
    ; definition_nodes : definitions }
    type full_state = state * (node * node option array) Evar.Map.t

  module M = Monad_util.ReaderStateMonadT
      (G)
      (struct type r = context end)
      (struct type s = full_state end)
  module OList = List
  open M
  include Monad_util.WithMonadNotations(M)

  (** Lifting of basic drawing primitives *)
  let mk_node nl ch = M.lift @@ mk_node nl ch
  let with_delayed_node ?definition f = unrun @@ fun c s ->
    with_delayed_node ?definition (fun n ->
        G.map (fun (s, (a, nl, ch)) -> (s, a), nl, ch) (run (f n) c s))

  (* This is a typical function that would benefit greatly from having sized vectors! *)
  let with_delayed_nodes ?definition i f = unrun @@ fun c s ->
    with_delayed_nodes ?definition i (fun n ->
        G.map (fun (s, (a, chls)) -> (s, a), chls) (run (f n) c s))

  (** Registering and lookup of definitions *)

  let update_error x = function
    | None -> Some x
    | Some _ -> CErrors.anomaly (Pp.str "Map update attempt while key already existed")
  let update_error2 p x = function
    | None -> Some x
    | Some (NActual, _) -> CErrors.anomaly Pp.(str "Map update attempt while key already existed: " ++ p)
    | Some ((NDischarged | NSubstituted), _) -> Some x

  let register_constant c n =
    let* ({ definition_nodes = ({ constants; _ } as dn); _ } as s, se) = get in
    put ({ s with
          previous = Some n
        ; definition_nodes =
            { dn with constants = Cmap.update c (update_error2 (Constant.print c) (NActual, n)) constants }}, se)
  let find_constant c =
    let+ { definition_nodes = { constants; _ }; _ }, _ = get in
    Cmap.find_opt c constants

  let register_inductive i n =
    let* ({ definition_nodes = ({ inductives; _ } as dn); _ } as s, se) = get in
    put ({ s with
          previous = Some n
        ; definition_nodes =
            { dn with inductives = Indmap.update i (update_error2 (Pp.str "ind") (NActual, n)) inductives }}, se)
  let find_inductive i =
    let+ { definition_nodes = { inductives; _ }; _ }, _ = get in
    Indmap.find_opt i inductives

  let register_constructor c n =
    let* ({ definition_nodes = ({ constructors; _ } as dn); _ } as s, se) = get in
    put ({ s with
          previous = Some n
        ; definition_nodes =
            { dn with constructors =
                        Constrmap.update c (update_error2 (Pp.str "constr") (NActual, n)) constructors }}, se)
  let find_constructor c =
    let+ { definition_nodes = { constructors; _ }; _ }, _ = get in
    Constrmap.find_opt c constructors

  let register_projection p n =
    let* ({ definition_nodes = ({ projections; _ } as dn); _ } as s, se) = get in
    put ({ s with
          previous = Some n
        ; definition_nodes =
            { dn with projections = ProjMap.update p (update_error2 (Pp.str "proj") (NActual, n)) projections  }}, se)
  let find_projection p =
    let+ { definition_nodes = { projections; _ }; _ }, _ = get in
    ProjMap.find_opt p projections

  let register_section_variable id n =
    let* ({ section_nodes; _ } as s), se = get in
    put ({ s with
          previous = Some n
        ; section_nodes = Id.Map.update id (update_error n) section_nodes }, se)
  let find_section_variable id =
    let+ { section_nodes; _ }, _ = get in
    Id.Map.find_opt id section_nodes

  let get_previous_definition =
    let+ { previous; _ }, _ = get in
    previous
  let drain_external_previous_definitions =
    let open Monad.Make(M) in
    let* ({ external_previous; _ } as s, se) = get in
    let+ () = put ({ s with external_previous = [] }, se) in
    external_previous

  let find_evar e =
    let+ _, sigma = get in
    Evar.Map.find_opt e sigma
  let register_evar e n ns =
    let* s, sigma = get in
    put (s, Evar.Map.update e (update_error (n, ns)) sigma)

  (** Managing the local context *)
  let lookup_relative_opt i =
    let+ { relative; _ } = ask in
    let rec find ctx i = match ctx, i with
      | node::_, 1 -> Some node
      | _::ctx, n -> find ctx (n - 1)
      | [], _ -> None in
    find relative i
  let lookup_relative i =
    let+ no = lookup_relative_opt i in
    match no with
    | None -> CErrors.anomaly (Pp.str "Invalid relative context")
    | Some n -> n
  let lookup_named_map =
    let+ { named; _ } = ask in
    named
  let lookup_named id =
    let+ named = lookup_named_map in
    try
      Id.Map.find id named
    with Not_found -> CErrors.anomaly Pp.(str "Variable name " ++ Id.print id ++ str " could not be resolved")
  let lookup_def_depth =
    let+ { def_depth; _ } = ask in
    def_depth
  let lookup_env =
    let+ { env; _ } = ask in
    match env with
    | None -> CErrors.anomaly Pp.(str "No env was present in the graph extractor")
    | Some env -> env
  let lookup_env_extra =
    let+ { env_extra; _ } = ask in
    match env_extra with
    | None -> CErrors.anomaly Pp.(str "No extra env was present in the graph extractor")
    | Some env_extra -> env_extra
  let lookup_include_metadata =
    let+ { metadata; _ } = ask in
    metadata
  let lookup_include_opaque =
    let+ { opaque; _ } = ask in
    opaque
  let lookup_proof_state e =
    let+ { evar_map; _ } = ask in
      evar_map e

  let with_relative n =
    local (fun ({ relative; _ } as c) -> { c with relative = n::relative })
  let with_relatives ns =
    local (fun ({ relative; _ } as c) -> { c with relative = ns@relative })
  let with_named id n =
    local (fun ({ named; _ } as c) -> { c with named = Id.Map.update id (update_error n) named })
  let with_empty_evars m =
    let* (s, se) = get in
    let* () = put (s, Evar.Map.empty) in
    let* a = m in
    let* (s, _) = get in
    let+ () = put (s, se) in
    a
  let with_empty_contexts m =
    local (fun c -> { c with named = Id.Map.empty; relative = [] }) m
  let with_decremented_def_depth m =
    local (fun ({ def_depth; _ } as c) ->
        { c with def_depth = Option.map (fun def_depth -> assert (def_depth > 0); def_depth - 1) def_depth }) m
  let with_env env =
    local (fun c -> { c with env = Some env })
  let with_env_extra env_extra =
    local (fun c -> { c with env_extra = Some env_extra })
  let with_evar_map evar_map m =
    with_empty_evars @@ local (fun c -> { c with evar_map }) m

  let run ?(include_metadata=false) ?(include_opaque=true) ?def_depth ~state m =
    G.run @@
    let context =
      { relative = []; named = Id.Map.empty
      ; evar_map = (fun e -> CErrors.anomaly Pp.(str "Evar " ++ Evar.print e ++ str " not found"))
      ; def_depth; env = None; env_extra = None; metadata = include_metadata
      ; opaque = include_opaque } in
    G.map (fun ((s, se), a) -> s, a) @@ run m context (state, Evar.Map.empty)
  let run_empty ?(include_metadata=false) ?(include_opaque=true) ?def_depth m =
    let definition_nodes =
      { constants = Cmap.empty
      ; inductives = Indmap.empty
      ; constructors = Constrmap.empty
      ; projections = ProjMap.empty} in
    let state =
      { previous = None
      ; external_previous = []
      ; section_nodes = Id.Map.empty
      ; definition_nodes } in
    run ~include_metadata ~include_opaque ?def_depth ~state m
end

module GraphBuilder
    (G : sig
       type node'
       include CICGraphMonadType
         with type node = node'
          and type edge_label = edge_type
          and type node_label = node' node_type
     end) : sig
  open G
  type 'a with_envs = Environ.env -> env_extra -> 'a
  val gen_const               : (constant -> node t) with_envs
  val gen_mutinductive_helper : (mutind -> unit t) with_envs
  val gen_inductive           : (inductive -> node t) with_envs
  val gen_constructor         : (constructor -> node t) with_envs
  val gen_projection          : (Projection.t -> node t) with_envs
  val gen_constr              : (Constr.t -> node t) with_envs
  val gen_section_var         : (Id.t -> node t) with_envs
  val with_named_context      : ((Constr.t, Constr.t) Named.pt -> 'a t -> ((edge_type * node) list * 'a) t) with_envs
  val gen_proof_state         : (proof_state -> node Graph_def.proof_state t) with_envs
  val gen_proof_state_tactic  : env_extra -> node Graph_def.proof_state t Proofview.tactic
  val gen_globref             : (GlobRef.t -> node t) with_envs
end = struct

  type 'a with_envs = Environ.env -> env_extra -> 'a
  module OList = List
  open G
  open Monad.Make(G)
  open Monad_util.WithMonadNotations(G)

  let cached_gen_const c gen =
    let* n = find_constant c in
    match n with
    | Some (NActual, c) -> return c
    | _ -> with_empty_evars @@ with_empty_contexts gen

  let with_named_context gen_constr c (m : 'a t) =
    let* env = lookup_env in
    snd @@ Named.fold_inside (fun (index, m) d ->
        match d with
        | Named.Declaration.LocalAssum (id, typ) ->
          (try
             ignore (Environ.lookup_named id.binder_name env); (index, m)
           with Not_found ->
             index - 1,
             let* typ = gen_constr typ in
             let* var = mk_node (ContextAssum (index, id.binder_name)) [ContextDefType, typ] in
             let+ (ctx, v) = with_named id.binder_name var m in
             ((ContextElem, var)::ctx), v)
        | Named.Declaration.LocalDef (id, term, typ) ->
          (try
             ignore (Environ.lookup_named id.binder_name env); (index, m)
           with Not_found ->
             index - 1,
             let* typ = gen_constr typ in
             let* term = gen_constr term in
             let* var = mk_node (ContextDef (index, id.binder_name)) [ContextDefType, typ; ContextDefTerm, term] in
             let+ (ctx, v) = with_named id.binder_name var m in
             ((ContextElem, var)::ctx), v))
      c ~init:(OList.length c, (let+ m = m in [], m))

  (* This is used for definition leafs when we don't want to 'follow' definitions *)
  let mk_fake_definition def_type gref =
    (* TODO: Using the nametab here is very dangerous because it is mutable *)
    let path = Nametab.path_of_global gref in
    with_delayed_node @@ fun node ->
    return (node,
            Definition { previous = None; external_previous = []; def_type = def_type node;
                         path; status = DOriginal; term_text = None; type_text = "" },
            [])

  let mk_definition (def_type : node definition_type) gref mk_node =
    let* def =
      (* TODO: Using the nametab here is very dangerous because it is mutable *)
      let path = Nametab.path_of_global gref in
      let* previous = get_previous_definition
      and+ status = match def_type with
        | Ind (_, i) -> find_inductive i
        | Construct (_, c) -> find_constructor c
        | Proj (_, p) -> find_projection p
        | ManualConst c | TacticalConstant (c, _) -> find_constant c
        | ManualSectionConst c | TacticalSectionConstant (c, _) -> (* Always actual *) return None
      and+ external_previous = drain_external_previous_definitions
      and+ env = lookup_env in
      let status = match status with
        | None -> DOriginal
        | Some (NActual, _) -> CErrors.anomaly Pp.(str "Definition was already known as an actual while creating it")
        | Some (NDischarged, n) -> DDischarged n
        | Some (NSubstituted, n) -> DSubstituted n in
      let+ type_text, term_text =
        let+ b = lookup_include_metadata in
        if not b then "", None else
          let print c =
            (* This try is specifically aimed at catching errors coming from Coqlib.lib_ref, which is at least
               Known to happen in theories/Float/PrimFloat.v on line 92 *)
            try
              with_depth @@ fun () -> Pp.string_of_ppcmds @@ Sexpr.format_oneline @@
              Printer.pr_constr_env env Evd.empty c
            with CErrors.UserError _ -> ""
          in
          match def_type with
          | Ind (_, (m, i)) ->
            let ({ mind_packets; _ } as mb) =
              Environ.lookup_mind m env in
            let univs = Declareops.inductive_polymorphic_context mb in
            let inst = Univ.make_abstract_instance univs in
            let env = Environ.push_context ~strict:false (Univ.AUContext.repr univs) env in
            let typ = Inductive.type_of_inductive env ((mb, Array.get mind_packets i), inst) in
            print typ, None
          | Construct (_, ((m, i), c)) ->
            let ({ mind_packets; _ } as mb) =
              Environ.lookup_mind m env in
            let univs = Declareops.inductive_polymorphic_context mb in
            let inst = Univ.make_abstract_instance univs in
            let typ = Inductive.type_of_constructor (((m, i), c), inst) (mb, Array.get mind_packets i) in
            print typ, None
          (* TODO: Unclear what to do here, but this situation has already changed in newer Coq's *)
          | Proj _ -> "", None
          | ManualConst c | TacticalConstant (c, _) ->
            let { const_body; const_type; _ } = Environ.lookup_constant c env in
            let term_text = match const_body with
              | Undef _ -> None
              | Def c -> Some (print @@ Mod_subst.force_constr c)
              | OpaqueDef c ->
                let c, _ = Opaqueproof.force_proof Library.indirect_accessor (Environ.opaque_tables env) c in
                Some (print c)
              | Primitive p -> None in
            print const_type, term_text
          | ManualSectionConst id | TacticalSectionConstant (id, _) ->
            let def = Environ.lookup_named id env in
            match def with
            | Named.Declaration.LocalAssum (_, typ) ->
              print typ, None
            | Named.Declaration.LocalDef (_, term, typ) ->
              print typ, Some (print term)
      in
      Definition { previous; external_previous; def_type; path; status; type_text; term_text } in
    let* n = mk_node def in
    let+ () = match def_type with
      | Ind (_, i) -> register_inductive i n
      | Construct (_, c) -> register_constructor c n
      | Proj (_, p) -> register_projection p n
      | ManualConst c | TacticalConstant (c, _) -> register_constant c n
      | ManualSectionConst id | TacticalSectionConstant (id, _) -> register_section_variable id n in
    n, def

  let follow_def alt m =
    let* follow_defs = lookup_def_depth in
    match follow_defs with
    | None -> m
    | Some follow_defs ->
      if follow_defs > 0 then with_decremented_def_depth m else alt

  let rec gen_proof_state (evd, _, (hyps, concl, evar)) =
    let* env = lookup_env
    and+ metadata = lookup_include_metadata in
    let if_metadata f = if metadata then f () else "" in
    let env = Environ.push_named_context hyps @@ Environ.reset_context env in
    let+ root, arr = gen_evar evar in
    let ps_string = if_metadata @@ fun () -> proof_state_to_string_safe (hyps, concl) env evd in
    let concl_string = if_metadata @@ fun () -> constr_str env evd concl in
    let context = OList.rev @@ OList.filter_map (fun (hyp, node) ->
        let id = Named.Declaration.get_id hyp in
        Option.map (fun node -> { id; node
                                ; text = if_metadata @@ fun () ->hyp_to_string_safe env evd hyp }) node) @@
      OList.combine hyps @@ Array.to_list arr in
    { ps_string; concl_string; root; context; evar }
  and gen_proof_step (outcomes, tactic) =
    let* env = lookup_env
    and+ metadata = lookup_include_metadata in
    let if_metadata f = if metadata then f () else "" in
    let tactic, args =
      match tactic with
      | None -> None, []
      | Some tac ->
        let pr_tac t = Pp.string_of_ppcmds @@ Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
        let tactic_non_anonymous = tac in
        let { anonymized_tactic; base_tactic; interm_tactic; args; tactic_exact } = analyze_tactic tac in
        let tactic_hash = Tactic_hash.tactic_hash env base_tactic in
        try
          let tactic =
            if metadata then
              Some { tactic = pr_tac anonymized_tactic
                   ; tactic_non_anonymous = pr_tac tactic_non_anonymous
                   ; base_tactic = pr_tac base_tactic
                   ; interm_tactic = pr_tac interm_tactic
                   ; tactic_hash
                   ; tactic_exact }
            else
              Some { tactic = ""
                   ; tactic_non_anonymous = ""
                   ; base_tactic = ""
                   ; interm_tactic = ""
                   ; tactic_hash
                   ; tactic_exact } in
          tactic, args
        with e when CErrors.noncritical e || CErrors.is_anomaly e ->
          (* Aggressively catch errors during tactic printing.
             Sometimes the printing just errors out, mostly due to notations that no longer exist *)
          None, [] in
    let gen_outcome (((before_sigma, before_proof_states, (before_hyps, before_concl, before_evar)),
                      term, term_sigma, term_proof_states, after) : outcome) =
      let term_text =
        (* Note: We intentionally butcher evars here, because we want all evars of a term to be printed
           as underscores. This increases the chance that the term can be parsed back, because un-named
           evars can usually not be parsed, but underscores can. *)
        let beauti_evar c =
          let rec aux c =
            match CAst.(c.v) with
            | Constrexpr.CEvar (x, _) -> CAst.make @@ Constrexpr.CHole (None, IntroAnonymous, None)
            | _ -> Constrexpr_ops.map_constr_expr_with_binders (fun _ () -> ()) (fun () c -> aux c) () c in
          aux c in
        if_metadata @@ fun () ->
          let env = Environ.push_named_context before_hyps @@ Environ.reset_context env in
          let cexpr = beauti_evar @@ Constrextern.extern_constr false env term_sigma (EConstr.of_constr term) in
          Pp.string_of_ppcmds @@ Sexpr.format_oneline @@
          with_depth (fun () -> Ppconstr.pr_constr_expr env term_sigma cexpr) in
      let+ proof_states_after, proof_state_before, arguments, term =
        with_evar_map before_proof_states @@
        let* ctx, (proof_states_after, subject, arguments, map, term) =
          with_named_context gen_constr before_hyps @@
          let* subject = gen_constr before_concl
          and+ proof_states_after, term =
            with_evar_map term_proof_states @@
            let+ proof_states_after = List.map gen_proof_state after
            and+ term = gen_constr term in
            proof_states_after, term
          and+ map = lookup_named_map in
          let warn_arg id = () in
            (* let tac = match tactic with *)
            (*   | None -> "Unknown-tac" *)
            (*   | Some tactic -> tactic.tactic in *)
            (* Feedback.msg_warning Pp.(str "Unknown tactical argument: " ++ Id.print id ++ str " in tactic " ++ *)
            (*                          str tac (\* ++ str " in context\n" ++ *\) *)
            (*                          (\* prlist_with_sep (fun () -> str "\n") (fun (id, node) -> Id.print id ++ str " : ") context *\)) in *)
          let check_default id = function
            | None -> warn_arg id; None
            | x -> x in
          let+ arguments =
            let open Tactic_one_variable in
            List.map (function
                | TVar id ->
                  return @@ check_default id @@
                  Id.Map.find_opt id map
                | TRef c ->
                  (match c with
                   | GlobRef.VarRef id ->
                     (try
                        let def = Environ.lookup_named id env in
                        let+ c = gen_section_var id def in
                        Some c
                      with Not_found ->
                        return @@ check_default id @@
                        Id.Map.find_opt id map)
                   | GlobRef.ConstRef c ->
                     let+ c = gen_const c in
                     Some c
                   | GlobRef.IndRef i ->
                     let+ c = gen_inductive i in
                     Some c
                   | GlobRef.ConstructRef c ->
                     let+ c = gen_constructor c in
                     Some c
                  )
                | TOther -> return None
              ) args in
          proof_states_after, subject, arguments, map, term in
        let env = Environ.push_named_context before_hyps @@ Environ.reset_context env in
        let+ root = mk_node (ProofState before_evar) ((ContextSubject, subject)::ctx) in
        let ps_string = if_metadata @@ fun () ->
          proof_state_to_string_safe (before_hyps, before_concl) env before_sigma in
        let concl_string = if_metadata @@ fun () -> constr_str env before_sigma before_concl in
        let context = OList.rev @@ OList.filter_map (fun hyp ->
            let id = Named.Declaration.get_id hyp in
            Option.map (fun node -> { id; node
                                    ; text = if_metadata @@ fun () -> hyp_to_string_safe env before_sigma hyp }) @@
              Id.Map.find_opt id map) before_hyps in
        proof_states_after, { ps_string; concl_string; root; context; evar = before_evar }, arguments, term in
      { term; term_text; arguments; proof_state_before; proof_states_after } in
    let+ outcomes = List.map gen_outcome outcomes in
    { tactic; outcomes }
  and gen_const c : G.node t =
    (* Only process canonical constants *)
    let c = Constant.make1 (Constant.canonical c) in
    follow_def (mk_fake_definition (fun _self -> ManualConst c) (GlobRef.ConstRef c)) @@
    cached_gen_const c @@
    let gen_const_aux d p =
      let* env = lookup_env in
      let { const_body; const_type; _ } = Environ.lookup_constant c env in
      let* children =
        let bt, b = match const_body with
          | Undef _ -> ConstUndef, mk_node ConstEmpty []
          | Def c -> ConstDef, gen_constr @@ Mod_subst.force_constr c
          | OpaqueDef c ->
            let c =
              let* include_opaque = lookup_include_opaque in
              if include_opaque then
                let c, _ = Opaqueproof.force_proof Library.indirect_accessor (Environ.opaque_tables env) c in
                gen_constr c
              else
                mk_node ConstEmpty [] in
            ConstOpaqueDef, c
          | Primitive p -> ConstPrimitive, mk_node (Primitive p) [] in
        let+ b = b
        and+ typ = gen_constr const_type in
        [ ConstType, typ; bt, b ] in
      let+ (n, _) = mk_definition d p (fun d -> mk_node d children) in
      n
    in
    let* proofs = lookup_env_extra in
    let proof = Cmap.find_opt c @@ snd proofs in
    match proof with
    | None -> gen_const_aux (ManualConst c) (GlobRef.ConstRef c)
    | Some proof ->
      let* proof = List.map gen_proof_step proof in
      gen_const_aux (TacticalConstant (c, proof)) (GlobRef.ConstRef c)
  and gen_primitive_constructor representative ind proj_npars typ =
    let relctx, sort = Term.decompose_prod_assum typ in
    let real_arity = Rel.nhyps @@ CList.skipn proj_npars @@ OList.rev relctx in
    snd @@ CList.fold_left (fun (reli, m) -> function
        | Rel.Declaration.LocalAssum ({ binder_name = id; _ }, typ) ->
          reli - 1, with_delayed_node @@ fun prod ->
          let* typ = gen_constr typ in
          let* cont, prim_defs = with_relative prod m in
          let+ prim_defs = match id with
           | Name id when reli >= 0 ->
             let proj = Projection.Repr.make
                 ind ~proj_npars ~proj_arg:reli @@ Label.of_id id in
             (* TODO: This is clearly incorrect; something needs to be done about this.
                Note that newer versions of Coq already thread projections differently *)
             let const = GlobRef.ConstRef (Projection.Repr.constant proj) in
             let+ prim_def, _ = mk_definition (Proj (representative, proj)) const
                 (fun d -> mk_node d [ProjTerm, prod]) in
             prim_def::prim_defs
           | _ -> return prim_defs in
          (prod, prim_defs), (Prod id), [ProdType, typ; ProdTerm, cont]
        | Rel.Declaration.LocalDef ({ binder_name = id; _ }, def, typ) ->
          reli, with_delayed_node @@ fun letin ->
          let* typ = gen_constr typ in
          let* def = gen_constr def in
          let+ cont, prim_defs = with_relative letin m in
          (letin, prim_defs), (LetIn id), [LetInType, typ; LetInDef, def; LetInTerm, cont])
      (real_arity - 1, map (fun x -> x, []) @@ gen_constr sort) relctx
  and gen_mutinductive_helper m =
    (* Only process canonical inductives *)
    let m = MutInd.make1 (MutInd.canonical m) in
    let* c = find_inductive (m, 0) in
    match c with
    | Some (NActual, _) -> return ()
    | _ ->
      with_empty_evars @@ with_empty_contexts @@
      let* env = lookup_env in

      (* We have to ensure that all dependencies of the inductive are written away before
         we generate the inductive itself. This is needed, because we want all elements of
         the mutually recursive definition cluster to be adjacent in the global context.
         We only do this when we are still following definitions though, because otherwise
         we get dangling definition nodes. *)
      let* follow_defs = lookup_def_depth in
      let follow_defs = Option.default true @@ (Option.map (fun follow_defs -> follow_defs > 0)) follow_defs in
      (if follow_defs then
         let dependencies = Definition_order.mutinductive_in_order_traverse env GlobRef.Set.empty
             (fun c set -> GlobRef.Set.add (GlobRef.ConstRef c) set)
             (fun m set -> GlobRef.Set.add (GlobRef.IndRef (m, 0)) set)
             (fun id set -> GlobRef.Set.add (GlobRef.VarRef id) set) m in
         List.iter (fun r -> map (fun _ -> ()) @@ gen_globref r) @@
         GlobRef.Set.elements dependencies
       else return ()) >>

      with_empty_contexts @@
      let ({ mind_params_ctxt; mind_packets; mind_record; _ } as mb) =
        Environ.lookup_mind m env in
      let inds = OList.mapi (fun i ind -> i, ind) (Array.to_list mind_packets) in
      with_delayed_nodes ~definition:true (OList.length inds) @@ fun indsn ->
      let inds = OList.combine inds indsn in
      let indsn = OList.rev indsn in (* Backwards ordering w.r.t. Fun *)
      let representative = OList.hd indsn in
      let+ inds = List.map (fun ((i, ({ mind_user_lc; mind_consnames; _ } as ib)), n) ->
          let gen_constr_typ typ = match mind_record with
            | NotRecord | FakeRecord -> map (fun x -> x, []) @@ gen_constr typ
            | PrimRecord _ -> gen_primitive_constructor representative (m, i) (OList.length mind_params_ctxt) typ in
          let constructs = OList.mapi (fun j x -> j, x) @@
            OList.combine (Array.to_list mind_user_lc) (Array.to_list mind_consnames) in
          let* children =
            let* cstrs = List.map (fun (j, (typ, id)) ->
                with_relatives indsn @@
                let* typ, prim_defs = gen_constr_typ typ in
                let+ n, _ = mk_definition
                    (Construct (representative, ((m, i), j + 1))) (GlobRef.ConstructRef ((m, i), j + 1))
                    (fun d -> mk_node d [ConstructTerm, typ]) in
                (IndConstruct, n) :: OList.map (fun pd -> IndProjection, pd) prim_defs) constructs in
            let univs = Declareops.inductive_polymorphic_context mb in
            let inst = Univ.make_abstract_instance univs in
            let env = Environ.push_context ~strict:false (Univ.AUContext.repr univs) env in
            let typ = Inductive.type_of_inductive env ((mb, ib), inst) in
            let+ n = gen_constr typ in
            (IndType, n) :: OList.concat cstrs in
          let+ _, def = mk_definition (Ind (representative, (m, i))) (GlobRef.IndRef (m, i)) (fun d -> return n) in
          def, children
        ) inds in
      (), inds
  and gen_inductive ((m, _) as i) : G.node t =
    follow_def (mk_fake_definition (fun self -> Ind (self, i)) (GlobRef.IndRef i))
      (gen_mutinductive_helper m >>
       let+ n = find_inductive i in
       match n with
       | Some (NActual, inn) -> inn
       | _ -> CErrors.anomaly (Pp.str "Inductive generation problem"))
  and gen_constructor (((m, _), _) as c) : G.node t =
    follow_def (mk_fake_definition (fun self -> Construct (self, c)) (GlobRef.ConstructRef c))
      (gen_mutinductive_helper m >>
       let+ n = find_constructor c in
       match n with
       | Some (NActual, cn) -> cn
       | _ -> CErrors.anomaly (Pp.str "Inductive generation problem"))
  and gen_projection p =
    (* TODO: This is clearly incorrect; something needs to be done about this.
       Note that newer versions of Coq already treat projections differently *)
    let const = GlobRef.ConstRef (Projection.Repr.constant @@ Projection.repr p) in
    follow_def (mk_fake_definition (fun self -> Proj (self, Projection.repr p)) const)
      (gen_mutinductive_helper (Projection.mind p) >>
       let+ n = find_projection (Projection.repr p) in
       match n with
       | Some (NActual, cn) -> cn
       | _ -> CErrors.anomaly (Pp.str "Inductive generation problem"))
  and gen_section_var id def =
    let* sv = find_section_variable id in
    match sv with
    | None ->
      let gen_aux c =
        follow_def (mk_fake_definition (fun _self -> c) (GlobRef.VarRef id)) @@
        let* children =
          match def with
          | Named.Declaration.LocalAssum (_, typ) ->
            let+ typ = gen_constr typ
            and+ term = mk_node ConstEmpty [] in
            [ ConstType, typ; ConstUndef, term ]
          | Named.Declaration.LocalDef (_, term, typ) ->
            let+ typ = gen_constr typ
            and+ term = gen_constr term in
            [ ConstType, typ; ConstDef, term ]
        in
        let+ n, _ = mk_definition c (GlobRef.VarRef id) (fun d -> mk_node d children) in
        n in
      let* proofs = lookup_env_extra in
      let proof = Id.Map.find_opt id @@ fst proofs in
      (match proof with
       | None -> gen_aux (ManualSectionConst id)
       | Some proof ->
         let* proof = List.map gen_proof_step proof in
         gen_aux (TacticalSectionConstant (id, proof)))
    | Some sv -> return sv
  and gen_evar e : (node * node option array) t =
    let* n = find_evar e in
    match n with
    | Some c -> return c
    | None ->
      let* hyps, concl, _ = lookup_proof_state e in
      with_empty_contexts @@
      let* ctx, (subject, map) = with_named_context gen_constr hyps @@
        let* subject = gen_constr concl in
        let+ map = lookup_named_map in
        subject, map in
      let* root = mk_node (ProofState e) ((ContextSubject, subject)::ctx) in
      let arr = Array.of_list @@ OList.map (fun id -> Id.Map.find_opt id map) @@
        OList.map Named.Declaration.get_id hyps in
      let+ () = register_evar e root arr in
      root, arr
  and gen_constr c = gen_kind_of_term @@ Constr.kind c
  and gen_kind_of_term = function
    | Rel i ->
      let* ino = lookup_relative i in
      mk_node Rel [RelPointer, ino]
    | Var id ->
      let* env = lookup_env in
      (try
         let def = Environ.lookup_named id env in
         gen_section_var id def
       with Not_found ->
         lookup_named id)
    | Meta i ->
      CErrors.anomaly (Pp.str "Unexpected meta")
    | Evar (ev, substs) ->
      let* n, ctx = gen_evar ev in
      if not (Array.length ctx = Array.length substs) then
        CErrors.anomaly Pp.(str "Array length difference " ++
                            int (Array.length ctx) ++ str " " ++ int (Array.length substs));
      let substs = OList.filter_map (fun (x, y) -> Option.map (fun y -> x, y) y) @@
        OList.combine (Array.to_list substs) (Array.to_list ctx) in
      let* substs = List.map (fun (c, t) ->
          let* valid = match Constr.kind c with
            | Constr.Rel i ->
              let+ no = lookup_relative_opt i in
              (match no with
               | None ->
                 Feedback.msg_warning Pp.(str "Invalid term detected due to https://github.com/coq/coq/issues/17314");
                 false
               | Some _ -> true)
            | Constr.Var id ->
              let+ named = lookup_named_map in
              if Names.Id.Map.mem id named then true else
                (Feedback.msg_warning Pp.(str "Invalid term detected due to https://github.com/coq/coq/issues/17295");
                 false)
            | _ -> return true in
          if not valid then return (EvarSubstPointer, n)
          else
            let* c = gen_constr c in
            map (fun n -> EvarSubstPointer, n) @@
            mk_node EvarSubst [EvarSubstTerm, c; EvarSubstTarget, t]) substs in
      mk_node Evar ((EvarSubject, n)::substs)
    | Sort s ->
      mk_node (match s with
          | Sorts.SProp -> SortSProp
          | Sorts.Prop -> SortProp
          | Sorts.Set -> SortSet
          | Sorts.Type _ -> SortType) []
    | Cast (term, kind, typ) ->
      let* term = gen_constr term in
      let* typ = gen_constr typ in
      mk_node Cast [CastTerm, term; CastType, typ]
    | Prod (id, bi, conc) ->
      let* bi = gen_constr bi in
      with_delayed_node @@ fun prod ->
      let+ conc = with_relative prod @@ gen_constr conc in
      prod, (Prod id.binder_name), [ProdType, bi; ProdTerm, conc]
    | Lambda (id, typ, term) ->
      let* typ = gen_constr typ in
      with_delayed_node @@ fun lambda ->
      let+ term = with_relative lambda @@ gen_constr term in
      lambda, (Lambda id.binder_name), [LambdaType, typ; LambdaTerm, term]
    | LetIn (id, def, typ, term) ->
      let* def = gen_constr def in
      let* typ = gen_constr typ in
      with_delayed_node @@ fun letin ->
      let+ term = with_relative letin @@ gen_constr term in
      letin, (LetIn id.binder_name), [LetInType, typ; LetInDef, def; LetInTerm, term]
    | App (f, args) ->
      let* f = gen_constr f in
      List.fold_left (fun f arg ->
          let* arg = gen_constr arg in
          mk_node App [AppFun, f; AppArg, arg])
          f @@ Array.to_list args
    | Const (c, u) -> gen_const c
    | Ind (i, u) -> gen_inductive i
    | Construct (c, u) -> gen_constructor c
    | Case (i, ret, term, branches) ->
      let* ind = gen_inductive i.ci_ind in
      let* ret = gen_constr ret in
      let* term = gen_constr term in
      let* branches = List.map (fun (c, branch) ->
          let* cstr = gen_constructor (i.ci_ind, c + 1) in
          let* term = gen_constr branch in
          let+ branch = mk_node CaseBranch [CBConstruct, cstr; CBTerm, term] in
          CaseBranchPointer, branch)
          (OList.mapi (fun i x -> i, x) @@ Array.to_list branches) in
      mk_node Case ([CaseInd, ind; CaseReturn, ret; CaseTerm, term]@branches)
    | Fix ((offset, ret), (ids, typs, terms)) ->
      let* funs = with_delayed_nodes (Array.length ids) @@ fun funs ->
        let combined = OList.combine funs @@ OList.combine (Array.to_list ids) @@
          OList.combine (Array.to_list typs) (Array.to_list terms) in
        let+ children = List.map (fun (fn, (id, (typ, term))) ->
            let* typ = gen_constr typ in
            let+ term = with_relatives (OList.rev funs) @@ gen_constr term in
            (FixFun id.binder_name), [FixFunType, typ; FixFunTerm, term])
            combined in
        funs, children in
      mk_node Fix @@ (FixReturn, (OList.nth funs ret))::(OList.map (fun f -> FixMutual, f) funs)
    | CoFix (ret, (ids, typs, terms)) ->
      let* funs = with_delayed_nodes (Array.length ids) @@ fun funs ->
        let combined = OList.combine funs @@ OList.combine (Array.to_list ids) @@
          OList.combine (Array.to_list typs) (Array.to_list terms) in
        let+ children = List.map (fun (fn, (id, (typ, term))) ->
            let* typ = gen_constr typ in
            let+ term = with_relatives (OList.rev funs) @@ gen_constr term in
            (CoFixFun id.binder_name), [CoFixFunType, typ; CoFixFunTerm, term])
            combined in
        funs, children in
      mk_node CoFix @@ (CoFixReturn, (OList.nth funs ret))::(OList.map (fun f -> CoFixMutual, f) funs)
    | Proj (p, term) ->
      let* fn = gen_projection p in
      let* term = gen_constr term in
      mk_node App [AppFun, fn; AppArg, term]
    | Int n ->
      mk_node (Int n) []
    | Float f ->
      mk_node (Float f) []
  and gen_globref = function
    | GlobRef.VarRef id ->
      let* env = lookup_env in
      let def = Environ.lookup_named id env in
      gen_section_var id def
    | GlobRef.ConstRef c -> gen_const c
    | GlobRef.IndRef i -> gen_inductive i
    | GlobRef.ConstructRef c -> gen_constructor c


  let with_named_context ctx m = with_named_context gen_constr ctx m

  let with_envs f env env_extra x = with_env env (with_env_extra env_extra (f x))

  let gen_proof_state_tactic env_extra =
    (* NOTE: We intentionally get retrieve then environment here, because we don't want any of the
       local context elements of the proof state to be in the environment. If they are, they will be
       extracted as definitions instead of local variables. *)
    Proofview.tclBIND Proofview.tclENV @@ fun env ->
    Proofview.Goal.enter_one @@ fun g ->
    let sigma = Proofview.Goal.sigma g in
    let concl = EConstr.to_constr sigma @@ Proofview.Goal.concl g in
    let hyps = Proofview.Goal.hyps g in
    let evar = Proofview.Goal.goal g in
    let hyps = OList.map (map_named (EConstr.to_constr sigma)) hyps in
    Proofview.tclUNIT @@
    with_env env @@ with_env_extra env_extra @@
    let proof_state_lookup = sigma_to_proof_state_lookup sigma in
    with_evar_map proof_state_lookup @@
    gen_proof_state (sigma, proof_state_lookup, (hyps, concl, evar))

  let gen_section_var =
    with_envs @@ fun id ->
    let* env = lookup_env in
    let def = Environ.lookup_named id env in
    gen_section_var id def

  let gen_proof_state = with_envs gen_proof_state
  let gen_const = with_envs gen_const
  let gen_mutinductive_helper = with_envs gen_mutinductive_helper
  let gen_inductive = with_envs gen_inductive
  let gen_constructor = with_envs gen_constructor
  let gen_projection = with_envs gen_projection
  let gen_constr = with_envs gen_constr
  let with_named_context env env_extra ps = with_envs (with_named_context ps) env env_extra
  let gen_globref = with_envs gen_globref

end
