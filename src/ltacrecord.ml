open Ltac_plugin

open Util
open Tactician_util
open Tacexpr
open Tacenv
open Tactic_learner_internal
open TS
open Tactic_annotate
open Cook_tacexpr
open Search_strategy_internal

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let open_permanently file =
  open_out_gen [Open_creat; Open_text; Open_trunc; Open_wronly] 0o640 file

let global_record = ref true
let recordoptions = Goptions.{optdepr = false;
                              optname = "Tactician Record";
                              optkey = ["Tactician"; "Record"];
                              optread = (fun () -> !global_record);
                              optwrite = (fun b -> global_record := b)}
let _ = Goptions.declare_bool_option recordoptions

let _ = Random.self_init ()

(* TODO: In interactive mode this is a memory leak, but it seems difficult to properly clean this table *)
(* It might be possible to completely empty the db when a new lemma starts. *)
type semilocaldb = data_in list
let int64_to_knn : (Int64.t, semilocaldb * exn option * Safe_typing.private_constants) Hashtbl.t =
  Hashtbl.create 10

let subst_outcomes (s, { outcomes; tactic; name; status=_; path }) =
  let subst_tac tac =
    let tac = tactic_repr tac in
    TS.tactic_make (Tacsubst.subst_tactic s tac) in
  let subst_named_context =
    let open Mod_subst in
    let open Context in
    List.map (function
        | Named.Declaration.LocalAssum (id, typ) ->
          Named.Declaration.LocalAssum (id, subst_mps s typ)
        | Named.Declaration.LocalDef (id, term, typ) ->
          Named.Declaration.LocalDef (id, subst_mps s term, subst_mps s typ)
      ) in
  let subst_single_pf (hyps, g, evar) = Mod_subst.(subst_named_context hyps, subst_mps s g, evar) in
  let subst_pf (sigma, ustate, ps) = Evar.Map.map subst_single_pf sigma, ustate, subst_single_pf ps in
  let rec subst_pd = function
    | End -> End
    | Step ps -> Step (subst_ps ps)
  and subst_ps {executions; tactic} =
    { executions = List.map (fun (ps, pd) -> subst_pf ps, subst_pd pd) executions
    ; tactic = Option.map subst_tac tactic } in
  let subst_result (term, sigma, ustate, pss) =
    Mod_subst.subst_mps s term,
    Evar.Map.map subst_single_pf sigma,
    ustate,
    List.map subst_single_pf pss in
  let outcomes = List.map (fun { parents; siblings; before; result } ->
      { parents = List.map (fun (psa, pse) -> (subst_pf psa, subst_ps pse)) parents
      ; siblings = subst_pd siblings
      ; before = subst_pf before
      ; result = subst_result result }) outcomes in
  let name = Mod_subst.subst_constant s name in
  let path' =
    (* TODO: This is not ideal, but seems to work in practice *)
    let open Names in
    let (mp, id) = KerName.repr @@ Constant.user name in
    let rec modpath_to_dirpath = function
      | MPfile dp -> DirPath.repr dp
      | MPbound b ->
        let (_, id, dp) = MBId.repr b in
        id :: DirPath.repr dp
      | MPdot (mp, l) -> Label.to_id l :: modpath_to_dirpath mp in
    Libnames.make_path (DirPath.make @@ modpath_to_dirpath mp) @@ Label.to_id id in

  { outcomes; name; tactic = Option.map subst_tac tactic
  ; status = Substituted path; path = path' }

let tmp_ltac_defs = Summary.ref ~name:"TACTICIANTMPSECTION" []
let in_section_ltac_defs : (Names.KerName.t * glob_tactic_expr) list -> Libobject.obj =
  Libobject.(declare_object (local_object "LTACRECORDSECTIONLTACS"
                               ~cache:(fun (_obj, p) -> tmp_ltac_defs := p::!tmp_ltac_defs)
                               ~discharge:(fun (_obj, p) -> Some p)))

let rec with_let_prefix ltac_defs tac =
  let ids, tac = rebuild tac in
  let kername_tolname id = CAst.make (Names.(Name.mk_name (Label.to_id (KerName.label id)))) in
  let ltac_to_let rem_defs ltacset int =
    TacLetIn (true,
              List.map (fun (id, tac) -> (kername_tolname id, Tacexp (with_let_prefix rem_defs tac))) ltacset,
              int) in
  let rec prefix acc = function
    | [] -> acc
    | ltacset::rem ->
      let set_occurs = List.fold_right (fun (id, _) b ->
          b || Names.KNset.mem id ids) ltacset false in
      if set_occurs then
        prefix (ltac_to_let rem ltacset acc) rem else
        prefix acc rem in
  prefix tac ltac_defs

let rebuild_outcomes { outcomes; tactic; name; status=_; path } =
  let rebuild_tac tac = tactic_make (with_let_prefix !tmp_ltac_defs (tactic_repr tac)) in
  let rec rebuild_pd = function
    | End -> End
    | Step ps -> Step (rebuild_ps ps)
  and rebuild_ps {executions; tactic} =
    { executions = List.map (fun (ps, pd) -> ps, rebuild_pd pd) executions
    ; tactic = Option.map rebuild_tac tactic } in
  let outcomes = List.map (fun { parents; siblings; before; result } ->
      { parents = List.map (fun (psa, pse) -> (psa, rebuild_ps pse)) parents
      ; siblings = rebuild_pd siblings
      ; before; result }) outcomes in
  { outcomes; tactic = Option.map rebuild_tac tactic
  ; name; status = Discharged path; path = Lib.make_path @@ Libnames.basename path }

let discharge_outcomes senv { outcomes; tactic; name; status; path } =
  try
    let sections = Safe_typing.sections_of_safe_env senv in
    let env = Safe_typing.env_of_safe_env senv in
    let modlist = Section.replacement_context env sections in
    let secctx = Environ.named_context env in
    let constantctx = if Environ.mem_constant name env
      then Names.Id.Set.of_list @@
        List.map Context.Named.Declaration.get_id @@ (Environ.lookup_constant name env).const_hyps
      else raise Not_found in
    let irrelevantctx = Names.Id.Set.of_list @@ List.filter
        (fun x -> not @@ Names.Id.Set.mem x constantctx) @@ List.map Context.Named.Declaration.get_id secctx in
    let mk_mask hyps =
      List.map (fun x -> not @@ Names.Id.Set.mem (Context.Named.Declaration.get_id x) irrelevantctx) hyps in
    let discharge_constr masks t =
      let t = Cooking.expmod_constr modlist t in
      let rec fix_evars c =
        match Constr.kind c with
        | Constr.Evar (e, subst) ->
          let subst = Array.filter_with (Evar.Map.find e masks) subst in
          Constr.of_kind (Constr.Evar (e, subst))
        | _ -> Constr.map fix_evars c in
      fix_evars t in
    let discharge_tactic t ctx evd =
      let t = tactic_repr t in
      let env = Environ.push_named_context ctx @@ Environ.reset_context env in
      tactic_make @@ Discharge_tacexpr.discharge t env evd modlist in
    let discharge_single_proof_state masks (ctx, concl, ev) =
      List.map (Tactician_util.map_named (discharge_constr masks)) @@
      List.filter (fun x -> not @@ Names.Id.Set.mem (Context.Named.Declaration.get_id x) irrelevantctx) ctx,
      discharge_constr masks concl, ev in
    let discharge_proof_state (map, ustate, (_, _, pse)) =
      let masks = Evar.Map.map (fun (hyps, _, _) -> mk_mask hyps) map in
      let map = Evar.Map.map (discharge_single_proof_state masks) map in
      map, ustate, Evar.Map.find pse map in
    let rec discharge_pd = function
      | End -> End
      | Step ps -> Step (discharge_ps ps)
    and discharge_ps {executions; tactic} =
      { executions = List.map (fun (ps, pd) -> discharge_proof_state ps, discharge_pd pd) executions
      ; tactic = if executions = [] then tactic else
            Option.map (fun t -> discharge_tactic t
                           (Tactic_learner_internal.TS.proof_state_hypotheses (fst @@ List.hd executions))
                           (Tactic_learner_internal.TS.proof_state_sigma (fst @@ List.hd executions))) tactic } in
    let discharge_result before_masks (term, map, ustate, pss) =
      let masks = Evar.Map.map (fun (hyps, _, _) -> mk_mask hyps) map in
      let map = Evar.Map.map (discharge_single_proof_state masks) map in
      discharge_constr before_masks term, map, ustate, List.map (fun (_, _, e) -> Evar.Map.find e map) pss in
    let tactic = if outcomes = [] then tactic else
        Option.map (fun t -> discharge_tactic t
                       (Tactic_learner_internal.TS.proof_state_hypotheses (List.hd outcomes).before)
                       (Tactic_learner_internal.TS.proof_state_sigma (List.hd outcomes).before)) tactic in
    let outcomes = List.map (fun {parents; siblings; before; result} ->
        let before_masks =
          let map, _, _ = before in
          Evar.Map.map (fun (hyps, _, _) -> mk_mask hyps) map in
        { parents = List.map (fun (psa, pse) -> (psa, discharge_ps pse)) parents
        ; siblings = discharge_pd siblings
        ; before = discharge_proof_state before
        ; result = discharge_result before_masks result }) outcomes in
    Some { outcomes; tactic; name; status; path }
  with Not_found -> None

let section_ltac_helper bodies =
  tmp_ltac_defs := []; (* Safe to discard tmp state from old section discharge *)
  let ist = Tacintern.make_empty_glob_sign () in
  let intern t = Tacintern.intern_tactic_or_tacarg ist t in
  let def_trans = function
    | TacticDefinition (id, tac) ->
      Lib.make_kn CAst.(id.v), intern tac
    | TacticRedefinition (id, tac) ->
      Tacenv.locate_tactic id, intern tac in
  if not (Global.sections_are_opened ()) then () else
    Lib.add_anonymous_leaf (in_section_ltac_defs (List.map def_trans bodies))

(* TODO: Ugly hack. It seems impossible to obtain the Kername that a notation
   was assigned from outside Tacentries or Tacenv. Therefore we simulate the
   Kernname generation function in Tacenv. However, we don't know how many
   times it was called before, so we have to do a search to find the correct id. *)
let find_last_key : (string * string option) Tacentries.grammar_tactic_prod_item_expr list -> Names.KerName.t =
  let open Tacentries in
  let open Names in
  let id = Summary.ref ~name:"TACTICIAN-NOTATION-COUNTER" 0 in
  fun prods ->
    let map = function
      | TacTerm s -> s
      | TacNonTerm _ -> "#"
    in
    let prods = String.concat "_" (List.map map prods) in
    let rec next () =
      let cur = incr id; !id in
      (* We embed the hash of the kernel name in the label so that the identifier
         should be mostly unique. This ensures that including two modules
         together won't confuse the corresponding labels. *)
      let hash = (cur lxor (ModPath.hash (Lib.current_mp ()))) land 0x7FFFFFFF in
      let lbl = Id.of_string_soft (Printf.sprintf "%s_%08X" prods hash) in
      let name = Lib.make_kn lbl in
      if Tacenv.check_alias name then name else next () in
    next ()

let section_notation_helper prods _e =
  tmp_ltac_defs := []; (* Safe to discard tmp state from old section discharge *)
  if Global.sections_are_opened () then
    let id = find_last_key prods in
    let alias = Tacenv.interp_alias id in
    let func = TacFun (List.map Names.Name.mk_name alias.alias_args, alias.alias_body) in
    Lib.add_anonymous_leaf (in_section_ltac_defs [id, func])

(* TODO: Determining where we have to call this exactly is tricky business *)
let load_plugins () =
  let open Mltop in
  let plugins = [("ssreflect_plugin", "tactician_ssreflect_plugin")] in
  let load (dep, target) =
    if module_is_known dep && not (module_is_known target) then
      declare_ml_modules false [target] in
  if module_is_known "tactician_ltac1_record_plugin" then
    List.iter load plugins

(* TODO: Hack: Option have the property that they are being read by Coq's stm (multiple times) on every
   vernac command. Hence, we can use it to execute arbitrary code. We use this to load extra plugins. *)
let load_plugin_hack_option =
  Goptions.{ optdepr = true
           ; optname = ""
           ; optkey = ["Tactician"; "Internal"; "LoadPluginHack"]
           ; optread = (fun () -> load_plugins (); false)
           ; optwrite = (fun _ -> ()) }
let () = Goptions.declare_bool_option load_plugin_hack_option

let in_db : data_in -> Libobject.obj =
  Libobject.(declare_object { (default_object "LTACRECORD") with
                              cache_function = (fun ((path, kn),({ outcomes; tactic; name=_; status; path=_ } : data_in)) ->
                                  learner_learn (kn, path, status) outcomes tactic)
                            ; load_function = (fun _ ((path, kn), { outcomes; tactic; name; status; path=_ }) ->
                                  if Names.KerName.equal (Names.Constant.canonical name) (Names.Constant.user name) then
                                    if !global_record then learner_learn (kn, path, status) outcomes tactic else ())
                            ; open_function = (fun _ (_, _) -> ())
                            ; classify_function = (fun data -> Libobject.Substitute data)
                            ; subst_function = (fun x ->
                                load_plugins (); subst_outcomes x)
                            ; discharge_function = (fun (_, data) ->
                                load_plugins ();
                                let senv = Global.safe_env () in
                                discharge_outcomes senv data)
                            ; rebuild_function = (fun data ->
                                rebuild_outcomes data)
                            })

let add_to_db (x : data_in) =
  ignore(Lib.add_leaf (Names.Label.to_id @@ Names.Constant.label x.name) (in_db x))

(* Types and accessors for state in the proof monad *)
type localdb = ((Proofview.Goal.t * EConstr.t * Evd.evar_map * Proofview.Goal.t list) list * glob_tactic_expr option) list
type goal_stack = Proofview.Goal.t list list
type tactic_trace = glob_tactic_expr option list
type state_id_stack = int list

let record_field : bool Evd.Store.field = Evd.Store.field ()
let name_field : (Names.Constant.t * Libnames.full_path) Evd.Store.field = Evd.Store.field ()
let localdb_field : localdb Evd.Store.field = Evd.Store.field ()
let goal_stack_field : goal_stack Evd.Store.field = Evd.Store.field ()
let tactic_trace_field : tactic_trace Proofview_monad.StateStore.field = Proofview_monad.StateStore.field ()
let state_id_stack_field : state_id_stack Proofview_monad.StateStore.field = Proofview_monad.StateStore.field ()

let modify_field fi g d =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun evm ->
  let store = Evd.get_extra_data evm in
  let data = match Evd.Store.get store fi with
    | None -> d ()
    | Some x -> x in
  let data', ret = g data in
  let evm' = Evd.set_extra_data (Evd.Store.set store fi data') evm in
  Unsafe.tclEVARS evm' <*> tclUNIT ret

let modify_field_goals fi g d =
  let open Proofview in
  let open Notations in
  let open Proofview_monad in
  Unsafe.tclGETGOALS >>= fun gls ->
  let gls', ret = List.split (List.mapi (fun i gl ->
      let bare = drop_state gl in
      let state = get_state gl in
      let data = match StateStore.get state fi with
        | None -> (d i)
        | Some x -> x in
      let data', ret = g i data in
      let state' = StateStore.set state fi data' in
      goal_with_state bare state', ret
    ) gls) in
  Unsafe.tclSETGOALS gls' <*> tclUNIT ret

let get_field_goal2 fi gl d =
  let open Proofview in
  let open Proofview_monad in
  let state = Goal.state gl in
  match StateStore.get state fi with
  | None -> d ()
  | Some x -> x

let set_record b =
  modify_field record_field (fun _ -> b, ()) (fun () -> true)

let set_name n =
  modify_field name_field (fun _ -> n, ())
    (fun () ->
       let id = Names.Id.of_string "__tactician__" in
       Names.Constant.make2 (Global.current_modpath ()) (Names.Label.of_id id), Lib.make_path @@ id)

let get_record () =
  modify_field record_field (fun b -> b, b) (fun () -> true)

let get_name () =
  modify_field name_field (fun n -> n, n)
    (fun () ->
       let id = Names.Id.of_string "__tactician__" in
       Names.Constant.make2 (Global.current_modpath ()) (Names.Label.of_id id), Lib.make_path @@ id)

let push_localdb x =
  modify_field localdb_field (fun db -> x::db, ()) (fun () -> [])

let empty_localdb () =
  modify_field localdb_field (fun db -> [], db) (fun () -> [])

let get_localdb () =
  modify_field localdb_field (fun db -> db, db) (fun () -> [])

let push_goal_stack gls =
  let open Proofview in
  let open Notations in
  modify_field goal_stack_field (fun st -> gls::st, ()) (fun () -> []) >>=
  fun _ -> tclUNIT ()

let pop_goal_stack () =
  modify_field goal_stack_field (fun st -> List.tl st, List.hd st) (fun () -> assert false)

let push_state_id_stack () =
  let open Proofview in
  let open Notations in
  modify_field_goals state_id_stack_field (fun i st -> i::st, ()) (fun _ -> []) >>=
  fun _ -> tclUNIT ()

let warn tac =
  let msg tac =
      Feedback.msg_warning Pp.(str "Tactician has uncovered a bug in a tactic. Please report. " ++ tac) in
  match tac with
  | None ->
    msg (Pp.str "Unknown")
  | Some tac ->
    let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic (Global.env ()) t) in
    (* The unshelve tactic is the only tactic known to generate goals that do not inherit state from their
       parents (because those goals were on the shelf). We filter tactics expressions that contain this
       tactic out of the warning. *)
    let unshelve_ml = Tacexpr.{ mltac_name = { mltac_plugin = "ltac_plugin"; mltac_tactic = "unshelve" }
                              ; mltac_index = 0 } in
    if not (Find_tactic_syntax.contains_ml_tactic unshelve_ml tac) then
      msg (tac_pp tac)

let pop_state_id_stack tac2 =
  let open Proofview in
  let open Notations in
  (* Sometimes, a new goal does not inherit its id from its parent, and thus the id stack
     is too short. This happens for example when using `unshelve`. In that case, we assign 0 *)
  modify_field_goals state_id_stack_field (fun _ st ->
      match st with | [] -> warn tac2; [], 0 | x::xs -> xs, x)
    (fun _ -> []) >>=
  fun _ -> tclUNIT ()

(* TODO: We access this field from the Proofview.Goal.state, because I want to make
sure we only process user-visible goals. This is a bit convoluted though, because now
we access the top of the stack here, and then pop the stack with `pop_state_id_stack`. *)
let get_state_id_goal_top gl =
  (* Sometimes, a new goal does not inherit its id from its parent, and thus the id stack
     is too short. This happens for example when using `unshelve`. In that case, we assign 0 *)
  List.hd (get_field_goal2 state_id_stack_field gl (fun () -> [0]))

let push_tactic_trace tac =
  let open Proofview in
  let open Notations in
  modify_field_goals tactic_trace_field (fun _ st -> tac::st, ()) (fun _ -> []) >>=
  fun _ -> tclUNIT ()

let get_tactic_trace gl =
  get_field_goal2 tactic_trace_field gl (fun _ -> [])

let mk_outcome (st, term, sigma, sts) =
  (* let mem = (List.map TS.tactic_make (get_tactic_trace st)) in *)
  let st : proof_state = goal_to_proof_state st in
  { parents = [] (* List.map (fun tac -> (st (\* TODO: Fix *\), { executions = []; tactic = tac })) mem *)
  ; siblings = End
  ; before = st
  ; result = make_result term sigma sts }

let mk_data_in outcomes tactic name path =
  let tactic = Option.map TS.tactic_make tactic in
  let outcomes = List.map mk_outcome outcomes in
  { outcomes; tactic; name; status = Original; path }

let add_to_db2 id ((outcomes, tactic) : (Proofview.Goal.t * EConstr.t * Evd.evar_map * Proofview.Goal.t list) list *
                                        glob_tactic_expr option)
    sideff name path =
  let data = mk_data_in outcomes tactic name path in
  add_to_db data;
  let semidb, exn, _ = Hashtbl.find int64_to_knn id in
  Hashtbl.replace int64_to_knn id ({ data with status = QedTime }::semidb, exn, sideff)

let firstn n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc
    | n, h::t -> aux (h::acc) (pred n) t
    | _ -> List.rev acc
  in
  aux [] n l

let run_ml_tac name = TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = name}; mltac_index = 0}, []))

(* Running predicted tactics *)

let parse_tac tac =
    try
      Tacinterp.eval_tactic tac
    with
    e -> print_endline (Printexc.to_string e); flush_all (); assert false

let print_goal_short = Proofview.Goal.enter
    (fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let goal = Proofview.Goal.concl gl in
       (Proofview.tclLIFT (Proofview.NonLogical.print_info (Printer.pr_econstr_env env sigma (goal)))))

type witness_elem =
  { tac : glob_tactic_expr
  ; focus : int
  ; prediction_index : int }
let synthesize_tactic (env : Environ.env) tcss =
  let open Pp in
  let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
  let synthesize_single tcs =
    prlist_with_sep
      (fun () -> str "; ")
      (fun { tac; focus; _ } -> str "only" ++ spc () ++ int (1+focus) ++ str ":" ++ spc () ++ tac_pp tac) @@
    List.rev tcs in
  let rec loop = function
    | [] -> assert false
    | [tcs] -> synthesize_single tcs
    | tcs::tcss -> str "unshelve" ++ spc () ++ str "(" ++ synthesize_single tcs ++ str "); " ++ loop tcss in
  h 0 (str "synth" ++ spc () ++ str "with" ++ spc () ++ str "cache" ++ spc () ++ str "(" ++
       loop (List.rev tcss) ++ str ").")

let synthesize_trace tccs =
  List.map (fun { prediction_index; _ } -> prediction_index) @@
  List.concat tccs

let search_witness_field : witness_elem list list Evd.Store.field = Evd.Store.field ()
let push_witness w =
  modify_field search_witness_field (function s::ss -> (w::s)::ss, () | _ -> assert false) (fun () -> [])
let new_witness () =
  modify_field search_witness_field (fun ss -> []::ss, ()) (fun () -> [])
let get_witness () =
  modify_field search_witness_field (fun n -> n, n) (fun () -> [])
let empty_witness () =
  modify_field search_witness_field (fun _ -> [], ()) (fun () -> [])

let tclDebugTac t env debug =
    let open Proofview in
    let open Notations in
    (if debug then
      get_witness () >>= fun wit ->
      let mark = String.concat "." @@ List.map string_of_int @@ synthesize_trace wit in
      (tclLIFT @@ NonLogical.print_info
         Pp.(str "------------------------------" ++ fnl () ++
             str mark ++ fnl () ++ synthesize_tactic env wit ++ fnl () ++
             str "Exec: " ++ Pptactic.pr_glob_tactic env t)) <*>
      print_goal_short
     else tclUNIT ()) <*>
    tclPROGRESS @@ Timeouttac.tclTIMEOUTF 0.1 @@ parse_tac t

let predict () =
  let open Proofview in
  let open Notations in
  get_localdb () >>= fun db -> get_name () >>= fun (const, path) ->
  let learner = learner_get () in
  let learner = List.fold_left (fun learner (outcomes, tactic) ->
      let { outcomes; tactic; name; status; path} = mk_data_in outcomes tactic const path in
      learner.learn (Names.Constant.canonical name, path, status) outcomes tactic
    ) learner db in
  let predictor = learner.predict () in
  let cont =
    Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
    let situation = List.map (fun gl ->
        let ps = goal_to_proof_state gl in
        { parents = List.map (fun tac -> (ps (* TODO: Fix *), { executions = [](*TODO: Fix*); tactic = tac }))
              ([] (* List.map TS.tactic_make (get_tactic_trace gl) *))
        ; siblings = End
        ; state = ps}) gls in
    (* Coq stores goals in reverse order, so we present them in an intuitive order.
       Note that the tclFocus function also internally reverses the list, so focussing
       on goal zero will focus in the first goal of the reversed `situation` *)
    tclUNIT (predictor (List.rev situation)) in
  tclUNIT (learner, cont)

let filterTactics p q (tacs : Tactic_learner_internal.TS.prediction IStream.t) =
  let exception SuccessException of bool in
  let open Proofview in
  let open Notations in
  let rec aux n m tacs solve progress = match n = 0 || m = 0, IStream.peek tacs with
    | true, _ | _, IStream.Nil -> tclUNIT (firstn p (List.rev (if List.is_empty solve then progress else solve)))
    | false, IStream.Cons (Tactic_learner_internal.TS.{ tactic; _} as p, tacs) ->
      let tactic = parse_tac (tactic_repr tactic) in
      tclOR (
        tclPROGRESS (tclTIMEOUT 1 tactic) <*>
        (tclINDEPENDENT (tclZERO (SuccessException false))) <*> tclZERO (SuccessException true))
        (function
          | (SuccessException true, _) -> aux (n - 1) m tacs (p::solve) progress
          | (SuccessException false, _) -> aux n (m - 1) tacs solve (p::progress)
          | _ -> aux n m tacs solve progress)
  in aux p q tacs [] []

let print_rank debug env rank =
  let tac_pp env t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
  let strs = List.map (fun (x, t) -> (if debug then Printf.sprintf "%.4f " x else "") ^
                                     (Pp.string_of_ppcmds (tac_pp env t))) rank in
  Pp.str (String.concat "\n" strs)

let userPredict debug =
  let open Proofview in
  let open Notations in
  tclENV >>= fun env -> predict () >>= fun (_learner, cont) -> cont >>=
  (if debug then (fun r -> tclUNIT (to_list 10 r)) else filterTactics 10 10000) >>= fun r ->
  let r = List.map (fun ({confidence; focus; tactic} : Tactic_learner_internal.TS.prediction) ->
      (confidence, focus, tactic)) r in
  let r = List.map (fun (x, _, (y, _)) -> (x, y)) r in
  (* Print predictions *)
  (Proofview.tclLIFT (if List.is_empty r then
                        NonLogical.print_info (Pp.str "Ran out of suggestions to give...") else
                        Proofview.NonLogical.print_info (print_rank debug env r)))

let term_from_goal sigma gl =
  let open Proofview in
  let Evd.{ evar_body; _ } = Evd.find sigma @@ Goal.goal gl in
  match evar_body with
  | Evd.Evar_empty ->
    let ctx = Array.of_list @@
      List.map (fun pt -> EConstr.mkVar @@ Context.Named.Declaration.get_id pt) @@
      Goal.hyps gl in
    EConstr.mkEvar (Goal.goal gl, ctx)
  | Evd.Evar_defined term -> term

let tac_exec_count = ref 0
let tacpredict debug max_reached =
  let open Proofview in
  let open Notations in
  predict () >>= fun (learner, cont) ->
  let cont = cont >>= fun predictions ->
    let taceval i focus (t, h) = tclUNIT () >>= fun () ->
      if max_reached () then Tacticals.New.tclZEROMSG (Pp.str "Ran out of executions") else
        tclFOCUS ~nosuchgoal:(Tacticals.New.tclZEROMSG (Pp.str "Predictor gave wrong focus"))
          (focus+1) (focus+1)
          (Goal.enter_one (fun gl ->
               let env = Goal.env gl in
               push_witness { tac = t; focus; prediction_index = i } <*>
               (tac_exec_count := 1 + !tac_exec_count;
                tclDebugTac t env debug) >>= fun () ->
               Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
               tclEVARMAP >>= fun sigma ->
               let term = term_from_goal sigma gl in
               let outcome = mk_outcome (gl, term, sigma, gls) in
               tclUNIT (snd @@ learner.evaluate outcome (t, h)))) in
    let transform i (r : Tactic_learner_internal.TS.prediction) =
      { confidence = r.confidence; focus = r.focus; tactic = taceval i r.focus r.tactic } in
    tclUNIT (mapi (fun i p -> transform i p) predictions) in
  tclUNIT cont

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let search_recursion_depth_field : int Evd.Store.field = Evd.Store.field ()
let max_recursion_depth = 2
let inc_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> 1+n, n) (fun () -> 0)
let dec_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> (if n <= 0 then 0 else n - 1), ()) (fun () -> 0)
let get_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> n, n) (fun () -> 0)

let unshelve t =
  let open Proofview in
  let open Notations in
  with_shelf t >>= fun (gls, res) ->
  let gls = List.map with_empty_state gls in
  Unsafe.tclGETGOALS >>= fun ogls ->
  Unsafe.tclSETGOALS (gls @ ogls) >>= fun () ->
  tclUNIT (List.is_empty gls, res)

let search_and_unshelve max_reached predict =
  let open Proofview.Notations in
  let Cont s = search_with_strategy max_reached predict in
  let rec loop search =
    new_witness () <*> unshelve (Tacticals.New.tclCOMPLETE search) >>= fun (empty, Cont search) ->
    if empty then Proofview.tclUNIT () else loop search in
  loop s

let commonSearch debug max_exec =
    let open Proofview in
    let open Notations in
    (* TODO: Remove this hack *)
    let max_reached () = match max_exec with
      | None -> false
      | Some t -> !tac_exec_count >= t in
    (* We want to allow at least one nested search, such that users can embed search in more complicated
       expressions. But allowing infinite nesting will just lead to divergence. *)
    inc_search_recursion_depth () >>= fun n ->
    if n >= max_recursion_depth then Tacticals.New.tclZEROMSG (Pp.str "too much search nesting") else
      tacpredict debug max_reached >>= fun predict ->
      tclLIFT (NonLogical.make (fun () -> CWarnings.get_flags ())) >>= (fun oldFlags ->
          (* TODO: Find a way to reset dumbglob to original value. This is a temporary hack. *)
          let doFlags = n = 0 in
          let setFlags () = if not doFlags then tclUNIT () else tclLIFT (NonLogical.make (fun () ->
              Dumpglob.continue (); CWarnings.set_flags (oldFlags))) in
          (if not doFlags then tclUNIT () else
             tclLIFT (NonLogical.make (fun () ->
                 tac_exec_count := 0; Dumpglob.pause(); CWarnings.set_flags ("-all"))))
          <*> tclOR
            (tclONCE (search_and_unshelve max_reached predict) <*>
             get_witness () >>= fun wit -> empty_witness () <*>
             dec_search_recursion_depth () >>= fun () -> setFlags () <*> tclUNIT (wit, !tac_exec_count))
            (fun (e, i) -> setFlags () <*> tclZERO ~info:i e))

let solved_check t fail =
  let calc_defined_deps sigma es =
    let open Evd in
    Evar.Set.fold
      (fun e evs -> match (find sigma e).evar_body with
         | Evar_empty -> Evar.Set.add e evs
         | Evar_defined term -> Evar.Set.union evs @@ Evd.evars_of_term sigma term)
      es Evar.Set.empty in
  let open Proofview in
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
  tclEVARMAP >>= fun sigma_before ->
  let gls = Evar.Set.of_list @@ List.map Goal.goal gls in
  let gls_deps = Evar.Set.fold
      (fun e evs -> Tactic_learner_internal.calculate_deps sigma_before evs e)
      gls Evar.Set.empty in
  let gls_deps = Evar.Set.diff gls_deps gls in
  t >>= fun res ->
  tclENV >>= fun env -> tclEVARMAP >>= fun sigma ->
  let gls_deps_evars = calc_defined_deps sigma gls_deps in
  let gls_evars = calc_defined_deps sigma gls in
  let non_solved = Evar.Set.diff gls_evars gls_deps_evars in
  if Evar.Set.is_empty non_solved then tclUNIT res else fail non_solved res

let type_check t fail =
  let open Proofview in
  let open Notations in
  Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
  let gls = List.map Goal.goal gls in
  t >>= fun res ->
  tclENV >>= fun env -> tclEVARMAP >>= fun sigma ->
  try
    List.iter (fun ev ->
        let Evd.{ evar_body; evar_concl; _ } as info = Evd.find sigma ev in
        let env = Environ.reset_with_named_context (Evd.evar_filtered_hyps info) env in
        match evar_body with
        | Evd.Evar_empty -> ()
        | Evd.Evar_defined term -> ignore (Typing.check env sigma term evar_concl)
      ) gls;
    tclUNIT res
  with
  | Type_errors.TypeError (env, err) ->
    fail (`Type_error (env, sigma, err)) res
  | Pretype_errors.PretypeError (env, map, err) ->
    fail (`Pretype_error (env, map, err)) res

let benchmarked_field : bool Evd.Store.field = Evd.Store.field ()
let get_benchmarked () =
  modify_field benchmarked_field (fun b -> b, b) (fun () -> false)
let set_benchmarked () =
  modify_field benchmarked_field (fun _ -> true, ()) (fun () -> true)

let benchmarkSearch name time deterministic : unit Proofview.tactic =
  let open Proofview in
  let open Notations in
  let abstract_time = time in
  let timeout_command = if deterministic then fun x -> x else Timeouttac.ptimeout abstract_time in
  let max_exec = if deterministic then Some abstract_time else None in
  let print_success env (wit, count) start_time =
    let tdiff = Unix.gettimeofday () -. start_time in
    let tstring = Pp.string_of_ppcmds (synthesize_tactic env wit) in
    Benchmark.(send_bench_result (Found { lemma = Libnames.string_of_path name
                                        ; trace = synthesize_trace wit
                                        ; witness = tstring
                                        ; time = tdiff
                                        ; inferences = count }));
  in
  let start_time = Unix.gettimeofday () in
  timeout_command (tclENV >>= fun env ->
                   let solved_check_fail err (wit, _) =
                     let tstring = synthesize_tactic env wit in
                     let msg = Pp.(str "Incomplete witness for the following tactic:" ++ fnl () ++
                                   tstring ++ fnl () ++ str "Unsolved evars:" ++ fnl () ++
                                   prlist Evar.print (Evar.Set.elements err)) in
                     CErrors.anomaly msg in
                   let type_check_fail err (wit, _) =
                     let tstring = synthesize_tactic env wit in
                     let err = match err with
                       | `Type_error (env, sigma, err) ->
                         Himsg.explain_type_error env sigma @@ Type_errors.map_ptype_error EConstr.of_constr err
                       | `Pretype_error (env, sigma, err) -> Himsg.explain_pretype_error env sigma err in
                     let msg = Pp.(str "Typing failure of the following tactic:" ++ fnl () ++
                                   tstring ++ fnl () ++ str "Typing error:" ++ fnl () ++ err) in
                     CErrors.anomaly msg in
                   type_check (solved_check (commonSearch false max_exec) solved_check_fail) type_check_fail >>=
                   fun m -> print_success env m start_time; tclUNIT ())

let nested_search_solutions_field : witness_elem list list list Evd.Store.field = Evd.Store.field ()
let push_nested_search_solutions tcs =
  modify_field nested_search_solutions_field (fun acc -> tcs :: acc, ()) (fun () -> [])
let empty_nested_search_solutions () =
  modify_field nested_search_solutions_field (fun acc -> [], acc) (fun () -> [])
let userSearch debug =
    let open Proofview in
    let open Notations in
    tclUNIT () >>= fun () -> commonSearch debug None >>= fun (wit, _count) ->
    get_search_recursion_depth () >>= fun n ->
    if n >= 1 then push_nested_search_solutions wit else
      empty_nested_search_solutions () >>= fun acc -> tclENV >>= fun env ->
      let main_msg = Pp.(str "Tactician found a proof! The following tactic caches the proof:\n\n" ++
                         synthesize_tactic env wit) in
      let acc_msg = if List.is_empty acc then Pp.mt () else
          Pp.(str ("\n\nThe tactic above uses nested searching. The following tactics cache those nested searches.\n")
              ++ (prlist_with_sep fnl (synthesize_tactic env) acc)) in
      tclLIFT (NonLogical.print_info (Pp.(main_msg ++ acc_msg)))

(* Name globalization *)

(*
let id_of_global env = function
  | ConstRef kn -> Label.to_id (Constant.label kn)
  | IndRef (kn,0) -> Label.to_id (MutInd.label kn)
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) (Label.to_id l)

let dirpath_of_global = function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global env r =
  Libnames.make_qualid (dirpath_of_global r) (id_of_global env r)
*)

(* End name globalization *)

(* Tactic recording tactic *)

let should_record b =
  b && !global_record

let push_state_tac () =
  let open Proofview in
  let open Notations in
  get_record () >>= fun b -> if not (should_record b) then tclUNIT () else
    push_state_id_stack () <*> Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
    push_goal_stack gls

let record_tac (tac2 : glob_tactic_expr option) : unit Proofview.tactic =
  let open Proofview in
  let open Notations in
  tclEVARMAP >>= fun sigma ->
  let collect_states before_gls after_gls =
    List.map (fun gl_before ->
        let term = term_from_goal sigma gl_before in
        let i = get_state_id_goal_top gl_before in
        (gl_before, term, sigma, List.filter_map (fun (j, gl_after) ->
             if i = j then Some gl_after else None) after_gls)) before_gls in
  get_record () >>= fun b -> if not (should_record b) then tclUNIT () else
    pop_goal_stack () >>= fun before_gls ->
    Goal.goals >>= record_map (fun x -> x) >>= (fun after_gls ->
        let after_gls = List.map (fun gl -> get_state_id_goal_top gl, gl) after_gls in
        push_localdb (collect_states before_gls after_gls, tac2)
      ) >>= (fun () -> pop_state_id_stack tac2 <*> (* TODO: This is a strange way of doing things, see todo above. *)
                       push_tactic_trace tac2)

let ml_record_tac args _is =
  (*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*)
  let tac = Tacinterp.Value.cast (Genarg.topwit @@ Genarg.wit_opt wit_glbtactic) (List.hd args) in
  record_tac tac

let ml_push_state_tac _args _is =
  push_state_tac ()

let ml_fail_strict_tac args is =
  (*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*)
  let tac = Tacinterp.Value.cast (Genarg.topwit @@ Genarg.wit_opt wit_glbtactic) (List.hd args) in
  let tac = match tac with
    | None -> Pp.str "Unknown"
    | Some tac -> Pptactic.pr_glob_tactic (Global.env ()) tac in
  Feedback.msg_warning Pp.(str "Strict failure: " ++ tac);
  Proofview.tclUNIT ()

let () = register ml_record_tac "recordtac"
let () = register ml_push_state_tac "pushstatetac"
let () = register ml_fail_strict_tac "failstricttac"

let run_record_tac (tac : glob_tactic_expr option) : glob_tactic_expr =
  let enc = Genarg.in_gen (Genarg.glbwit @@ Genarg.wit_opt wit_glbtactic) tac in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "recordtac"}; mltac_index = 0},
                    [TacGeneric enc]))

let run_pushs_state_tac (): glob_tactic_expr =
  (*let tac_glob = Tacintern.intern_pure_tactic*)
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "pushstatetac"}; mltac_index = 0},
                []))

let fail_strict_tac (tac : glob_tactic_expr option) : glob_tactic_expr =
  let enc = Genarg.in_gen (Genarg.glbwit @@ Genarg.wit_opt wit_glbtactic) tac in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "failstricttac"}; mltac_index = 0},
                    [TacGeneric enc]))

(* This still needs some kind of nicer solution. See https://github.com/coq-tactician/coq-tactician/issues/14 *)
let record_tac_complete orig tac : glob_tactic_expr = (* TODO: Implement self-learning *)
  (* let strict_tac = Tactic_normalize.tactic_strict tac in *)
  TacThen (run_pushs_state_tac (), TacThen ((* TacFirst [strict_tac; TacThen (fail_strict_tac tac, *) tac, run_record_tac orig))

let record_tac_complete_ml orig tac =
  let open Proofview in
  let open Notations in
  push_state_tac () >>= fun () -> tac >>= fun () -> record_tac orig

let hide_interp_t global t ot rtac const path =
  let open Proofview in
  let open Notations in
  let hide_interp env =
    let ist = Genintern.empty_glob_sign env in
    let t = Tacintern.intern_pure_tactic ist t in
    let t = Tacinterp.eval_tactic @@ rtac t in
    let t = match ot with
      | None -> t
      | Some t' -> Tacticals.New.tclTHEN t (record_tac_complete_ml None t') in
    empty_localdb () >>= fun _ -> set_name (const, path) <*> t
  in
  if global then
    Proofview.tclENV >>= fun env ->
    hide_interp env
  else
    Proofview.Goal.enter begin fun gl ->
      hide_interp (Proofview.Goal.env gl)
    end

let vernac_solve ~pstate n info tcom b id =
  let print_error ~pstate ~pstate1 ~pstate2 =
    let open Proofview in
    let open Notations in
    let tac =
      let open Proofview in
      Proofview.tclENV >>= fun env ->
      let ist = Genintern.empty_glob_sign env in
      let t1 = Tacintern.intern_pure_tactic ist tcom in
      let t2 = decompose_annotate t1 (fun _ t -> t) in
      Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
      let msg = Pp.(
        str "Tactician found a bug in it's tactical decomposition. Please report." ++ fnl () ++
        Pptactic.pr_glob_tactic (Global.env ()) t1 ++ fnl () ++
        Pptactic.pr_glob_tactic (Global.env ()) t2 ++ fnl ()
        (* Printer.pr_open_subgoals_diff ~diffs:true ~oproof:pstate1 pstate2 ++ fnl () ++ *)
        (* Printer.pr_open_subgoals_diff ~diffs:true ~oproof:pstate2 pstate1 *)
      ) in
      Feedback.msg_warning msg; tclUNIT () in
    ignore (Pfedit.solve n info tac pstate) in
  let name = Proof_global.get_proof_name pstate in
  let const = Names.Constant.make2 (Global.current_modpath ()) (Names.Label.of_id name) in
  let path = Lib.make_path name in
  Benchmark.add_lemma path;
  let save_db env sideff (db : localdb) =
    let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
    let string_tac t = Pp.string_of_ppcmds (tac_pp t) in
    let tryadd (execs, tac) =
      let filter =
        match tac with
        | None -> false
        | Some tac ->
          try
            (* In v8.11 and v8.12, this is know to very occasionally crash (particularly for 'simpl in').
               Therefore, we have to wrap it in a try-catch. *)
            let s = string_tac tac in
            (* TODO: Move this to annotation time *)
            String.equal s "admit" || String.equal s "synth" || String.is_prefix "synth with cache" s
            || String.is_prefix "tactician ignore" s || String.is_prefix "fix" s || String.is_prefix "cofix" s
            || String.is_prefix "change_no_check" s || String.is_prefix "exact_no_checK" s
            || String.is_prefix "native_cast_no_check" s || String.is_prefix "vm_cast_no_check" s
            || String.is_prefix "shelve" s
          with _ -> false in
      if filter then () else add_to_db2 id (execs, tac) sideff const path;
      let msg typ t =
        Feedback.msg_warning Pp.(
            str "Tactician detected a " ++ str typ ++ str " problem " ++
            str "for the following tactic. " ++ str t ++ str " Please report.") in
      try (* This is purely for parsing bug detection and could be removed for performance reasons *)
        match tac with
        | None -> ()
        | Some tac ->
          let s = string_tac tac in
          try
            let _ = Pcoq.parse_string Pltac.tactic_eoi s in ()
          with _ -> msg "printing/parsing" s
      with _ -> msg "printing" "" in
    List.iter (fun trp -> tryadd trp) @@ List.rev db in
  (* Returns true if tactic execution should be skipped *)
  let pre_vernac_solve id =
    load_plugins ();
    let env = Global.env () in
    match Hashtbl.find_opt int64_to_knn id with
    | Some (db, exn, sideff) ->
      let aborted =
        let open Vernacexpr in
        let doc = Stm.get_doc 0 in
        Option.cata (fun CAst.{ v = { expr; _ }; _ } ->
            match expr with
            | VernacAbort _ | VernacEndProof Admitted -> true
            | _ -> false) true
          Stm.(get_ast ~doc (get_current_state ~doc)) in
      (if not aborted then
         let db = Inline_private_constants.inline env sideff db in
         List.iter add_to_db @@ List.rev db);
      Hashtbl.remove int64_to_knn id;
      (match exn with
       | None -> true
       | Some exn ->
         (* TODO: This is truly evil:
            Because Tactician registers tactics as side-effecting, the tactics are run again at Qed-time.
            Therefore, we have to actually prevent them from running. However, if tactics throw an exception, we still need to raise those,
            because the `Fail` command expects them. That works. However, this now causes `Fail` to print failure messages during Qed.
            In itself, this is not a huge problem, but it causes the IO-tests of some projects to fail (notably Iris). Therefore, we pull out
            another hugely ugly hack to temporarily block the message of `Fail` from being printed by replacing the formatter.
            This is extremely dangerous because it cannot be fully guaranteed that the formatter is being reset afterwards. *)
         let ignore_one_formatter original =
           let reset () = Topfmt.std_ft := original in
           Format.(formatter_of_out_functions
	                   { out_string = (fun _ _ _ -> reset ())
                     ; out_flush = (fun _ -> reset ())
                     ; out_newline = (fun _ -> reset ())
                     ; out_spaces = (fun _ -> reset ())
                     ; out_indent = (fun _ -> reset ())
                     }) in
         if not !Flags.quiet || !Vernacinterp.test_mode then begin
           Topfmt.std_ft := ignore_one_formatter !Topfmt.std_ft;
           raise exn
         end else raise exn)
    | None -> Hashtbl.add int64_to_knn id ([], None, Safe_typing.empty_private_constants); false in
  let skip = pre_vernac_solve id in
  if skip then pstate else
    try
      let open Proofview in
      let open Proofview.Notations in
      Benchmark.add_lemma path;
      let pstate, status = Proof_global.map_fold_proof_endline (fun etac p ->
          ignore (Pfedit.solve n None (
              get_benchmarked () >>= fun benchmarked ->
              if benchmarked then tclUNIT () else
                match Benchmark.should_benchmark path with
                | None -> tclUNIT ()
                | Some (time, deterministic) -> benchmarkSearch path time deterministic
            ) p);

          let with_end_tac = if b then Some etac else None in
          let global = match n with SelectAll | SelectList _ -> true | _ -> false in
          let info = Option.append info G_ltac.(!print_info_trace) in
          let (pstate1,status1) =
            Pfedit.solve n info
              (set_benchmarked () <*>
               hide_interp_t global tcom with_end_tac
                 (fun t -> record_tac_complete (Some t) t) const path) p in
          let p, status =
            (* If the 'abstract' tactic was used, we should not run the tactic a second time.
               The reason for this is that it will cause the numbering of the _subproofx names to
               diverge. And since these numbers may be referenced later, we must keep this consistent. *)
            let seff1 = (Evd.eval_side_effects (Proof.data p).sigma).seff_private in
            let seff2 = (Evd.eval_side_effects (Proof.data pstate1).sigma).seff_private in
            (* TODO: Temporary hack to prevent synth from being executed twice and producing output twice *)
            let is_synth =
              try
                let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic (Global.env ()) t) in
                let ist = Genintern.empty_glob_sign (Global.env ()) in
                let tcom = Tacintern.intern_pure_tactic ist tcom in
                let s = Pp.string_of_ppcmds (tac_pp tcom) in
              String.equal s "debug synth" || String.equal s "synth"
            with _ -> false in
            if seff1 <> seff2 || is_synth then
              pstate1, status1 else
              try
                let (pstate2,status2) =
                  (* TODO: Another dirty trick: We need to suppress any output generated during the
                     second run of the decomposed tactic. This is because some projects have IO-tests
                     that fail when things are printed twice. *)
                  let ignore_formatter () =
                    Format.(formatter_of_out_functions
	                            { out_string = (fun _ _ _ -> ())
                              ; out_flush = (fun _ -> ())
                              ; out_newline = (fun _ -> ())
                              ; out_spaces = (fun _ -> ())
                              ; out_indent = (fun _ -> ())
                              }) in
                  let original = !Topfmt.std_ft in
                  Topfmt.std_ft := ignore_formatter ();
                  Fun.protect ~finally:(fun () -> Topfmt.std_ft := original) @@ fun () ->
                  Pfedit.solve n info
                    (set_benchmarked () <*>
                     hide_interp_t global tcom with_end_tac
                       (fun t -> decompose_annotate t record_tac_complete) const path) p in
                if Proof_equality.pstate_equal ~pstate1 ~pstate2 then
                  pstate2, status2
                else
                  (print_error ~pstate:p ~pstate1 ~pstate2;
                   pstate1, status1)
              with
              | e when CErrors.noncritical e ->
                let msg = Pp.(str "Tactician's tactical decomposition crashed. Please report.") in
                Feedback.msg_warning msg;
                pstate1, status1
          in
          let env = Global.env () in
          let Proof.{ sigma; _ } = Proof.data p in
          let sideff = Evd.eval_side_effects sigma in
          let store = Evd.get_extra_data sigma in
          let data = Option.get @@ Evd.Store.get store localdb_field in
          save_db env sideff.seff_private data;
         (* in case a strict subtree was completed,
             go back to the top of the prooftree *)
          let p = Proof.maximal_unfocus Vernacentries.command_focus p in
          p,status) pstate in
      if not status then Feedback.feedback Feedback.AddedAxiom;
      pstate
    with
    | e when CErrors.noncritical e || e = CErrors.Timeout ->
      (match Hashtbl.find_opt int64_to_knn id with
       | Some (v, None, sideff) -> Hashtbl.replace int64_to_knn id (v, Some e, sideff)
       | _ -> assert false (* Should not happen *));
      raise e

let tactician_ignore t =
  let open Proofview in
  let open Notations in
  get_record () >>= fun b ->
  set_record false <*> t <*> set_record b

let subst_one dep_proof_ok x (hyp,rhs,dir) =
  let open Termops in
  let module NamedDecl = Context.Named.Declaration in
  let open Logic in
  let open Names in
  let open Tacticals.New in
  let open Locus in
  let open Tactics in
  let open Equality in
  let open EConstr in
  Proofview.Goal.enter begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Tacmach.New.project gl in
  let hyps = Proofview.Goal.hyps gl in
  let concl = Proofview.Goal.concl gl in
  (* The set of hypotheses using x *)
  let dephyps =
    List.rev (pi3 (List.fold_right (fun dcl (dest,deps,allhyps) ->
      let id = NamedDecl.get_id dcl in
      if not (Id.equal id hyp)
         && List.exists (fun y -> occur_var_in_decl env sigma y dcl) deps
      then
        (* let id_dest = if !regular_subst_tactic then dest else MoveLast in *)
        let id_dest = dest in
        (dest,id::deps,(id_dest,id)::allhyps)
      else
        (MoveBefore id,deps,allhyps))
      hyps
      (MoveBefore x,[x],[]))) in (* In practice, no dep hyps before x, so MoveBefore x is good enough *)
  (* Decides if x appears in conclusion *)
  let depconcl = occur_var env sigma x concl in
  let need_rewrite = not (List.is_empty dephyps) || depconcl in
  tclTHENLIST
    ((if need_rewrite then
      [revert (List.map snd dephyps);
       general_rewrite dir AtLeastOneOccurrence true dep_proof_ok (mkVar hyp);
       (tclMAP (fun (dest,id) -> intro_move (Some id) dest) dephyps)]
      else
       [Proofview.tclUNIT ()]) @
     [tclTRY (clear [x; hyp])])
  end

let subst_from hyps dir =
  let open Proofview in
  let subst_one_from gl hyp =
    let c = Tacmach.New.pf_get_hyp_typ hyp gl in
    let sigma = Goal.sigma gl in
    try
      let _, _, (_, lhs, rhs) = Hipattern.find_eq_data_decompose gl c in
      match dir with
      | true when EConstr.isVar sigma lhs -> subst_one true (EConstr.destVar sigma lhs) (hyp, rhs, dir)
      | false when EConstr.isVar sigma rhs -> subst_one true (EConstr.destVar sigma rhs) (hyp, lhs, dir)
      | _ -> Tacticals.New.tclZEROMSG Pp.(str "Hypothesis could not be substituted.")
    with Constr_matching.PatternMatchingFailure ->
      Tacticals.New.tclZEROMSG Pp.(str "Hypothesis could not be substituted.") in
  Proofview.Goal.enter @@ fun gl ->
  Tacticals.New.tclMAP (subst_one_from gl) hyps
