open Ltac_plugin

open Util
open Tacexpr
open Tacenv
open Loadpath
open Geninterp
open Tactic_learner_internal
open TS
open Tactic_annotate
open Cook_tacexpr

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let open_permanently file =
  open_out_gen [Open_creat; Open_text; Open_trunc; Open_wronly] 0o640 file

let select_v_file ~warn loadpath base =
  let find ext =
    let loadpath = List.map fst loadpath in
    try
      let name = Names.Id.to_string base ^ ext in
      let lpath, file =
        System.where_in_path ~warn loadpath name in
      Some (lpath, file)
    with Not_found -> None in
  match find ".v" with
  | None ->
    Error LibNotFound
  | Some res ->
    Ok res

let load_path_to_physical t =
  let printed = pp t in
  let path = match Pp.repr printed with
  | Pp.Ppcmd_box (_, k) -> (match Pp.repr k with
    | Pp.Ppcmd_glue ks -> (match Pp.repr (List.nth ks 2) with
      | Pp.Ppcmd_string s -> s
      | _ -> assert false)
    | _ -> assert false)
  | _ -> assert false in
  path

let filter_path f =
  let rec aux = function
  | [] -> []
  | p :: l ->
    if f (logical p) then (load_path_to_physical p, logical p) :: aux l
    else aux l
  in
  aux (get_load_paths ())

let locate_absolute_library dir : CUnix.physical_path locate_result =
  (* Search in loadpath *)
  let pref, base = Libnames.split_dirpath dir in
  let loadpath = filter_path (fun dir -> Names.DirPath.equal dir pref) in
  match loadpath with
  | [] -> Error LibUnmappedDir
  | _ ->
    match select_v_file ~warn:false loadpath base with
    | Ok (_, file) -> Ok file
    | Error fail -> Error fail

let try_locate_absolute_library dir =
  match locate_absolute_library dir with
  | Ok res -> Some res
  | Error LibUnmappedDir ->
    None
  | Error LibNotFound ->
    None

let benchmarking = ref None
let featureprinting = ref false

let base_filename =
  let dirpath = Global.current_dirpath () in
  Option.map (fun f -> Filename.remove_extension f) (try_locate_absolute_library dirpath)

let feat_file =
  let file = ref None in
  (fun () ->
    match !file with
      | None -> let filename = Option.default "" base_filename ^ ".feat" in
        let k = open_permanently filename in
        file := Some k;
        k
      | Some f -> f)

let eval_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" base_filename ^ ".bench" in
       let k = open_permanently filename in
       file := Some k;
       k
     | Some f -> f)

let print_to_feat str =
  output_string (feat_file ()) str;
  flush (feat_file ())

let print_to_eval str =
  output_string (eval_file ()) str;
  flush (eval_file ())

let benchoptions = Goptions.{optdepr = false;
                             optname = "Tactician benchmark time";
                             optkey = ["Tactician"; "Benchmark"];
                             optread = (fun () -> !benchmarking);
                             optwrite = (fun b -> benchmarking := b;
                                          match b with
                                          | Some _ -> (match base_filename with
                                              | None -> Feedback.msg_notice (
                                                  Pp.str "No source file could be found. Disabling benchmarking.");
                                                benchmarking := None
                                              | Some f -> ignore (eval_file ()))
                                          | _ -> ())}
let featureoptions = Goptions.{optdepr = false;
                               optname = "Tactician feature outputting";
                               optkey = ["Tactician"; "Output"; "Features"];
                               optread = (fun () -> !featureprinting);
                               optwrite = (fun b -> featureprinting := b; if b then
                                              (match base_filename with
                                              | None -> Feedback.msg_notice (
                                                  Pp.str "No source file could be found. Disabling feature writing.");
                                                benchmarking := None
                                              | Some f -> ignore (feat_file ())))}

let _ = Goptions.declare_int_option benchoptions
let _ = Goptions.declare_bool_option featureoptions

let _ = Random.self_init ()

type data_in = outcome list * tactic

(* TODO: In interactive mode this is a memory leak, but it seems difficult to properly clean this table *)
(* It might be possible to completely empty the db when a new lemma starts. *)
type semilocaldb = data_in list
let int64_to_knn : (Int64.t, semilocaldb * exn option) Hashtbl.t = Hashtbl.create 10

let subst_outcomes (s, (outcomes, tac)) =
  let subst_tac (tac, h) = Tacsubst.subst_tactic s tac, h in (* TODO: Recalculate (or remove) hash *)
  let subst_pf (hyps, g) = Mod_subst.(List.map (
      fun (id, te, ty) -> (id, Option.map (subst_mps s) te, subst_mps s ty)) hyps, subst_mps s g) in
  let rec subst_pd = function
    | End -> End
    | Step ps -> Step (subst_ps ps)
  and subst_ps {executions; tactic} =
    { executions = List.map (fun (ps, pd) -> subst_pf ps, subst_pd pd) executions
    ; tactic = subst_tac tactic } in 
  let outcomes = List.map (fun {parents; siblings; before; after} ->
      { parents = List.map (fun (psa, pse) -> (subst_pf psa, subst_ps pse)) parents
      ; siblings = subst_pd siblings
      ; before = subst_pf before
      ; after = List.map subst_pf after }) outcomes in
  (outcomes, subst_tac tac)

let tmp_ltac_defs = Summary.ref ~name:"TACTICIANTMPSECTION" []
let in_section_ltac_defs : (Names.KerName.t * glob_tactic_expr) list -> Libobject.obj =
  Libobject.(declare_object (local_object "LTACRECORDSECTIONLTACS"
                               ~cache:(fun (obj, p) -> tmp_ltac_defs := p::!tmp_ltac_defs)
                               ~discharge:(fun (obj, p) -> Some p)))

let with_let_prefix tac =
  let names = List.fold_right Names.KNset.add
      (List.concat (List.map (List.map fst) !tmp_ltac_defs)) Names.KNset.empty in
  let tac, all, ids = rebuild names tac in
  let kername_tolname id = CAst.make (Names.(Name.mk_name (Label.to_id (KerName.label id)))) in
  let ltac_to_let ltacset int =
    TacLetIn (true,
              List.map (fun (id, tac) -> (kername_tolname id, Tacexp tac)) ltacset,
              int) in
  let rec prefix acc = function
    | [] -> acc
    | ltacset::rem ->
      let set_occurs = all || List.fold_right (fun (id, _) b ->
          b || Names.KNset.mem id ids) ltacset false in
      if set_occurs then
        prefix (ltac_to_let ltacset acc) rem else
        prefix acc rem in
  prefix tac !tmp_ltac_defs

let rebuild_outcomes (outcomes, tac) =
  let rebuild_tac (tac, h) = with_let_prefix tac, h in
  let rec rebuild_pd = function
    | End -> End
    | Step ps -> Step (rebuild_ps ps)
  and rebuild_ps {executions; tactic} =
    { executions = List.map (fun (ps, pd) -> ps, rebuild_pd pd) executions
    ; tactic = rebuild_tac tactic } in 
  let outcomes = List.map (fun {parents; siblings; before; after} ->
      { parents = List.map (fun (psa, pse) -> (psa, rebuild_ps pse)) parents
      ; siblings = rebuild_pd siblings
      ; before; after }) outcomes in
  (outcomes, rebuild_tac tac)

let discharge_outcomes env (outcomes, tac) =
  if !tmp_ltac_defs = [] then (outcomes, tac) else
    let genarg_print_tac (tac, h) = discharge env tac, h in
    let rec genarg_print_pd = function
      | End -> End
      | Step ps -> Step (genarg_print_ps ps)
    and genarg_print_ps {executions; tactic} =
      { executions = List.map (fun (ps, pd) -> ps, genarg_print_pd pd) executions
      ; tactic = genarg_print_tac tactic } in 
    let outcomes = List.map (fun {parents; siblings; before; after} ->
        { parents = List.map (fun (psa, pse) -> (psa, genarg_print_ps pse)) parents
        ; siblings = genarg_print_pd siblings
        ; before; after }) outcomes in
    (outcomes, genarg_print_tac tac)

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

let section_notation_helper prods e =
  tmp_ltac_defs := []; (* Safe to discard tmp state from old section discharge *)
  if Global.sections_are_opened () then
    let id = find_last_key prods in
    let alias = Tacenv.interp_alias id in
    let func = TacFun (List.map Names.Name.mk_name alias.alias_args, alias.alias_body) in
    Lib.add_anonymous_leaf (in_section_ltac_defs [id, func])

let in_db : data_in -> Libobject.obj =
  Libobject.(declare_object { (default_object "LTACRECORD") with
                              cache_function = (fun (_,((outcomes, tac) : data_in)) ->
                                  learner_learn outcomes tac)
                            ; load_function = (fun i (_, (outcomes, tac)) ->
                                  learner_learn outcomes tac)
                            ; open_function = (fun i (_, (execs, tac)) -> ())
                            ; classify_function = (fun data -> Libobject.Substitute data)
                            ; subst_function = subst_outcomes
                            ; discharge_function = (fun (obj, data) ->
                                let env = Global.env () in
                                Some (discharge_outcomes env data))
                            ; rebuild_function = (fun data ->
                                rebuild_outcomes data)
                            })

let add_to_db (x : data_in) =
  Lib.add_anonymous_leaf (in_db x)

let add_to_db2 id ((outcomes, tac) : (tactic list * Proofview.Goal.t * Proofview.Goal.t list) list *
                               tactic) =
  let outcomes = List.map (fun (mem, st, sts) ->
      let st : proof_state = goal_to_proof_state st in
      { parents = List.map (fun tac -> (st (* TODO: Fix *), { executions = []; tactic = tac})) mem
      ; siblings = End
      ; before = st
      ; after = [] (* List.map goal_to_proof_state sts *) }) outcomes in
  add_to_db (outcomes, tac);
  let semidb, exn = Hashtbl.find int64_to_knn id in
  Hashtbl.replace int64_to_knn id ((outcomes, tac)::semidb, exn);
  if !featureprinting then (
    (* let h s = string_of_int (Hashtbl.hash s) in
     * (\* let l2s fs = "[" ^ (String.concat ", " (List.map (fun x -> string_of_int x) fs)) ^ "]" in *\)
     * let p2s x = proof_state_to_json x in *)
    let entry (outcomes, tac) =
      "Not implemented curretnly" in
      (* "{\"before\": [" ^ String.concat ", " (List.map p2s before) ^ "]\n" ^
       * ", \"tacid\": " ^ (\*Base64.encode_string*\) h tac ^  "\n" ^
       * ", \"after\": [" ^ String.concat ", " (List.map p2s after) ^ "]}\n" in *)
    print_to_feat (entry (outcomes, tac)))

(* Types and accessors for state in the proof monad *)
type localdb = ((glob_tactic_expr list * Proofview.Goal.t * Proofview.Goal.t list) list * glob_tactic_expr) list
type goal_stack = (glob_tactic_expr list * int * Proofview.Goal.t) list list
type tactic_trace = glob_tactic_expr list
type state_id_stack = int list

let global_record = Summary.ref ~name:"TACTICIAN-RECORD" true
let record_field : bool Evd.Store.field = Evd.Store.field ()
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

let warn () = Feedback.msg_warning (Pp.str ("Tactician has uncovered a bug. Please report. "))

let set_record b =
  modify_field record_field (fun _ -> b, ()) (fun i -> true)

let get_record () =
  modify_field record_field (fun b -> b, b) (fun i -> true)

let push_localdb x =
  modify_field localdb_field (fun db -> x::db, ()) (fun () -> [])

let empty_localdb () =
  modify_field localdb_field (fun db -> [], db) (fun () -> [])

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
  modify_field_goals state_id_stack_field (fun i st -> i::st, ()) (fun i -> []) >>=
  fun _ -> tclUNIT ()

let pop_state_id_stack () =
  let open Proofview in
  let open Notations in
  (* Sometimes, a new goal does not inherit its id from its parent, and thus the id stack
     is too short. This happens for example when using `unshelve`. In that case, we assign 0 *)
  modify_field_goals state_id_stack_field (fun i st ->
      match st with | [] -> warn (); [], 0 | x::xs -> xs, x)
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
  modify_field_goals tactic_trace_field (fun i st -> tac::st, ()) (fun i -> []) >>=
  fun _ -> tclUNIT ()

let get_tactic_trace gl =
  get_field_goal2 tactic_trace_field gl (fun _ -> [])

let features term = List.map Hashtbl.hash (Features.extract_features (Hh_term.hhterm_of (Hh_term.econstr_to_constr term)))

let goal_to_features gl =
       let goal = Proofview.Goal.concl gl in
       let hyps = Proofview.Goal.hyps gl in
       let hyps_features =
          List.map
            (fun pt -> match pt with
                 | Context.Named.Declaration.LocalAssum (id, typ) ->
                   features typ
                 | Context.Named.Declaration.LocalDef (id, term, typ) ->
                   List.append (features term) (features typ))
            hyps in
       let feats = (List.append (features goal) (List.concat hyps_features)) in
       (*let feats = List.map Hashtbl.hash feats in*)
       List.sort(*_uniq*) Int.compare feats

let record_map (f : Proofview.Goal.t -> 'a)
    (gls : Proofview.Goal.t Proofview.tactic list) : 'a list Proofview.tactic =
  let rec aux gls acc =
    let open Proofview.Notations in
    match gls with
    | [] -> Proofview.tclUNIT (acc)
    | gl::gls' -> gl >>= fun gl' -> aux gls' (f gl' :: acc) in
  aux gls []

(* let () = Vernacentries.requirehook := (fun files ->
 *   let newrequires = List.map (fun (pair) -> CUnix.canonical_path_name (snd pair)) files in
 *   let newrequires = List.map (fun (file) -> (String.sub file 0 (String.length file - 2)) ^ "feat") newrequires in
 *   requires := List.append newrequires !requires
 * ) *)

let firstn n l =
  let rec aux acc n l =
    match n, l with
    | 0, _ -> List.rev acc
    | n, h::t -> aux (h::acc) (pred n) t
    | _ -> List.rev acc
  in
  aux [] n l

let get_k_str ranking comp =
    let rec get_k' acc ranking =
    match ranking with
    | (_, f, o) :: r -> if String.equal o comp then acc else get_k' (1 + acc) r
    | [] -> -1
    in get_k' 0 ranking

let mk_ml_tac tac = fun args is -> tac

let register tac name =
  let fullname = {mltac_plugin = "recording"; mltac_tactic = name} in
  register_ml_tactic fullname [| tac |]

let run_ml_tac name = TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = name}; mltac_index = 0}, []))

let print_rank env rank =
  let tac_pp env t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
  let strs = List.map (fun (x, t) -> (Printf.sprintf "%.4f " x) ^ (Pp.string_of_ppcmds (tac_pp env t))) rank in
  Pp.str (String.concat "\n" strs)

(* Running predicted tactics *)

exception PredictionsEnd

let parse_tac tac =
    try
      Tacinterp.eval_tactic tac
    with
    e -> print_endline (Printexc.to_string e); flush_all (); assert false

let rec tclFairJoin (tacs : 'a Proofview.tactic Proofview.tactic) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1, resttacs) ->
      tclCASE tac1 >>= function
      | Fail e -> (tclFairJoin (resttacs e))
      | Next (a, tac1') ->
        tclOR (tclUNIT a)
              (fun e -> (tclFairJoin (tclOR (resttacs e)
                                            (fun e -> tclUNIT (tac1' e)))))

let tclInterleave tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclFairJoin ((tclUNIT tac1) <+> (tclUNIT tac2))

let tclInterleaveList (tacs : 'a Proofview.tactic list) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFairJoin
      (List.fold_right (fun tac acc -> (tclUNIT tac) <+> acc) tacs (tclZERO PredictionsEnd))

let rec tclInterleaveCaseTacsSpecial start (tacs : bool Proofview.case Proofview.tactic) =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1case, resttacs) ->
      match tac1case with
      | Fail e -> (tclInterleaveCaseTacsSpecial start (resttacs e))
      | Next (b, tac1') ->
        if (start && b) then Tacticals.New.tclZEROMSG (Pp.str "Ran out of tactics") else
        tclOR (if b then tclUNIT () else Tacticals.New.tclCOMPLETE (tclUNIT ()))
              (fun e -> (tclInterleaveCaseTacsSpecial b (tclOR (resttacs e)
                                                               (fun e -> (tclCASE (tac1' e))))))

let rec tclInfiniteTrue () =
    let open Proofview in
    tclOR (tclUNIT true) (fun _ -> tclInfiniteTrue ())

let tclInterleaveListSpecial (tacs : unit Proofview.tactic list) : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let tacs = List.map (fun t -> t <*> tclUNIT false) tacs in
    tclInterleaveCaseTacsSpecial true
      (List.fold_right (fun tac acc -> (tclCASE tac) <+> acc) tacs (tclCASE (tclInfiniteTrue ())))

let tclInterleaveSpecial tac1 tac2 =
    tclInterleaveListSpecial [tac1; tac2]

let rec tclInterleaveWrong tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclCASE tac1 >>= function
    | Fail iexn -> tac2
    | Next ((), tac1') -> tclOR (tclUNIT ()) (fun e -> (tclInterleaveWrong tac2 (tac1' e)))

let predict (gls : Proofview.Goal.t list) =
  let states = List.map (fun gl ->
      let ps = goal_to_proof_state gl in
      { parents = List.map (fun tac -> (ps (* TODO: Fix *), { executions = []; tactic = tac }))
            ([] (*TODO: Fix*) (* get_tactic_trace gl *))
      ; siblings = End
      ; state = ps}) gls in
  learner_predict states

let print_goal_short = Proofview.Goal.enter
    (fun gl ->
       let env = Proofview.Goal.env gl in
       let sigma = Proofview.Goal.sigma gl in
       let goal = Proofview.Goal.concl gl in
       (Proofview.tclLIFT (Proofview.NonLogical.print_info (Printer.pr_econstr_env env sigma (goal)))))

type blaat = | Intermediate | Complete | No_goal

(* TODO: This does not use the focus, and is generally entirely wrong. Probably delete or rewrite *)
let rec tclFold tac : blaat Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFOCUS ~nosuchgoal:(tclUNIT No_goal) 1 1 tac >>=
    (function
     | No_goal -> tclUNIT Complete
     | Complete -> tclFold tac
     | Intermediate -> tclUNIT Intermediate)

let rec tclSearchBFS () mark : blaat Proofview.tactic =
  let open Proofview in
  let open Notations in
  tclENV >>= fun env -> Goal.goals >>= record_map (fun x -> x) >>= function
  | [] -> tclUNIT No_goal
  | gls -> let predictions = predict gls in
    (tclSearchGoalBFS predictions mark)
and tclSearchGoalBFS ps mark =
    let open Proofview in
    let open Notations in
      tclUNIT Intermediate <+> tclInterleaveList
        (List.mapi (fun i {focus; tactic=(tac, _)} ->
          let tac2 = parse_tac tac in
          tclFold (
           (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
           (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int i)))) <*>
           (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pp.str "")))) <*>
           print_goal_short <*>
           tclPROGRESS tac2 <*>
           (*print_goal_short <*>*)
           tclSearchBFS () (mark ^ "." ^ string_of_int i))
       ) (Stream.npeek 100 ps))

exception DepthEnd

let synthesize_tactic (env : Environ.env) tcs =
  let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
  Pp.(h 0 (str "search" ++ ws 1 ++ str "failing" ++ ws 1 ++
          Pp.str "(" ++ (prlist_with_sep
                           (fun () -> str "; ")
                           (fun (t, i) -> str "only" ++ ws 1 ++ int (1+i) ++ str ":" ++ ws 1 ++ tac_pp t)
                           (Stdlib.List.rev tcs)) ++ str (").")))

type witness_elem =
  { tac : glob_tactic_expr
  ; focus : int
  ; prediction_index : int }
let search_witness_field : witness_elem list Evd.Store.field = Evd.Store.field ()
let push_witness w =
  modify_field search_witness_field (fun s -> w::s, ()) (fun () -> [])
let get_witness () =
  modify_field search_witness_field (fun n -> n, n) (fun () -> [])
let empty_witness () =
  modify_field search_witness_field (fun n -> [], ()) (fun () -> [])

let tclDebugTac t env debug =
    let open Proofview in
    let open Notations in
    let tac2 = parse_tac t in
    (* let tac2 = tclUNIT () >>= fun () ->
     *     try
     *         tac2 >>= (fun () -> CErrors.user_err (Pp.str "blaat"))
     *     with e -> print_endline (Printexc.to_string e); print_endline "hahahah dom"; assert false; Tacticals.New.tclZEROMSG (Pp.str "Tactic error")
     * in *)
    if debug then
    (
      get_witness () >>= fun wit ->
      let tcs, mark = List.split (List.map (fun {tac;focus;prediction_index} ->
          ((tac, focus), prediction_index)) wit) in
      let mark = String.concat "." (List.map string_of_int mark) in
      (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
      (tclLIFT (NonLogical.print_info (Pp.str mark))) <*>
      (tclLIFT (NonLogical.print_info (synthesize_tactic env tcs))) <*>
      (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_glob_tactic env t)))) <*>
      print_goal_short <*>
      tclPROGRESS tac2)
    else tclPROGRESS tac2

let rec tclFold2 (d : 'a) (tac : 'a -> 'a Proofview.tactic) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    (tclFOCUS ~nosuchgoal:(tclUNIT None) 1 1 (tac d >>= (fun x -> tclUNIT (Some x)))) >>=
    function
    | None -> tclUNIT d
    | Some x -> tclFold2 x tac

let tclFoldPredictions tacs =
  let rec aux depth =
    let open Proofview in
    match Stream.peek tacs with
    | None -> tclZERO (if depth then DepthEnd else PredictionsEnd)
    | Some tac -> Stream.junk tacs;
      tclOR tac
        (fun e ->
           let depth = depth || (match e with
               | (DepthEnd, _) -> true
               | _ -> false) in
           aux depth) in
  aux false

let stream_mapi f stream =
  let next i =
    try Some (f i (Stream.next stream))
    with Stream.Failure -> None in
  Stream.from next

let tclSearchDiagonalDFS depth =
    let open Proofview in
    let open Notations in
    let count = ref 0 in (* TODO: This does not thread through the DiagonalIterative function *)
    let rec aux (depth : int)
      : int Proofview.tactic =
    tclENV >>= fun env -> Goal.goals >>= record_map (fun x -> x) >>= function
    | [] -> tclUNIT depth
    | gls ->
      (* TODO: Remove rev *)
      let predictions = predict [List.hd (List.rev gls)] in
      (tclFoldPredictions
        (stream_mapi
           (fun i {focus; tactic=(t, _)} ->
              let ndepth = depth - i in
              if ndepth <= 0 then tclZERO DepthEnd else
                (count := !count + 1;
                 tclFOCUS ~nosuchgoal:(Tacticals.New.tclZEROMSG (Pp.str "Predictor gave wrong focus"))
                   (focus+1) (focus+1)
                   (push_witness { tac = t; focus = focus; prediction_index = i } <*>
                    tclDebugTac t env false <*>
                    (aux ((ndepth - 1))))))
           predictions)) >>= aux in
    aux depth >>= fun _ -> tclUNIT !count

let rec tclSearchDiagonalIterative d : int Proofview.tactic =
    let open Proofview in
    (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
    tclOR
      (tclSearchDiagonalDFS d)
      (function
        | (PredictionsEnd, _) -> Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
        | _ -> tclSearchDiagonalIterative (d + 1))


(* TODO: Doesn't compile anymore and is probably wrong
let rec tclSearch () mark curr : blaat Proofview.tactic =
    let open Proofview in
    tclFold (Goal.enter_one (fun gl ->
        let predictions = List.map fst (predict gl) in
        (tclSearchGoal predictions mark curr)))
and tclSearchGoal ps mark curr =
    let open Proofview in
    let open Notations in
    match ps with
    | [] -> Tacticals.New.tclZEROMSG (Pp.str "No more predicted tactics")
    | tac::ps' ->
      let tac2 = parse_tac tac in
      tclUNIT Intermediate <+> tclInterleave
        (tclSearchGoal ps' mark (curr + 1))
        (
         (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
         (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int curr)))) <*>
         (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic Environ.empty_env Evd.empty tac)))) <*>
         print_goal_short <*>
         tclPROGRESS tac2 <*>
         print_goal_short <*>
         tclSearch () (mark ^ "." ^ string_of_int curr) 0)
*)

  let tclTIMEOUT2 n t =
    Proofview.tclOR
      (Timeouttac.ptimeout n t)
      begin function (e, info) -> match e with
        | Logic_monad.Tac_Timeout -> Tacticals.New.tclZEROMSG (Pp.str "timout")
        | e -> Tacticals.New.tclZEROMSG (Pp.str "haha")
      end

let contains s1 s2 =
    let re = Str.regexp_string s2
    in
        try ignore (Str.search_forward re s1 0); true
        with Not_found -> false

let rec tclInfiniteUnit () =
    let open Proofview in
    tclOR (tclUNIT ()) (fun _ -> tclInfiniteUnit ())

let search_recursion_depth_field : int Evd.Store.field = Evd.Store.field ()
let max_recursion_depth = 2
let inc_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> 1+n, n) (fun () -> 0)
let dec_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> (if n <= 0 then 0 else n - 1), ()) (fun () -> 0)
let get_search_recursion_depth () =
  modify_field search_recursion_depth_field (fun n -> n, n) (fun () -> 0)

let commonSearch () =
    let open Proofview in
    let open Notations in
    (* We want to allow at least one nested search, such that users can embed search in more complicated
       expressions. But allowing infinite nesting will just lead to divergence. *)
    inc_search_recursion_depth () >>= fun n ->
    if n >= max_recursion_depth then Tacticals.New.tclZEROMSG (Pp.str "too much search nesting") else
      tclLIFT (NonLogical.make (fun () -> CWarnings.get_flags ())) >>= (fun oldFlags ->
          (* TODO: Find a way to reset dumbglob to original value. This is a temporary hack. *)
          let doFlags = n = 0 in
          let setFlags () = if not doFlags then tclUNIT () else tclLIFT (NonLogical.make (fun () ->
              Dumpglob.continue (); CWarnings.set_flags (oldFlags))) in
          (if not doFlags then tclUNIT () else
            tclLIFT (NonLogical.make (fun () -> Dumpglob.pause(); CWarnings.set_flags ("-all"))))
          <*> tclOR
            (tclONCE (Tacticals.New.tclCOMPLETE (tclSearchDiagonalIterative 1)) >>= fun c ->
             get_witness () >>= fun wit -> empty_witness () <*>
             dec_search_recursion_depth () >>= fun () -> setFlags () <*> tclUNIT (wit, c))
            (fun (e, i) -> setFlags () <*> tclZERO ~info:i e))

let benchmarked_field : bool Evd.Store.field = Evd.Store.field ()
let get_benchmarked () =
  modify_field benchmarked_field (fun b -> b, b) (fun () -> false)
let set_benchmarked () =
  modify_field benchmarked_field (fun _ -> true, ()) (fun () -> true)

let benchmarkSearch name : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let modpath = Global.current_modpath () in
    let time = match !benchmarking with
      | None -> assert false
      | Some t -> t in
    let full_name = Names.ModPath.to_string modpath ^ "." ^ Names.Id.to_string name in
    let print_success env (wit, count) start_time =
      let tcs, m = List.split (List.map (fun {tac;focus;prediction_index} ->
          ((tac, focus), prediction_index)) wit) in
      let m = String.concat "." (List.map string_of_int m) in
      let tdiff = string_of_float (Unix.gettimeofday () -. start_time) in
      let open NonLogical in
      let tstring = Pp.string_of_ppcmds (synthesize_tactic env tcs) in
      (make (fun () -> print_to_eval ("\t" ^ m ^ "\t" ^ tstring ^ "\t" ^ tdiff ^ "\t" ^ string_of_int count))) >>
      (print_info (Pp.str ("Proof found for " ^ full_name ^ "!"))) in
    let print_name = NonLogical.make (fun () ->
        print_to_eval ("\n" ^ (full_name) ^ "\t" ^ string_of_int time)) in
    get_benchmarked () >>= fun benchmarked ->
    if benchmarked then tclUNIT () else
      set_benchmarked () <*>
      let start_time = Unix.gettimeofday () in
      tclTIMEOUT2 time (tclENV >>= fun env ->
                        tclLIFT (NonLogical.print_info (Pp.str ("Start proof search for " ^ full_name))) <*>
                        tclLIFT print_name <*>
                        commonSearch () >>=
                        fun m -> tclLIFT (print_success env m start_time))

let userPredict =
    let open Proofview in
    let open Notations in
    tclENV >>= fun env -> Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
    let states = List.map (fun gl ->
        let ps = goal_to_proof_state gl in
        { parents = List.map (fun tac -> (ps (* TODO: Fix *), { executions = []; tactic = tac }))
              ([] (*TODO: Fix*)(* get_tactic_trace gl *))
        ; siblings = End
        ; state = ps}) gls in
    let r = learner_predict states in
    let r = List.map (fun {confidence; focus; tactic} -> (confidence, focus, tactic)) (Stream.npeek 10 r) in
    let r = List.map (fun (x, _, (y, _)) -> (x, y)) r in
    (* Print predictions *)
    (Proofview.tclLIFT (Proofview.NonLogical.print_info (print_rank env r)))

let nested_search_solutions_field : tactic list list Evd.Store.field = Evd.Store.field ()
let push_nested_search_solutions tcs =
  modify_field nested_search_solutions_field (fun acc -> tcs :: acc, ()) (fun () -> [])
let empty_nested_search_solutions () =
  modify_field nested_search_solutions_field (fun acc -> [], acc) (fun () -> [])
let userSearch =
    let open Proofview in
    let open Notations in
    tclUNIT () >>= fun () -> commonSearch () >>= fun (wit, count) -> get_search_recursion_depth () >>= fun n ->
    let tcs, _ = List.split (List.map (fun {tac;focus;prediction_index} ->
        ((tac, focus), prediction_index)) wit) in
    if n >= 1 then push_nested_search_solutions tcs else
      empty_nested_search_solutions () >>= fun acc -> tclENV >>= fun env ->
      let main_msg = Pp.(str "Tactician found a proof! The following tactic caches the proof:\n\n" ++
                         synthesize_tactic env tcs) in
      let acc_msg = if List.is_empty acc then Pp.mt () else
          Pp.(str ("\n\nThe tactic above uses nested searching. The following tactics cache those nested searches.\n") ++
              (prlist_with_sep fnl (synthesize_tactic env) acc)) in
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

(* Returns true if tactic execution should be skipped *)
let pre_vernac_solve pstate id =
  (* If this needs to work again, put the current name in the evdmap storage *)
  (* if not (Names.Id.equal !current_name new_name) then (
   *   if !featureprinting then print_to_feat ("#lemma " ^ (Names.Id.to_string new_name) ^ "\n");
   * ); *)
  (* print_endline ("db_test: " ^ string_of_int (Predictor.count !db_test));
   * print_endline ("id: " ^ (Int64.to_string id)); *)
  match Hashtbl.find_opt int64_to_knn id with
  | Some (db, exn) -> (List.iter add_to_db db; Hashtbl.remove int64_to_knn id;
      match exn with
      | None -> true
      | Some exn -> raise exn)
  | None -> Hashtbl.add int64_to_knn id ([], None); false

let save_exn id exn =
  match Hashtbl.find_opt int64_to_knn id with
  | Some (v, None) -> Hashtbl.replace int64_to_knn id (v, Some exn)
  | _ -> assert false (* Should not happen *)

(* Tactic recording tactic *)

let val_tag wit = val_tag (Genarg.topwit wit)
let register_interp0 wit f =
  let open Ftactic.Notations in
  let interp ist v =
    f ist v >>= fun v -> Ftactic.return (Val.inject (val_tag wit) v)
  in
  Geninterp.register_interp0 wit interp

let wit_glbtactic : (Empty.t, glob_tactic_expr, glob_tactic_expr) Genarg.genarg_type =
  let wit = Genarg.create_arg "glbtactic" in
  let () = register_val0 wit None in
  register_interp0 wit (fun ist v -> Ftactic.return v);
  wit

let should_record b =
  b && !global_record

let push_state_tac () =
  let open Proofview in
  let open Notations in
  get_record () >>= fun b -> if not (should_record b) then tclUNIT () else
    push_state_id_stack () <*> Goal.goals >>= record_map (fun x -> x) >>= fun gls ->
    push_goal_stack (List.map (fun gl -> get_tactic_trace gl, get_state_id_goal_top gl, gl) gls)

let record_tac (tac2 : glob_tactic_expr) : unit Proofview.tactic =
  let open Proofview in
  let open Notations in
  let collect_states before_gls after_gls =
    List.map (fun (tr, i, gl_before) -> (tr, gl_before, List.filter_map (fun (j, gl_after) ->
        if i = j then Some gl_after else None) after_gls)) before_gls in
  get_record () >>= fun b -> if not (should_record b) then tclUNIT () else
    tclENV >>= fun env ->
    let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
    let tac = Pp.string_of_ppcmds(tac_pp tac2) in
    pop_goal_stack () >>= fun before_gls ->
    Goal.goals >>= record_map (fun x -> x) >>= (fun after_gls ->
        let after_gls = List.map (fun gl -> get_state_id_goal_top gl, gl) after_gls in
        (* TODO: There is probably a much better way to do this *)
        if (String.equal tac "admit" || String.equal tac "search" || String.is_prefix "search failing" tac
            || String.is_prefix "tactician ignore" tac)
        then Proofview.tclUNIT () else
          push_localdb (collect_states before_gls after_gls, tac2)
      ) >>= (fun () -> pop_state_id_stack () <*> (* TODO: This is a strange way of doing things, see todo above. *)
                       push_tactic_trace tac2)

        (* Make predictions *)
        (*let r = Predictor.knn db feat in
           let r = List.map (fun (x, y, (z, q)) -> (x, y, q)) r in
           let pp_str = Pp.int (get_k_str r tac) ++ (*(Pp.str " ") ++ (Pptactic.pr_raw_tactic tac) ++*) (Pp.str "\n") in
           append "count.txt" (Pp.string_of_ppcmds pp_str);*)

let ml_record_tac args is =
  (*let num = Tacinterp.Value.cast (Genarg.topwit Tacarg.wit_tactic) (List.hd args) in*)
  let tac = Tacinterp.Value.cast (Genarg.topwit wit_glbtactic) (List.hd args) in
  record_tac tac

let ml_push_state_tac args is =
  push_state_tac ()

let () = register ml_record_tac "recordtac"
let () = register ml_push_state_tac "pushstatetac"

let run_record_tac (tac : glob_tactic_expr) : glob_tactic_expr =
  let enc = Genarg.in_gen (Genarg.glbwit wit_glbtactic) tac in
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "recordtac"}; mltac_index = 0},
                    [TacGeneric enc]))

let run_pushs_state_tac (): glob_tactic_expr =
  (*let tac_glob = Tacintern.intern_pure_tactic*)
  TacML (CAst.make ({mltac_name = {mltac_plugin = "recording"; mltac_tactic = "pushstatetac"}; mltac_index = 0},
                []))

let record_tac_complete orig tac : glob_tactic_expr =
  TacThen (run_pushs_state_tac (), TacThen (tac, run_record_tac orig))

let recorder (tac : glob_tactic_expr) id name : unit Proofview.tactic = (* TODO: Implement self-learning *)
  let open Proofview in
  let open Notations in
  let save_db env (db : localdb) =
    let tac_pp t = Sexpr.format_oneline (Pptactic.pr_glob_tactic env t) in
    let string_tac t = Pp.string_of_ppcmds (tac_pp t) in
    let with_hash t = t, Hashtbl.hash (string_tac t) in
    let tryadd (execs, tac) =
      let s = string_tac tac in
      let tac' = tac, Hashtbl.hash s in
      let execs = List.map (fun (m, b, a) -> (List.map with_hash m, b, a)) execs in
      add_to_db2 id (execs, tac');
      try (* This is purely for parsing bug detection and could be removed for performance reasons *)
        let _ = Pcoq.parse_string Pltac.tactic_eoi s in ()
      with e ->
        Feedback.msg_warning (Pp.str (
            "Tactician detected a printing/parsing problem " ^
            "for the following tactic. Please report. " ^ s)) in
    List.iter (fun trp -> tryadd trp) db; tclUNIT () in
  let rtac = decompose_annotate tac record_tac_complete in
  let ptac = Tacinterp.eval_tactic rtac in
  let ptac = ptac <*> tclENV >>= fun env -> empty_localdb () >>= save_db env in
  match !benchmarking with
  | None -> ptac
  | Some _ -> benchmarkSearch name <*> ptac

let hide_interp_t global t ot id name =
  let open Proofview in
  let open Notations in
  let hide_interp env =
    let ist = Genintern.empty_glob_sign env in
    let te = Tacintern.intern_pure_tactic ist t in
    let t = recorder te id name in
    match ot with
    | None -> t
    | Some t' -> Tacticals.New.tclTHEN t t'
  in
  if global then
    Proofview.tclENV >>= fun env ->
    hide_interp env
  else
    Proofview.Goal.enter begin fun gl ->
      hide_interp (Proofview.Goal.env gl)
    end

let tactician_ignore t =
  let open Proofview in
  let open Notations in
  get_record () >>= fun b ->
  set_record false <*> t <*> set_record b
