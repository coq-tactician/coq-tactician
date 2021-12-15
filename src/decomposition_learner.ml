open Tactic_learner
open Tactician_util
open Ltac_plugin

let data_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" Ltacrecord.base_filename ^ ".eval" in
       let k = Ltacrecord.open_permanently filename in
       file := Some k;
       k
     | Some f -> f)

module Cata = Coq_ast_cata.Cata(IdentityMonad)

module DecompositionLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  open TS
  module Learner = Lshf_learner.ComplexLSHF

  type model = tactic list
  let last_model : tactic list ref = Summary.ref ~name:"dataset-generator-learner-lastmodel" []

  let empty () = []

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Libnames.dirpath name) then `File else `Dependency

  let learn db (name, status) outcomes tac =
    let outcomes = List.map (fun _ -> tac) outcomes in
    let db = match cache_type name with
    | `File -> outcomes @ db
    | `Dependency -> db in
    last_model := db;
    db

  let predict db situations = IStream.empty
  let evaluate db _ _ = 0., db

  (* We have to do some reversals before the evaluation *)
  let preprocess model =
    List.rev model

  let generate_step tac =
      (* let tac = tactic_repr tac in *)
      (* let tac = Cata.glob_tactic_expr_cata Cata.default_sequence_record tac in *)
      (* let strict_tac = Tactic_normalize.tactic_strict tac in *)
      (* let free = Tactic_substitute.tactic_free_variables @@ strict_tac in *)
      (* List.iter (fun outcome -> *)
      (*     let ps_hyps = proof_state_hypotheses outcome.before in *)
      (*     let bound_hyps = Context.Named.to_vars ps_hyps in *)
      (*     let free = List.filter (fun id -> not @@ Names.Id.Set.mem id bound_hyps) free in *)
      (*     if free != [] then *)
      (*       begin *)
      (*         Feedback.msg_warning (Pp.seq (List.map Names.Id.print free)); *)
      (*         Feedback.msg_warning (Pptactic.pr_glob_tactic (Global.env ()) tac) *)
      (*       end; *)
    (*     ()) outcomes *)
    let tac = tactic_repr tac in
    let tac = Tactic_normalize.tactic_normalize tac in
    let tac = Tactic_normalize.tactic_strict tac in
    let tac = Tactic_name_remove.tactic_name_remove tac in
    let tac = Extreme_tactic_normalize.tactic_normalize tac in
    let tachash = string_of_int @@ Hashtbl.hash_param 255 255 tac in
    let tacstr = Pp.string_of_ppcmds @@
      Sexpr.format_oneline @@ Pptactic.pr_glob_tactic (Global.env ()) @@ tac in
    let tacsexpr = Sexpr.sexpr_to_string @@ Tactic_sexpr.tactic_sexpr @@ tac in
    output_string (data_file ()) (tachash ^ "\t" ^ tacstr ^ "\t" ^ tacsexpr ^ "\n")

  let endline_hook () = print_endline "writing";
    let data = preprocess !last_model in
    ignore (List.iter generate_step data)

  let () = Declaremods.append_end_library_hook endline_hook

end

let () = register_online_learner "decomposition-learner" (module DecompositionLearner)
let () = Tactic_learner_internal.disable_queue ()
