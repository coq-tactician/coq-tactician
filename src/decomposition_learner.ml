open Tactic_learner
open Names
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

module DecompositionLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  open TS
  module Learner = Lshf_learner.ComplexLSHF

  type model = unit

  let last_model = Summary.ref ~name:"offline-evaluation-simulator-learner-lastmodel" []

  let empty () = ()

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Names.ModPath.dp @@ Names.Constant.modpath name) then `File else `Dependency

  let learn db status name outcomes tac =
    match cache_type name with
    | `File ->
      let strict_tac = Tactic_normalize.tactic_strict @@ tactic_repr tac in
      let free = Tactic_substitute.tactic_free_variables @@ strict_tac in
      List.iter (fun outcome ->
          let ps_hyps = proof_state_hypotheses outcome.before in
          let bound_hyps = Context.Named.to_vars ps_hyps in
          let free = List.filter (fun id -> not @@ Names.Id.Set.mem id bound_hyps) free in
          if free != [] then
            begin
              Feedback.msg_warning (Pp.seq (List.map Names.Id.print free));
              Feedback.msg_warning (Pptactic.pr_glob_tactic (Global.env ()) @@ tactic_repr tac)
            end;
          ()) outcomes
      (* Feedback.msg_info @@ Pptactic.pr_glob_tactic (Global.env ()) @@ tactic_repr tac *)
    | `Dependency -> ()

  let predict db situations = IStream.empty
  let evaluate db _ _ = 0., db

end

let () = register_online_learner "decomposition-learner" (module DecompositionLearner)
let () = Tactic_learner_internal.disable_queue ()
