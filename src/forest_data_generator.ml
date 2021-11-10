open Tactic_learner
open Serlib
open Sexplib
open Ltac_plugin
open Learner_helper
open Features

let data_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" Ltacrecord.base_filename ^ ".sexpr" in
       let k = Ltacrecord.open_permanently filename in
       file := Some k;
       k
     | Some f -> f)


module DatasetGeneratorLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  module FH = Features.F(TS)
  open TS
  open LH
  open FH
  module LSHF = Naiveknn_learner.ComplexNaiveKnn(TS)

  type ownmodel = (data_status * Names.Constant.t * (outcome list * tactic) list) list
  type model = {database : ownmodel; lshf : LSHF.model}

  module IntSet = Set.Make(struct type t = feature let compare = compare end)

  let last_model = Summary.ref ~name:"dataset-generator-learner-lastmodel" []

  let empty () = {database = []; lshf = LSHF.empty ()}

  let term_equal term1 term2 =
    Constr.equal (term_repr term1) (term_repr term2)

  let hyp_equal hyp1 hyp2 = Context.Named.Declaration.equal
    (fun hyp_1 hyp_2 -> term_equal hyp_1 hyp_2) hyp1 hyp2

  let mkfeats t = term_sexpr_to_simple_features 3 (term_sexpr t)

  let list_to_set l =
    List.fold_left (fun int_set elm -> IntSet.add elm int_set) IntSet.empty l

  let rec hyps_feats_disappear hyps hyps' feat_set =
    let get_hyp_feats hyp =
    match hyp with
    | Context.Named.Declaration.LocalAssum (_, typ) ->
      mkfeats typ
    | Context.Named.Declaration.LocalDef (_, term, typ) ->
      mkfeats typ @ mkfeats term
    in
    match hyps with
    | [] -> feat_set
    | hyp :: target_tl ->
      if List.exists (fun hyp' -> hyp_equal hyp hyp') hyps'
      then hyps_feats_disappear target_tl hyps' feat_set
      else
        let hyp_feat_set =  list_to_set (List.rev (List.rev_map Hashtbl.hash (get_hyp_feats hyp))) in
        let new_feat_set = IntSet.union feat_set hyp_feat_set in
        hyps_feats_disappear target_tl hyps' new_feat_set

  (* get features in state not in state' *)
  let state_diff state state'=
    let hyps = proof_state_hypotheses state in
    let goal = proof_state_goal state in
    let hyps' = proof_state_hypotheses state' in
    let goal' = proof_state_goal state' in
    let goal_diff =
      if term_equal goal goal' then []
      else List.rev (List.rev_map Hashtbl.hash (mkfeats goal)) in
    hyps_feats_disappear hyps hyps' (list_to_set goal_diff)

  let feat_disappear before_state after_states =
    if after_states == [] then
      proof_state_to_simple_ints before_state
    else
      let disappear_feat_set =
      List.fold_left (
        fun feat_set after_state ->
          IntSet.union feat_set (state_diff before_state after_state)
        ) IntSet.empty after_states in
      IntSet.elements disappear_feat_set

  let feat_appear before_state after_states =
    let appear_feat_set =
      List.fold_left (fun feat_set after_state ->
        (IntSet.union feat_set (state_diff after_state before_state))
      ) IntSet.empty after_states in
    IntSet.elements appear_feat_set

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Names.ModPath.dp @@ Names.Constant.modpath name) then `File else `Dependency

  let learn db status name outcomes tac =
    let lshfnew = LSHF.learn db.lshf status name outcomes tac in
    let new_database = match db.database with
      | (pstatus, pname, ls)::data when Names.Constant.equal name pname ->
        (pstatus, pname, (outcomes, tac)::ls)::data
      | _ -> (status, name, [outcomes, tac])::db.database in
    last_model := new_database; {database = new_database; lshf = lshfnew}
  let predict db situations = LSHF.predict db.lshf situations
  let evaluate db _ _ = 0., db

  let output_sexpr (ps, tac) =
    let term_to_sexpr t = Ser_constr.sexp_of_constr (term_repr t) in
    let named_context_to_sexpr = Sexplib.Std.sexp_of_list
        (Ser_context.Named.Declaration.sexp_of_pt term_to_sexpr term_to_sexpr) in
    let proof_state_to_sexpr ps =
      let hyps = proof_state_hypotheses ps in
      let goal = proof_state_goal ps in
      Sexplib.Pre_sexp.List [named_context_to_sexpr hyps; term_to_sexpr goal] in
    let line = Sexplib.Pre_sexp.List [proof_state_to_sexpr ps; Std.sexp_of_int (tactic_hash tac)] in
    output_string (data_file ()) (Sexp.to_string line ^ "\n")

  let syntactic_feats tac =
    let str = Pp.string_of_ppcmds @@ Sexpr.format_oneline @@
      Pptactic.pr_glob_tactic (Global.env ()) (tactic_repr tac) in
    let split = String.split_on_char ' ' str in
    List.map Hashtbl.hash split

  let generate_step (status, name, ls) =
    match cache_type name with
    | `File ->
      output_string (data_file ()) "#lemma\n";
      List.iter (fun (outcomes, tac) ->
          List.iter (fun { before; after; preds; parents; _ } ->
              let ps = proof_state_to_simple_ints before in
              let preds = CEphemeron.default preds [] in
              let preds = List.map (fun (tactic, after) ->
                  let disappear_feats = Option.default [-1] @@ Option.map (feat_disappear before) after in
                  let appear_feats = Option.default [-1] @@ Option.map (feat_appear before) after in
                  (tactic, disappear_feats, appear_feats)) preds in
              let disappear_feats = feat_disappear before after in
              let appear_feats = feat_appear before after in
              let preds = List.map (fun (tac, df, af) ->
                  Sexplib.Pre_sexp.List [Std.sexp_of_int @@ tactic_hash tac;
                                         Std.sexp_of_list Std.sexp_of_int df;
                                         Std.sexp_of_list Std.sexp_of_int af;
                                         Std.sexp_of_list Std.sexp_of_int @@ syntactic_feats tac]) preds in
              let tac' = tactic_hash tac in
              (* let neg = List.filter (fun neg_tac -> tac != neg_tac) neg in *)
              let parent_tacs = List.map (fun (_, { executions; tactic }) -> tactic_hash tactic) parents in
              let line = Sexplib.Pre_sexp.List [ Std.sexp_of_list Std.sexp_of_int ps
                                               ; Std.sexp_of_int tac'
                                               ; Sexplib.Pre_sexp.List preds
                                               ; Std.sexp_of_list Std.sexp_of_int disappear_feats
                                               ; Std.sexp_of_list Std.sexp_of_int appear_feats
                                               ; Std.sexp_of_list Std.sexp_of_int @@ syntactic_feats tac
                                               ; Std.sexp_of_list Std.sexp_of_int @@ parent_tacs ] in
              output_string (data_file ()) (Sexp.to_string line ^ "\n")
            ) outcomes
        ) ls
    | `Dependency -> ()

  (* We have to do some reversals before the evaluation *)
  let preprocess model =
    List.rev_map (fun (state, name, ls) -> state, name, List.rev ls) model

  let endline_hook () = print_endline "writing";
    let data = preprocess !last_model in
    ignore (List.iter generate_step data)

  (* let () = Declaremods.append_end_library_hook endline_hook *)
end

let () = register_online_learner "Dataset Generator Learner" (module DatasetGeneratorLearner)
let () = Tactic_learner_internal.disable_queue ()
