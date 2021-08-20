open Tactic_learner
open Serlib
open Sexplib
open Ltac_plugin
open Learner_helper
open Features
open Map_all_the_things
open Tactician_util
open Tacexpr
open Genarg
open Mapping_helpers

let data_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" Ltacrecord.base_filename ^ ".sexpr" in
       let k = Ltacrecord.open_permanently filename in
       file := Some k;
       k
     | Some f -> f)

module NormalizeDef = struct
  include MapDefTemplate (IdentityMonad)
  let map_sort = "normalize"
  let warnProblem wit =
    Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                              str "the following tactic. Please report. " ++
                              pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
end
module NormalizeMapper = MakeMapper(NormalizeDef)
open NormalizeDef
open Helpers(NormalizeDef)

type 'a k = 'a NormalizeDef.t

let placeholder = match Coqlib.lib_ref "tactician.private_constant_placeholder" with
  | Names.GlobRef.ConstRef const -> const
  | _ -> assert false

let mapper = { NormalizeDef.default_mapper with
               glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
             ; variable = (fun _ -> Names.Id.of_string "X")
             ; constant = (fun c ->
                 let body = (Global.lookup_constant c).const_body in
                 (match body with
                  | Declarations.OpaqueDef _ -> placeholder
                  | _ -> c)
               )
             ; constr_pattern = (fun _ _ -> Pattern.PMeta None)
             ; constr_expr = (fun _ _ -> CHole (None, IntroAnonymous, None))
             ; glob_constr = (fun _ _ -> Glob_term.GHole (Evar_kinds.GoalEvar, IntroAnonymous, None))
             }

let tactic_normalize = NormalizeMapper.glob_tactic_expr_map mapper

module DatasetGeneratorLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  module FH = Features.F(TS)
  open TS
  open LH
  open FH
  module LSHF = Lshf_learner.SimpleLSHF(TS)
  (* features of a proof state, positive tactic, possible tactics, disappear features, appear features *)
  type ownmodel = (proof_state * Names.Constant.t * tactic * (tactic * proof_state list option) list * proof_state list) list
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

  let learn db name outcomes tac =
    let lshfnew = LSHF.learn db.lshf name outcomes tac in
    match cache_type name with
    | `File ->
      let newdb = List.map (fun outcome ->
          outcome.before, name, tac, outcome.preds, outcome.after) outcomes @ db.database in
      last_model := newdb; {database = newdb; lshf = lshfnew}
    | `Dependency -> {database = db.database; lshf = lshfnew}
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
      Pptactic.pr_glob_tactic (Global.env ()) tac in
    let split = String.split_on_char ' ' str in
    List.map Hashtbl.hash split

  let tactic_normalize tac =
    let tac = tactic_normalize @@ Tactic_normalize.tactic_normalize (tactic_repr tac) in
    (* let tac = Tactic_substitute.tactic_substitute (fun _ -> Names.Id.of_string "X") tac in *)
    (* let tac = tactic_make tac in *)
    tac, Hashtbl.hash_param 255 255 tac

  let output_feats curr_name (before, new_name, tac, neg, after) =
    let tac, hash = tactic_normalize tac in
    if not (Names.Constant.equal curr_name new_name) then
      output_string (data_file ()) "#lemma\n";
    let ps = proof_state_to_simple_ints before in
    let neg = List.map (fun (tactic, after) ->
        let tactic, hash = tactic_normalize tactic in
        let disappear_feats = Option.default [-1] @@ Option.map (feat_disappear before) after in
        let appear_feats = Option.default [-1] @@ Option.map (feat_appear before) after in
        (tactic, hash, disappear_feats, appear_feats)) neg in
    let disappear_feats = feat_disappear before after in
    let appear_feats = feat_appear before after in
    let neg = List.map (fun (tac, hash, df, af) ->
        Sexplib.Pre_sexp.List [Std.sexp_of_int @@ hash;
                               Std.sexp_of_list Std.sexp_of_int df;
                               Std.sexp_of_list Std.sexp_of_int af;
                               Std.sexp_of_list Std.sexp_of_int @@ syntactic_feats tac]) neg in
    (* let neg = List.filter (fun neg_tac -> tac != neg_tac) neg in *)
    let line = Sexplib.Pre_sexp.List [ Std.sexp_of_list Std.sexp_of_int ps
                                     ; Std.sexp_of_int hash
                                     ; Sexplib.Pre_sexp.List neg
                                     ; Std.sexp_of_list Std.sexp_of_int disappear_feats
                                     ; Std.sexp_of_list Std.sexp_of_int appear_feats
                                     ; Std.sexp_of_list Std.sexp_of_int @@ syntactic_feats tac] in
    output_string (data_file ()) (Sexp.to_string line ^ "\n");
    new_name

  let endline_hook () = print_endline "writing";
    ignore @@ List.fold_left output_feats
      (Names.Constant.make2 Names.ModPath.initial (Names.Label.of_id @@ Names.Id.of_string "xxxxxxxx"))
      (List.rev !last_model)

  let () = Declaremods.append_end_library_hook endline_hook
end

let () = register_online_learner "Dataset Generator Learner" (module DatasetGeneratorLearner)
let () = Tactic_learner_internal.disable_queue ()
