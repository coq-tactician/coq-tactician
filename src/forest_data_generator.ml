open Tactic_learner
open Ltac_plugin
open Learner_helper
open Sexplib
open Map_all_the_things
open Mapping_helpers
open Monad_util
open Genarg


let data_file =
  let file = ref None in
  (fun () ->
     match !file with
     | None -> let filename = Option.default "" Tactician_util.base_filename ^ ".sexpr" in
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

  (* optimized *)
  let optimized_mapper = { NormalizeDef.default_mapper with
    glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))}
  let tactic_normalize_optimized = NormalizeMapper.glob_tactic_expr_map optimized_mapper
  let opaque_mapper = { NormalizeDef.default_mapper with
    glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
    ; variable = (fun _ -> Names.Id.of_string "X")
    ; constant = (fun c ->
      let body = (Global.lookup_constant c).const_body in (
        match body with
        | Declarations.OpaqueDef _ -> placeholder
        | _ -> c))}

  (* constants *)
  let constants_mapper = { NormalizeDef.default_mapper with
    glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
    ; variable = (fun _ -> Names.Id.of_string "X")
    ; constant = (fun c -> placeholder)}

  (* no-terms *)

  let no_terms_mapper = { NormalizeDef.default_mapper with
    glob_constr_and_expr = (fun (expr, _) g -> g (expr, None))
    ; variable = (fun _ -> Names.Id.of_string "X")
    ; constant = (fun c ->
      let body = (Global.lookup_constant c).const_body in
      (match body with
      | Declarations.OpaqueDef _ -> placeholder
      | _ -> c))
    ; constr_pattern = (fun _ _ -> Pattern.PMeta None)
    ; constr_expr = (fun _ _ -> CHole (None, IntroAnonymous, None))
    ; glob_constr = (fun _ _ -> Glob_term.GHole (Evar_kinds.GoalEvar, IntroAnonymous, None))
  }


module DatasetGeneratorLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  module FH = Features.F(TS)
  open TS
  open FH
  module LSHF = Naiveknn_learner.ComplexNaiveKnn(TS)
  (* module LSHF = Naiveknn_learner.SimpleNaiveKnn(TS) *)

  type ownmodel = (origin * (outcome list * tactic) list) list
  type model = {database : ownmodel; lshf : LSHF.model}

  module IntSet = Set.Make(struct type t = feature let compare = compare end)

  let last_model = Summary.ref ~name:"dataset-generator-learner-lastmodel" []

  let empty () = {database = []; lshf = LSHF.empty ()}

  let rec feat_to_diff_and_count (feat, count) feats_and_counts' =
    match feats_and_counts' with
    | [] -> (feat, count)
    | (feat', count'):: tl->
      if feat == feat' then
        (if count > count' then (feat, count - count') else (-1,-1))
      else feat_to_diff_and_count (feat, count) tl

  let get_state_diff_and_count int_and_count int_and_count'=
    List.rev (List.fold_left (fun acc (int_feat, count) ->
      let diff = feat_to_diff_and_count (int_feat, count) int_and_count' in
      if diff != (-1, -1) then (diff::acc) else acc
    ) [] int_and_count)

  let get_tac_semantic_aux before_state after_state =
    let int_and_count = proof_state_to_complex_ints_counts_no_kind before_state in
    let int_and_count' = proof_state_to_complex_ints_counts_no_kind after_state in
    let disappear_feats = get_state_diff_and_count int_and_count int_and_count' in
    let appear_feats = get_state_diff_and_count int_and_count' int_and_count in
    disappear_feats, appear_feats

  let get_tac_semantic before_state after_states =
    (* let proof_state_to_simple_features = (fun state -> (proof_state_to_simple_features 2 state)) in *)
    let disappear_feats, appear_feats =
    if after_states != [] then
      List.fold_left (
        fun (disappear_feats_acc, appear_feats_acc) after_state ->
          let disappear_feats', appear_feats' = get_tac_semantic_aux before_state after_state in
          disappear_feats_acc@disappear_feats', appear_feats_acc@appear_feats'
      )  ([], []) after_states
    else proof_state_to_complex_ints_counts_no_kind before_state, []
    in
    (* List.sort_uniq (fun (feat1, num1) (feat2, num2) -> Int.compare feat1 feat2) *) disappear_feats,
    (* List.sort_uniq (fun (feat1, num1) (feat2, num2) -> Int.compare feat1 feat2) *) appear_feats

  let cache_type name =
    let dirp = Global.current_dirpath () in
    if Libnames.is_dirpath_prefix_of dirp (Libnames.dirpath name) then `File else `Dependency

  let learn db (name, status) outcomes tac =
    let lshfnew = LSHF.learn db.lshf (name, status) outcomes tac in
    let new_database = match db.database with
      | ((pname, pstatus), ls)::data when Libnames.eq_full_path name pname ->
        ((pname, pstatus), (outcomes, tac)::ls)::data
      | _ -> ((name, status), [outcomes, tac])::db.database in
    last_model := new_database; {database = new_database; lshf = lshfnew}
  let predict db situations = LSHF.predict db.lshf situations
  let evaluate db _ _ = 0., db

  let syntactic_feats tac =
    let str = Pp.string_of_ppcmds @@ Sexpr.format_oneline @@
      Pptactic.pr_glob_tactic (Global.env ()) tac in
    let split = String.split_on_char ' ' str in
    List.map Hashtbl.hash split


  let tactic_local_context_sexpr ctx tac =
    let tac = Tactic_name_remove.tactic_name_remove @@ tactic_repr tac in
    let tac = Tactic_normalize.tactic_normalize @@ Tactic_normalize.tactic_strict @@ tac in
    let args, tac = Tactic_one_variable.tactic_one_variable tac in
    let ctxids = List.map Context.Named.Declaration.get_id ctx in
    let arg_index arg = Tactician_util.safe_index0 Names.Id.equal arg ctxids in
    let args = List.map (fun arg ->
        let x = Option.cata arg_index None arg in
        Option.default (-1) x) args in
    let tac = Extreme_tactic_normalize.tactic_normalize tac in
    let hash = Hashtbl.hash_param 255 255 tac in
    Sexplib.Pre_sexp.List
      [ Std.sexp_of_int hash
      (* ; Std.sexp_of_string (Pp.string_of_ppcmds @@ Pptactic.pr_glob_tactic (Global.env ()) tac) *)
      ; Std.sexp_of_list Std.sexp_of_int @@ syntactic_feats tac
      ; Std.sexp_of_list Std.sexp_of_int @@ args ]

  let tactic_normalize tac mapper =
    let tac = NormalizeMapper.glob_tactic_expr_map mapper (tactic_repr tac) in
    let tac =  tactic_make tac in
    let hash = tactic_hash tac in
    let tac_str =  LH.sexpr_to_string (tactic_sexpr tac) in
    tac_str, hash



  let generate_step ((name, status), ls) =
    match cache_type name with
    | `File ->
      output_string (data_file ()) "#lemma\n";
      List.iter (fun (outcomes, tac) ->
          List.iter (fun { before; after; preds; parents; _ } ->
              (* let ps = proof_state_to_simple_ints before in *)
              let ps =  proof_state_to_complex_ints_counts_no_kind before in
              let preds = List.rev_map (fun (tactic, after) ->
                let disappear_feats, appear_feats = 
                  if after = None then [(-1, -1)], [(-1, -1)]
                  else get_tac_semantic before (Option.get after) in
                  (tactic, disappear_feats, appear_feats)) preds in
              let disappear_feats, appear_feats = get_tac_semantic before after in
              let preds = List.rev_map (fun (tac, df, af) ->
                  Sexplib.Pre_sexp.List
                    [ tactic_local_context_sexpr (proof_state_hypotheses before) tac
                    ; Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int) df
                    ; Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int) af
                    ]) preds in
              (* let neg = List.filter (fun neg_tac -> tac != neg_tac) neg in *)
              let parent_tacs = List.map (fun (_, { executions; tactic }) ->
                let _tac_str, hash = tactic_normalize tactic optimized_mapper in
                let syn = syntactic_feats (tactic_repr tactic) in
                Sexplib.Pre_sexp.List [Std.sexp_of_int hash; Std.sexp_of_list Std.sexp_of_int @@ syn]
                ) parents in
              let lcontext = proof_state_hypotheses before in
              let mk_feats t =
                let feat_map = term_sexpr_to_complex_ints_no_kind (Int.hash 2000) 2 Int.Map.empty (term_repr t) in
                List.rev (Int.Map.fold (fun feat count acc -> (feat, count) :: acc) feat_map []) in
               let lcontext = List.map (function
                  | Context.Named.Declaration.LocalAssum (id, typ) -> mk_feats typ
                  | Context.Named.Declaration.LocalDef (id, typ, trm) -> (mk_feats typ @ mk_feats trm)
                ) lcontext in
              let line = Sexplib.Pre_sexp.List
                  [ Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int) ps
                  (* ; Std.sexp_of_int (tactic_hash tac) *)
                  ; tactic_local_context_sexpr (proof_state_hypotheses before) tac
                  ; Sexplib.Pre_sexp.List preds
                  ; Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int) disappear_feats
                  ; Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int) appear_feats 
                  ; Sexplib.Pre_sexp.List parent_tacs
                  ; Std.sexp_of_list (Std.sexp_of_list (Conv.sexp_of_pair Std.sexp_of_int Std.sexp_of_int)) lcontext
                  ] in
              output_string (data_file ()) (Sexp.to_string line ^ "\n")
            ) outcomes
        ) ls
    | `Dependency -> ()

  (* We have to do some reversals before the evaluation *)
  let preprocess model =
    List.rev_map (fun (origin, ls) -> origin, List.rev ls) model

  let endline_hook () = print_endline "writing";
    let data = preprocess !last_model in
    ignore (List.iter generate_step data)

  let () = Declaremods.append_end_library_hook endline_hook
end

let () = register_online_learner "Dataset Generator Learner" (module DatasetGeneratorLearner)
let () = Tactic_learner_internal.disable_queue ()
