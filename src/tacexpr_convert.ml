open Ltac_plugin
open Coq_ast_monadic_map
open Tacexpr_functor
open Monad_util

module O = Tacexpr

module M = Mapper(IdentityMonad)

let ( glob_tactic_expr_to_glob_tactic_expr
    , glob_tactic_arg_to_glob_tactic_arg
    , glob_atomic_tactic_to_glob_atomic_tactic
    , raw_tactic_expr_to_raw_tactic_expr
    , raw_tactic_arg_to_raw_tactic_arg
    , raw_atomic_tactic_to_raw_atomic_tactic
    , g_trm_to_g_trm
    , g_pat_to_g_pat
    , glob_intro_pattern_expr_to_glob_intro_pattern_expr
    , glob_intro_pattern_action_expr_to_glob_intro_pattern_action_expr
    , glob_or_and_intro_pattern_expr_to_glob_or_and_intro_pattern_expr
    , raw_intro_pattern_expr_to_raw_intro_pattern_expr
    , raw_intro_pattern_action_expr_to_raw_intro_pattern_action_expr
    , raw_or_and_intro_pattern_expr_to_raw_or_and_intro_pattern_expr
    ) :
  (O.glob_tactic_expr -> glob_tactic_expr) *
  (O.glob_tactic_arg -> glob_tactic_arg) *
  (O.glob_atomic_tactic_expr -> glob_atomic_tactic_expr) *
  (O.raw_tactic_expr -> raw_tactic_expr) *
  (O.raw_tactic_arg -> raw_tactic_arg) *
  (O.raw_atomic_tactic_expr -> raw_atomic_tactic_expr) *
  (O.g_trm -> g_trm) *
  (O.g_pat -> g_pat) *
  (O.g_trm Tactypes.intro_pattern_expr -> g_trm intro_pattern_expr) *
  (O.g_trm Tactypes.intro_pattern_action_expr -> g_trm intro_pattern_action_expr) *
  (O.g_trm Tactypes.or_and_intro_pattern_expr -> g_trm or_and_intro_pattern_expr) *
  (Genredexpr.r_trm Tactypes.intro_pattern_expr -> r_trm intro_pattern_expr) *
  (Genredexpr.r_trm Tactypes.intro_pattern_action_expr -> r_trm intro_pattern_action_expr) *
  (Genredexpr.r_trm Tactypes.or_and_intro_pattern_expr -> r_trm or_and_intro_pattern_expr)
  =

  let rec intro_pattern_expr_to_intro_pattern_expr trm_to_trm (t : _ Tactypes.intro_pattern_expr)
    : _ intro_pattern_expr =
    match t with
    | Tactypes.IntroForthcoming a ->
      IntroForthcoming a
    | Tactypes.IntroNaming x -> IntroNaming x
    | Tactypes.IntroAction x -> IntroAction (intro_pattern_action_expr_to_intro_pattern_action_expr trm_to_trm x)
  and intro_pattern_action_expr_to_intro_pattern_action_expr trm_to_trm = function
    | Tactypes.IntroWildcard -> IntroWildcard
    | Tactypes.IntroOrAndPattern x ->
      IntroOrAndPattern (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm x)
    | Tactypes.IntroInjection x ->
      IntroInjection (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) x)
    | Tactypes.IntroApplyOn (a, b) ->
      IntroApplyOn (CAst.map trm_to_trm a, CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm) b)
    | Tactypes.IntroRewrite a -> IntroRewrite a
  and or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm = function
    | Tactypes.IntroOrPattern a ->
      IntroOrPattern (List.map (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm))) a)
    | Tactypes.IntroAndPattern a ->
      IntroAndPattern (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) a)
  in

  let induction_clause_to_induction_clause trm_to_trm ((a, (b, c), d) : (_, _) O.induction_clause)
    : _ induction_clause =
    M.destruction_arg_map (M.with_bindings_map trm_to_trm) a,
    (b,
    Option.map (M.or_var_map (CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c),
    Option.map (M.clause_expr_map (fun x -> x)) d in

  let induction_clause_list_to_induction_clause_list trm_to_trm ((a, b) : (_, _, _) O.induction_clause_list)
    : _ induction_clause_list =
    List.map (induction_clause_to_induction_clause trm_to_trm) a, Option.map (M.with_bindings_map trm_to_trm) b in

  let inversion_strength_to_inversion_strength trm_to_trm (t : (_, _, _) O.inversion_strength) =
    match t with
    | O.NonDepInversion (a, b, c) ->
      NonDepInversion (
        a, b, Option.map (M.or_var_map (
            CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c)
    | O.DepInversion (a, b, c) ->
      DepInversion (
        a, Option.map trm_to_trm b,
        Option.map (M.or_var_map (
            CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c)
    | O.InversionUsing (a, b) ->
      InversionUsing (trm_to_trm a, b)
  in

  (* These functions only exist to verify that the two `glob_tactic_expr` types are isomorphic *)
  let rec gen_atomic_tactic_expr_to_gen_atomic_tactic_expr trm_to_trm pat_to_pat t =
    match t with
    | O.TacIntroPattern (a, b) ->
      TacIntroPattern (a, List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) b)
    | O.TacApply (a, b, c, d) ->
      TacApply (a, b, List.map (M.with_bindings_arg_map trm_to_trm) c,
                Option.map (fun (a, b) -> a, Option.map (CAst.map (
                    intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) b) d)
    | O.TacElim (a, b, c) ->
      TacElim (a, M.with_bindings_arg_map trm_to_trm b, Option.map (M.with_bindings_map trm_to_trm) c)
    | O.TacCase (a, b) ->
      TacCase(a, M.with_bindings_arg_map trm_to_trm b)
    | O.TacMutualFix (a, b, c) ->
      TacMutualFix (a, b, List.map (fun (a, b, c) -> a, b, trm_to_trm c) c)
    | O.TacMutualCofix (a, b) ->
      TacMutualCofix (a, List.map (fun (a, b) -> a, trm_to_trm b) b)
    | O.TacAssert (a, b, c, d, e) ->
      TacAssert (a, b, Option.map (Option.map (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat)) c,
                 Option.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) d,
                 trm_to_trm e)
    | O.TacGeneralize a ->
      TacGeneralize (List.map (fun (a, b) -> M.with_occurrences_map trm_to_trm a, b) a)
    | O.TacLetTac (a, b, c, d, e, f) ->
      TacLetTac (a, b, trm_to_trm c, d, e, f)
    | O.TacInductionDestruct (a, b, c) ->
      TacInductionDestruct (a, b, induction_clause_list_to_induction_clause_list trm_to_trm c)
    | O.TacReduce (a, b) ->
      TacReduce (M.red_expr_gen_map trm_to_trm (fun x -> x) pat_to_pat a, b)
    | O.TacChange (a, b, c, d) ->
      TacChange (a, Option.map pat_to_pat b, trm_to_trm c, d)
    | O.TacRewrite (a, b, c, d) ->
      TacRewrite (a, List.map (fun (a, b, c) -> a, b, M.with_bindings_arg_map trm_to_trm c) b, c,
                  Option.map (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat) d)
    | O.TacInversion (a, b) ->
      TacInversion (inversion_strength_to_inversion_strength trm_to_trm a, b)
  and gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat t =
    match t with
    | O.TacGeneric a ->
      TacGeneric a
    | O.ConstrMayEval a ->
      ConstrMayEval (M.may_eval_map trm_to_trm (fun x -> x) pat_to_pat a)
    | O.Reference a ->
      Reference a
    | O.TacCall a ->
      TacCall (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a)
    | O.TacFreshId a ->
      TacFreshId a
    | O.Tacexp a ->
      Tacexp (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat a)
    | O.TacPretype a ->
      TacPretype (trm_to_trm a)
    | O.TacNumgoals ->
      TacNumgoals
  and gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat t =
    let r = gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat in
    match t with
    | O.TacAtom a ->
      TacAtom (CAst.map (gen_atomic_tactic_expr_to_gen_atomic_tactic_expr trm_to_trm pat_to_pat) a)
    | O.TacThen (a, b) ->
      TacThen (r a, r b)
    | O.TacDispatch a ->
      TacDispatch (List.map r a)
    | O.TacExtendTac (a, b, c) ->
      TacExtendTac (Array.map r a, r b, Array.map r c)
    | O.TacThens (a, b) ->
      TacThens (r a, List.map r b)
    | O.TacThens3parts (a, b, c, d) ->
      TacThens3parts (r a, Array.map r b, r c, Array.map r d)
    | O.TacFirst a ->
      TacFirst (List.map r a)
    | O.TacComplete a ->
      TacComplete (r a)
    | O.TacSolve a ->
      TacSolve (List.map r a)
    | O.TacTry a ->
      TacTry (r a)
    | O.TacOr (a, b) ->
      TacOr (r a, r b)
    | O.TacOnce a ->
      TacOnce (r a)
    | O.TacExactlyOnce a ->
      TacExactlyOnce (r a)
    | O.TacIfThenCatch (a, b, c) ->
      TacIfThenCatch (r a, r b, r c)
    | O.TacOrelse (a, b) ->
      TacOrelse (r a, r b)
    | O.TacDo (a, b) ->
      TacDo (a, r b)
    | O.TacTimeout (a, b) ->
      TacTimeout (a, r b)
    | O.TacTime (a, b) ->
      TacTime (a, r b)
    | O.TacRepeat a ->
      TacRepeat (r a)
    | O.TacProgress a ->
      TacProgress (r a)
    | O.TacShowHyps a ->
      TacShowHyps (r a)
    | O.TacAbstract (a, b) ->
      TacAbstract (r a, b)
    | O.TacId a ->
      TacId a
    | O.TacFail (a, b, c) ->
      TacFail (a, b, c)
    | O.TacInfo a ->
      TacInfo (r a)
    | O.TacLetIn (a, b, c) ->
      TacLetIn (a, List.map (fun (a, b) -> a, gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat b) b, r c)
    | O.TacMatch (a, b, c) ->
      TacMatch (a, r b, List.map (M.match_rule_map pat_to_pat r) c)
    | O.TacMatchGoal (a, b, c) ->
      TacMatchGoal (a, b, List.map (M.match_rule_map pat_to_pat r) c)
    | O.TacFun a ->
      TacFun (M.gen_tactic_fun_ast_map r a)
    | O.TacArg a ->
      TacArg (CAst.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) a)
    | O.TacSelect (a, b) ->
      TacSelect (a, r b)
    | O.TacML a ->
      TacML (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a)
    | O.TacAlias a ->
      TacAlias (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a) in
  let g_trm_to_g_trm ((a, b) : O.g_trm) : g_trm =
    Glob_term_convert.glob_constr_to_glob_constr a, Option.map Constrexpr_convert.constr_expr_to_constr_expr b in
  let g_pat_to_g_pat ((a, b, c) : O.g_pat) : g_pat =
    a, g_trm_to_g_trm b, Pattern_convert.constr_pattern_to_constr_pattern c in
  let r_trm_to_r_trm (t : Genredexpr.r_trm) : r_trm =
    Constrexpr_convert.constr_expr_to_constr_expr t in
  let r_pat_to_r_pat (t : Genredexpr.r_pat) : r_pat =
    r_trm_to_r_trm t in
  let glob_atomic_tactic_expr_to_glob_atomic_tactic_expr (t : O.glob_atomic_tactic_expr) : glob_atomic_tactic_expr =
    gen_atomic_tactic_expr_to_gen_atomic_tactic_expr g_trm_to_g_trm g_pat_to_g_pat t in
  let glob_tactic_arg_to_glob_tactic_arg (t : O.glob_tactic_arg) : glob_tactic_arg =
    gen_tactic_arg_to_gen_tactic_arg g_trm_to_g_trm g_pat_to_g_pat t in
  let glob_tactic_expr_to_glob_tactic_expr (t : O.glob_tactic_expr) : glob_tactic_expr =
    gen_tactic_expr_to_gen_tactic_expr g_trm_to_g_trm g_pat_to_g_pat t in
  let raw_atomic_tactic_expr_to_raw_atomic_tactic_expr (t : O.raw_atomic_tactic_expr) : raw_atomic_tactic_expr =
    gen_atomic_tactic_expr_to_gen_atomic_tactic_expr r_trm_to_r_trm r_pat_to_r_pat t in
  let raw_tactic_arg_to_raw_tactic_arg (t : O.raw_tactic_arg) : raw_tactic_arg =
    gen_tactic_arg_to_gen_tactic_arg r_trm_to_r_trm r_pat_to_r_pat t in
  let raw_tactic_expr_to_raw_tactic_expr (t : O.raw_tactic_expr) : raw_tactic_expr =
    gen_tactic_expr_to_gen_tactic_expr r_trm_to_r_trm r_pat_to_r_pat t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = glob_tactic_expr_to_glob_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = glob_tactic_arg_to_glob_tactic_arg t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = glob_atomic_tactic_expr_to_glob_atomic_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_tactic_expr_to_raw_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_tactic_arg_to_raw_tactic_arg t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_atomic_tactic_expr_to_raw_atomic_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = g_pat_to_g_pat t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_expr_to_intro_pattern_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_action_expr_to_intro_pattern_action_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = or_and_intro_pattern_expr_to_or_and_intro_pattern_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_expr_to_intro_pattern_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_action_expr_to_intro_pattern_action_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = or_and_intro_pattern_expr_to_or_and_intro_pattern_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)

let ( glob_tactic_expr_to_glob_tactic_expr2
    , glob_tactic_arg_to_glob_tactic_arg2
    , glob_atomic_tactic_to_glob_atomic_tactic2
    , raw_tactic_expr_to_raw_tactic_expr2
    , raw_tactic_arg_to_raw_tactic_arg2
    , raw_atomic_tactic_to_raw_atomic_tactic2
    , g_trm_to_g_trm2
    , g_pat_to_g_pat2
    , glob_intro_pattern_expr_to_glob_intro_pattern_expr2
    , glob_intro_pattern_action_expr_to_glob_intro_pattern_action_expr2
    , glob_or_and_intro_pattern_expr_to_glob_or_and_intro_pattern_expr2
    , raw_intro_pattern_expr_to_raw_intro_pattern_expr2
    , raw_intro_pattern_action_expr_to_raw_intro_pattern_action_expr2
    , raw_or_and_intro_pattern_expr_to_raw_or_and_intro_pattern_expr2
    ) :
  (glob_tactic_expr -> O.glob_tactic_expr) *
  (glob_tactic_arg -> O.glob_tactic_arg) *
  (glob_atomic_tactic_expr -> O.glob_atomic_tactic_expr) *
  (raw_tactic_expr -> O.raw_tactic_expr) *
  (raw_tactic_arg -> O.raw_tactic_arg) *
  (raw_atomic_tactic_expr -> O.raw_atomic_tactic_expr) *
  (g_trm -> O.g_trm) *
  (g_pat -> O.g_pat) *
  (g_trm intro_pattern_expr -> O.g_trm Tactypes.intro_pattern_expr) *
  (g_trm intro_pattern_action_expr -> O.g_trm Tactypes.intro_pattern_action_expr) *
  (g_trm or_and_intro_pattern_expr -> O.g_trm Tactypes.or_and_intro_pattern_expr) *
  (r_trm intro_pattern_expr -> Genredexpr.r_trm Tactypes.intro_pattern_expr) *
  (r_trm intro_pattern_action_expr -> Genredexpr.r_trm Tactypes.intro_pattern_action_expr) *
  (r_trm or_and_intro_pattern_expr -> Genredexpr.r_trm Tactypes.or_and_intro_pattern_expr)
  =

  let rec intro_pattern_expr_to_intro_pattern_expr trm_to_trm (t : _ intro_pattern_expr)
    : _ Tactypes.intro_pattern_expr =
    match t with
    | IntroForthcoming a ->
      Tactypes.IntroForthcoming a
    | IntroNaming x -> Tactypes.IntroNaming x
    | IntroAction x -> Tactypes.IntroAction (intro_pattern_action_expr_to_intro_pattern_action_expr trm_to_trm x)
  and intro_pattern_action_expr_to_intro_pattern_action_expr trm_to_trm = function
    | IntroWildcard -> Tactypes.IntroWildcard
    | IntroOrAndPattern x ->
      Tactypes.IntroOrAndPattern (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm x)
    | IntroInjection x ->
      Tactypes.IntroInjection (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) x)
    | IntroApplyOn (a, b) ->
      Tactypes.IntroApplyOn (CAst.map trm_to_trm a, CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm) b)
    | IntroRewrite a -> Tactypes.IntroRewrite a
  and or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm = function
    | IntroOrPattern a ->
      Tactypes.IntroOrPattern (List.map (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm))) a)
    | IntroAndPattern a ->
      Tactypes.IntroAndPattern (List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) a)
  in

  let induction_clause_to_induction_clause trm_to_trm ((a, (b, c), d) : _ induction_clause)
    : (_, _) O.induction_clause =
    M.destruction_arg_map (M.with_bindings_map trm_to_trm) a,
    (b,
    Option.map (M.or_var_map (CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c),
    Option.map (M.clause_expr_map (fun x -> x)) d in

  let induction_clause_list_to_induction_clause_list trm_to_trm ((a, b) : _ induction_clause_list)
    : (_, _, _) O.induction_clause_list =
    List.map (induction_clause_to_induction_clause trm_to_trm) a, Option.map (M.with_bindings_map trm_to_trm) b in

  let inversion_strength_to_inversion_strength trm_to_trm (t : _ inversion_strength) =
    match t with
    | NonDepInversion (a, b, c) ->
      O.NonDepInversion (
        a, b, Option.map (M.or_var_map (
            CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c)
    | DepInversion (a, b, c) ->
      O.DepInversion (
        a, Option.map trm_to_trm b,
        Option.map (M.or_var_map (
            CAst.map (or_and_intro_pattern_expr_to_or_and_intro_pattern_expr trm_to_trm))) c)
    | InversionUsing (a, b) ->
      O.InversionUsing (trm_to_trm a, b)
  in
  (* These functions only exist to verify that the two `glob_tactic_expr` types are isomorphic *)
  let rec gen_atomic_tactic_expr_to_gen_atomic_tactic_expr trm_to_trm pat_to_pat t =
    match t with
    | TacIntroPattern (a, b) ->
      O.TacIntroPattern (a, List.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) b)
    | TacApply (a, b, c, d) ->
      O.TacApply (
        a, b, List.map (M.with_bindings_arg_map trm_to_trm) c,
        Option.map (fun (a, b) -> a, Option.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) b) d)
    | TacElim (a, b, c) ->
      O.TacElim (a, M.with_bindings_arg_map trm_to_trm b, Option.map (M.with_bindings_map trm_to_trm) c)
    | TacCase (a, b) ->
      O.TacCase(a, M.with_bindings_arg_map trm_to_trm b)
    | TacMutualFix (a, b, c) ->
      O.TacMutualFix (a, b, List.map (fun (a, b, c) -> a, b, trm_to_trm c) c)
    | TacMutualCofix (a, b) ->
      O.TacMutualCofix (a, List.map (fun (a, b) -> a, trm_to_trm b) b)
    | TacAssert (a, b, c, d, e) ->
      O.TacAssert (a, b, Option.map (Option.map (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat)) c,
                 Option.map (CAst.map (intro_pattern_expr_to_intro_pattern_expr trm_to_trm)) d,
                 trm_to_trm e)
    | TacGeneralize a ->
      O.TacGeneralize (List.map (fun (a, b) -> M.with_occurrences_map trm_to_trm a, b) a)
    | TacLetTac (a, b, c, d, e, f) ->
      O.TacLetTac (a, b, trm_to_trm c, d, e, f)
    | TacInductionDestruct (a, b, c) ->
      O.TacInductionDestruct (a, b, induction_clause_list_to_induction_clause_list trm_to_trm c)
    | TacReduce (a, b) ->
      O.TacReduce (M.red_expr_gen_map trm_to_trm (fun x -> x) pat_to_pat a, b)
    | TacChange (a, b, c, d) ->
      O.TacChange (a, Option.map pat_to_pat b, trm_to_trm c, d)
    | TacRewrite (a, b, c, d) ->
      O.TacRewrite (a, List.map (fun (a, b, c) -> a, b, M.with_bindings_arg_map trm_to_trm c) b, c,
                    Option.map (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat) d)
    | TacInversion (a, b) ->
      O.TacInversion (inversion_strength_to_inversion_strength trm_to_trm a, b)
  and gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat t =
    match t with
    | TacGeneric a ->
      O.TacGeneric a
    | ConstrMayEval a ->
      O.ConstrMayEval (M.may_eval_map trm_to_trm (fun x -> x) pat_to_pat a)
    | Reference a ->
      O.Reference a
    | TacCall a ->
      O.TacCall (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a)
    | TacFreshId a ->
      O.TacFreshId a
    | Tacexp a ->
      O.Tacexp (gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat a)
    | TacPretype a ->
      O.TacPretype (trm_to_trm a)
    | TacNumgoals ->
      O.TacNumgoals
  and gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat t =
    let r = gen_tactic_expr_to_gen_tactic_expr trm_to_trm pat_to_pat in
    match t with
    | TacAtom a ->
      O.TacAtom (CAst.map (gen_atomic_tactic_expr_to_gen_atomic_tactic_expr trm_to_trm pat_to_pat) a)
    | TacThen (a, b) ->
      O.TacThen (r a, r b)
    | TacDispatch a ->
      O.TacDispatch (List.map r a)
    | TacExtendTac (a, b, c) ->
      O.TacExtendTac (Array.map r a, r b, Array.map r c)
    | TacThens (a, b) ->
      O.TacThens (r a, List.map r b)
    | TacThens3parts (a, b, c, d) ->
      O.TacThens3parts (r a, Array.map r b, r c, Array.map r d)
    | TacFirst a ->
      O.TacFirst (List.map r a)
    | TacComplete a ->
      O.TacComplete (r a)
    | TacSolve a ->
      O.TacSolve (List.map r a)
    | TacTry a ->
      O.TacTry (r a)
    | TacOr (a, b) ->
      O.TacOr (r a, r b)
    | TacOnce a ->
      O.TacOnce (r a)
    | TacExactlyOnce a ->
      O.TacExactlyOnce (r a)
    | TacIfThenCatch (a, b, c) ->
      O.TacIfThenCatch (r a, r b, r c)
    | TacOrelse (a, b) ->
      O.TacOrelse (r a, r b)
    | TacDo (a, b) ->
      O.TacDo (a, r b)
    | TacTimeout (a, b) ->
      O.TacTimeout (a, r b)
    | TacTime (a, b) ->
      O.TacTime (a, r b)
    | TacRepeat a ->
      O.TacRepeat (r a)
    | TacProgress a ->
      O.TacProgress (r a)
    | TacShowHyps a ->
      O.TacShowHyps (r a)
    | TacAbstract (a, b) ->
      O.TacAbstract (r a, b)
    | TacId a ->
      O.TacId a
    | TacFail (a, b, c) ->
      O.TacFail (a, b, c)
    | TacInfo a ->
      O.TacInfo (r a)
    | TacLetIn (a, b, c) ->
      O.TacLetIn (a, List.map (fun (a, b) -> a, gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat b) b, r c)
    | TacMatch (a, b, c) ->
      O.TacMatch (a, r b, List.map (M.match_rule_map pat_to_pat r) c)
    | TacMatchGoal (a, b, c) ->
      O.TacMatchGoal (a, b, List.map (M.match_rule_map pat_to_pat r) c)
    | TacFun a ->
      O.TacFun (M.gen_tactic_fun_ast_map r a)
    | TacArg a ->
      O.TacArg (CAst.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) a)
    | TacSelect (a, b) ->
      O.TacSelect (a, r b)
    | TacML a ->
      O.TacML (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a)
    | TacAlias a ->
      O.TacAlias (CAst.map (fun (a, b) -> a, List.map (gen_tactic_arg_to_gen_tactic_arg trm_to_trm pat_to_pat) b) a) in
  let g_trm_to_g_trm ((a, b) : g_trm) : O.g_trm =
    Glob_term_convert.glob_constr_to_glob_constr2 a, Option.map Constrexpr_convert.constr_expr_to_constr_expr2 b in
  let g_pat_to_g_pat ((a, b, c) : g_pat) : O.g_pat =
    a, g_trm_to_g_trm b, Pattern_convert.constr_pattern_to_constr_pattern2 c in
  let r_trm_to_r_trm (t : r_trm) : Genredexpr.r_trm =
    Constrexpr_convert.constr_expr_to_constr_expr2 t in
  let r_pat_to_r_pat (t : r_pat) : Genredexpr.r_pat =
    r_trm_to_r_trm t in
  let glob_atomic_tactic_expr_to_glob_atomic_tactic_expr (t : glob_atomic_tactic_expr) : O.glob_atomic_tactic_expr =
    gen_atomic_tactic_expr_to_gen_atomic_tactic_expr g_trm_to_g_trm g_pat_to_g_pat t in
  let glob_tactic_arg_to_glob_tactic_arg (t : glob_tactic_arg) : O.glob_tactic_arg =
    gen_tactic_arg_to_gen_tactic_arg g_trm_to_g_trm g_pat_to_g_pat t in
  let glob_tactic_expr_to_glob_tactic_expr (t : glob_tactic_expr) : O.glob_tactic_expr =
    gen_tactic_expr_to_gen_tactic_expr g_trm_to_g_trm g_pat_to_g_pat t in
  let raw_atomic_tactic_expr_to_raw_atomic_tactic_expr (t : raw_atomic_tactic_expr) : O.raw_atomic_tactic_expr =
    gen_atomic_tactic_expr_to_gen_atomic_tactic_expr r_trm_to_r_trm r_pat_to_r_pat t in
  let raw_tactic_arg_to_raw_tactic_arg (t : raw_tactic_arg) : O.raw_tactic_arg =
    gen_tactic_arg_to_gen_tactic_arg r_trm_to_r_trm r_pat_to_r_pat t in
  let raw_tactic_expr_to_raw_tactic_expr (t : raw_tactic_expr) : O.raw_tactic_expr =
    gen_tactic_expr_to_gen_tactic_expr r_trm_to_r_trm r_pat_to_r_pat t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = glob_tactic_expr_to_glob_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = glob_tactic_arg_to_glob_tactic_arg t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = glob_atomic_tactic_expr_to_glob_atomic_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_tactic_expr_to_raw_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_tactic_arg_to_raw_tactic_arg t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = raw_atomic_tactic_expr_to_raw_atomic_tactic_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = g_pat_to_g_pat t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_expr_to_intro_pattern_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_action_expr_to_intro_pattern_action_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = or_and_intro_pattern_expr_to_or_and_intro_pattern_expr g_trm_to_g_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_expr_to_intro_pattern_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = intro_pattern_action_expr_to_intro_pattern_action_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = or_and_intro_pattern_expr_to_or_and_intro_pattern_expr r_trm_to_r_trm t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
