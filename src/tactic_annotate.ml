open Ltac_plugin
open Tacexpr
open Libobject
open CAst
open Equality
open Locus

type tac_ast = Then | Dispatch | Extend | Thens | Thens3parts | First | Complete | Solve | Or
             | Once | ExactlyOnce | IfThenCatch | Orelse | Do | Timeout | Repeat | Progress
             | Abstract | LetIn | Match | MatchGoal | Arg | Select | ML | Alias | Call
             | IntroPattern | Apply | Elim | Case | MutualFix | MutualCofix | Assert
             | Generalize | LetTac | InductionDestruct | Reduce | Change | Rewrite | RewriteMulti
             | Inversion

type tac_decomposition = Decompose | Keep | Both | Discard

module TacAstMap = Map.Make(struct
    type t = tac_ast
    let compare = compare
  end)
type tac_ast_map = tac_decomposition TacAstMap.t

let tac_ast_map_ref = Summary.ref TacAstMap.empty ~name:"DecompositionMap"

let get_ast_settings () = !tac_ast_map_ref

let tac_ast_setting : tac_ast_map -> obj =
  declare_object @@ global_object_nodischarge "TacticianDecompositionSetting"
    ~cache:(fun (_,m) -> tac_ast_map_ref := m)
    ~subst:None

let ast_setting_lookup ast = Option.default Keep (TacAstMap.find_opt ast (get_ast_settings ()))

let modify_ast_setting ast dec = Lib.add_anonymous_leaf
    (tac_ast_setting (TacAstMap.add ast dec (get_ast_settings ())))

let outer_record ast = match ast_setting_lookup ast with
  | Keep | Both -> true
  | Decompose | Discard -> false

let inner_record ast = match ast_setting_lookup ast with
  | Decompose | Both -> true
  | Keep | Discard -> false

let decompose_annotate (tac : glob_tactic_expr) (r : glob_tactic_expr -> glob_tactic_expr -> glob_tactic_expr) : glob_tactic_expr =
  let mkatom loc atom =
    let t = CAst.make @@ TacAtom atom in
    r t t in
  let mktactic t = CAst.make t in
  let tacthenfirst t1 t2 = mktactic @@ TacThens3parts (t1, Array.of_list [t2], mktactic @@ TacId [], Array.of_list []) in
  let tacthenlast  t1 t2 = mktactic @@ TacThens3parts (t1, Array.of_list [], mktactic @@ TacId [], Array.of_list [t2]) in
  let decompose_apply flg1 flg2 intros loc (ls : 'trm with_bindings_arg list) =
    let no_intro intro = match intro with | [] -> [] | [n, _] -> [n, None] | _ -> assert false in
    let combiner intro = match intro with | [] -> tacthenlast | _::_ -> tacthenfirst in
    let rec apps intro = function
      | [] -> assert false
      | [s] -> mkatom loc (TacApply (flg1, flg2, [s], intro))
      | s::ls -> combiner intro (mkatom loc (TacApply (flg1, flg2, [s], no_intro intro))) (apps intro ls) in
    let rec ins = function
      | [] -> apps [] ls
      | [intro] -> apps [intro] ls
      | intro::intros -> tacthenfirst (apps [intro] ls) (ins intros) in
    ins intros in
  let decompose_generalize loc ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacGeneralize [s])
      | s::ls -> mktactic @@ TacThen (mkatom loc (TacGeneralize [s]), aux ls)
    in aux ls in
  let decompose_induction_destruct loc flg1 flg2 ls =
    let rec aux = function
      | [] -> assert false
      | [s] -> mkatom loc (TacInductionDestruct (flg1, flg2, ([s], None)))
      | s::ls -> mktactic @@ TacThen (mkatom loc (TacInductionDestruct (flg1, flg2, ([s], None))), aux ls)
    in aux ls in
  let decompose_multi loc flg inc b trm by byorig mult = (* TODO: Maybe replace this with an OCaml-level tactic? *)
    let recname = CAst.make @@ Names.Id.of_string "rec" in
    let recname' = CAst.make @@ Names.Name.mk_name recname.v in
    let reccall = mktactic @@ TacArg (Reference (ArgVar recname)) in
    (* TODO: Why can't we use the 'do' and 'repeat' tactics here again? *)
    let repeat tac = mktactic @@ TacLetIn (true, [(recname', Tacexp (mktactic @@ TacTry (tacthenfirst tac reccall)))], reccall) in
    let rec don n tac = if n > 0 then tacthenfirst tac (don (n-1) tac) else mktactic @@ TacId [] in
    let onerewrite =
      let rew = mkatom loc @@ TacRewrite (flg, [(b, Precisely 1, trm)], inc, None) in
      match by with
      | None -> rew
      | Some by -> mktactic @@ TacThens3parts (rew, Array.of_list [mktactic @@ TacId []], mktactic @@ TacSolve [by], Array.of_list [])in
    let at r = match mult with
      | Precisely 1 -> onerewrite
      | Precisely n -> r (don n (onerewrite))
      | RepeatStar -> r (repeat (onerewrite))
      | RepeatPlus -> r (tacthenfirst (onerewrite) (repeat (onerewrite)))
      | UpTo n -> r (don n (mktactic @@ TacTry (onerewrite))) in
    let r = if outer_record RewriteMulti then r (CAst.make ?loc @@ TacAtom (TacRewrite (flg, [(b, mult, trm)], inc, byorig))) else fun x -> x in
    if inner_record RewriteMulti then at r else r (CAst.make ?loc @@ TacAtom (TacRewrite (flg, [(b, mult, trm)], inc, byorig))) in
  let decompose_rewrite loc flg inc ls by byorig =
    let rec aux = function
      | [] -> assert false
      | [(b, mult, trm)] -> decompose_multi loc flg inc b trm by byorig mult
      | (b, mult, trm)::ls -> tacthenfirst (decompose_multi loc flg inc b trm by byorig mult) (aux ls)
    in aux ls in
  let rec annotate_atomic loc a : glob_tactic_expr =
    let router ast t = if outer_record ast then r (CAst.make ?loc @@ TacAtom a) t else t in
    let at = CAst.make ?loc @@ TacAtom a in
    match a with
    | TacIntroPattern _ -> router IntroPattern at
    | TacApply (flg1, flg2, ls, intro) ->
      let at = if (inner_record Apply) then decompose_apply flg1 flg2 intro loc ls else at in
      router Apply at
    | TacElim _ -> router Elim at
    | TacCase _ -> router Case at
    | TacMutualFix _ -> router MutualFix at
    | TacMutualCofix _ -> router MutualCofix at
    | TacAssert (flg, b, by, pat, term) ->
      let by = if inner_record Assert then Option.map (Option.map annotate) by else by in
      router Assert (CAst.make ?loc @@ TacAtom (TacAssert (flg, b, by, pat, term)))
    | TacGeneralize gs ->
      let at = if inner_record Generalize then decompose_generalize loc (List.rev gs) else at in
      router Generalize at
    | TacLetTac _ -> router LetTac at
    (* This is induction .. using .., which is not decomposable *)
    | TacInductionDestruct (_, _, (_, Some _)) -> router InductionDestruct at
    (* TODO: induction a, b is not equal to induction a; induction b due to name mangling *)
    | TacInductionDestruct (true, _, _) -> router InductionDestruct at
    | TacInductionDestruct (flg1, flg2, (ts, None)) ->
      let at = if inner_record InductionDestruct then decompose_induction_destruct loc flg1 flg2 ts else at in
      router InductionDestruct at
    | TacReduce _ -> router Reduce at
    | TacChange _ -> router Change at
    | TacRewrite (flg1, ts, i, d) ->
      let at = if inner_record Rewrite then decompose_rewrite loc flg1 i ts (Option.map annotate d) d else at in (* TODO: Normalize rewrite .. by t to rewrite ..; [| t] (or similar) *)
      router Rewrite at
    | TacInversion _ -> router Inversion at
  and annotate_arg x = match x with
    | TacGeneric _ -> x, r (* TODO: Deal with ssreflect stuff *)
    | ConstrMayEval _ -> x, r
    | Reference _ -> x, r
    | TacCall c -> (if inner_record Call then
        TacCall (CAst.map (fun (a, b) -> (a, List.map (fun a -> fst (annotate_arg x)) b)) c) else x), r
    | TacFreshId _ -> x, r
    | Tacexp t -> Tacexp (annotate t), fun x _ -> x
    | TacPretype _ -> x, r
    | TacNumgoals -> x, r
  (* TODO: Improve efficiency of the annotation recursion *)
  and annotate_r loc (tac' : g_dispatch gen_tactic_expr_r) : glob_tactic_expr =
    let tac = CAst.make ?loc tac' in
    let router ast t = if outer_record ast then r tac (CAst.make ?loc t) else CAst.make ?loc t in
    let rinner ast t = if inner_record ast then annotate t else t in
    match tac' with
    | TacAtom a         ->                 annotate_atomic loc a
    | TacThen (t1, t2)  ->                 router Then (TacThen (rinner Then t1, rinner Then t2))
    | TacDispatch tl    ->                 router Dispatch (TacDispatch (List.map (rinner Dispatch) tl))
    | TacExtendTac (tl1, t, tl2) ->        router Extend (TacExtendTac (Array.map (rinner Extend) tl1,
                                                                        rinner Extend t,
                                                                        Array.map (rinner Extend) tl2))
    | TacThens (t1, tl) ->                 router Thens (TacThens (rinner Thens t1, List.map (rinner Thens) tl))
    | TacThens3parts (t1, tl1, t2, tl2) ->
      router Thens3parts (TacThens3parts (rinner Thens3parts t1,
                                           Array.map (rinner Thens3parts) tl1,
                                           rinner Thens3parts t2,
                                           Array.map (rinner Thens3parts) tl2))
    | TacFirst ts       ->                 router First (TacFirst (List.map (rinner First) ts))
    | TacComplete t     ->                 router Complete (TacComplete (rinner Complete t))
    | TacSolve ts       ->                 router Solve (TacSolve (List.map (rinner Solve) ts))
    | TacTry t          ->                 CAst.make ?loc @@ TacTry (annotate tac) (* No need to record try *)
    | TacOr (t1, t2)    ->                 router Or (TacOr (rinner Or t1, rinner Or t2))
    | TacOnce t         ->                 router Once (TacOnce (rinner Once t))
    | TacExactlyOnce t  ->                 router ExactlyOnce (TacExactlyOnce (rinner ExactlyOnce t))
    | TacIfThenCatch (t1, t2, t3) ->       router IfThenCatch (TacIfThenCatch (rinner IfThenCatch t1,
                                                                               rinner IfThenCatch t2,
                                                                               rinner IfThenCatch t3))
    | TacOrelse (t1, t2) ->                router Orelse (TacOrelse (rinner Orelse t1, rinner Orelse t2))
    | TacDo (n, t) ->                      router Do (TacDo (n, rinner Do t)) (* TODO: Perform decomposition when n is a number *)
    | TacTimeout (n, t)      ->            router Timeout (TacTimeout (n, rinner Timeout t))
    | TacTime (s, t)         ->            CAst.make ?loc @@ TacTime (s, annotate t) (* No need to record try *)
    | TacRepeat t       ->                 router Repeat (TacRepeat (rinner Repeat t))
    | TacProgress t     ->                 router Progress (TacProgress (rinner Progress t))
    | TacAbstract (t, id) ->               router Abstract (TacAbstract (rinner Abstract t, id))
    | TacId _           ->                 tac (* No need to record id *)
    | TacFail _         ->                 tac (* No need to record fail *)
    | TacLetIn (flg, ts, t) ->
      let ts = if inner_record LetIn then List.map (fun (a, b) -> (a, fst (annotate_arg b))) ts else ts in
      router LetIn (TacLetIn (flg, ts, rinner LetIn t))
    | TacMatch (flg, t, ts) ->
      router Match (TacMatch (flg, rinner Match t,
                              List.map (function | All t -> All (rinner Match t)
                                                 | Pat (c, p, t) -> Pat (c, p, rinner Match t)) ts))
    | TacMatchGoal (flg, d, ts) ->
      router MatchGoal (TacMatchGoal (
          flg, d, List.map (function | All t -> All (rinner MatchGoal t)
                                     | Pat (c, p, t) -> Pat (c, p, rinner MatchGoal t)) ts))
    | TacFun (args, t) -> CAst.make ?loc @@ TacFun (args, annotate t) (* Probably not outer-recordable *)
    | TacArg x ->
      let x', r = if inner_record Arg then annotate_arg x else x, r in
      let res = CAst.make ?loc @@ TacArg x' in
      if outer_record Arg then r tac res else res
    | TacSelect (i, t)       ->            router Select (TacSelect (i, rinner Select t))
    | TacML (e, args) ->
      let args = if inner_record ML then List.map (fun a -> fst (annotate_arg a)) args else args in
      router ML (TacML (e, args)) (* TODO: Decompose interesting known tactics (such as ssreflect) *)
    | TacAlias (e, args) ->
      let tactician_cache = CString.is_prefix "Tactician.Ltac1.Tactics.search_with_cache"
          (Names.KerName.to_string e) in
      let args = if inner_record Alias || tactician_cache then
          List.map (fun a -> fst (annotate_arg a)) args else args in
      (* TODO: This is a possible decomposition *)
      (* let al = Tacenv.interp_alias e in
       * let t = TacLetIn (false, List.map2 (fun x y ->
       *     (CAst.make (Names.Name.Name x)), y) al.Tacenv.alias_args args,
       *                   al.Tacenv.alias_body) in *)
      let t = CAst.make ?loc @@ TacAlias (e, args) in
      if outer_record Alias && not tactician_cache then r tac t else t
      (* TODO: Decompose user-defined tactics *)
  and annotate CAst.{v=tac; loc} =
    annotate_r loc tac
  in annotate tac
