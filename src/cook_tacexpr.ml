open Ltac_plugin
open Tacexpr
open Locus
open Util
open Geninterp
open Genarg

type pr_string = PrString of string
let wit_pr_arg : (Empty.t, pr_string, Empty.t) Genarg.genarg_type =
  let wit = Genarg.create_arg "pr_arg" in
  let () = register_val0 wit None in
  wit

(* let genarg_print env map (tac : glob_tactic_expr) : glob_tactic_expr =
 *   let rec genarg_print_atomic a =
 *     match a with
 *     | TacAssert (flg, b, by, pat, term) ->
 *       TacAssert (flg, b, Option.map (Option.map genarg_print) by, pat, term)
 *     | TacRewrite (flg1, ts, i, d) -> TacRewrite (flg1, ts, i, Option.map genarg_print d)
 *     | _ -> a
 *   and genarg_print_args x =
 *     let open Genarg in
 *     match x with
 *     | TacGeneric g ->
 *       let (GenArg (Glbwit k, u)) = g in
 *       (match k with
 *        | Genarg.ExtraArg _ -> print_endline "e"
 *        | Genarg.ListArg _ -> print_endline "l"
 *        | Genarg.OptArg _ -> print_endline "o"
 *        | Genarg.PairArg (_, _) -> print_endline "p");
 *       let default arg =
 *         let str = Pp.string_of_ppcmds (Pptactic.pr_glob_tactic env (TacArg (CAst.make (TacGeneric arg)))) in
 *         in_gen (glbwit wit_pr_arg) (PrString str) in
 *       let f () b arg = (), b, genarg_print arg in
 *       let _, _, res = Witness_whitelist.fold_genarg_tactic f default g () false in
 *       TacGeneric res
 *     | TacCall CAst.{v=(id, args)} ->
 *       TacCall (CAst.make (id, List.map genarg_print_args args))
 *     | Tacexp t -> Tacexp (genarg_print t)
 *     | _ -> x
 *   and genarg_print (tac : glob_tactic_expr) =
 *     match tac with
 *     | TacAtom CAst.{v} -> TacAtom (CAst.make (genarg_print_atomic v))
 *     | TacThen (t1, t2) -> TacThen (genarg_print t1, genarg_print t2)
 *     | TacDispatch tl -> TacDispatch (List.map genarg_print tl)
 *     | TacExtendTac (tl1, t, tl2) ->
 *       TacExtendTac (Array.map genarg_print tl1, genarg_print t, Array.map genarg_print tl2)
 *     | TacThens (t1, tl) ->
 *       TacThens (genarg_print t1, List.map genarg_print tl)
 *     | TacThens3parts (t1, tl1, t2, tl2) ->
 *       TacThens3parts (genarg_print t1, Array.map genarg_print tl1, genarg_print t2, Array.map genarg_print tl2)
 *     | TacFirst ts -> TacFirst (List.map genarg_print ts)
 *     | TacComplete t -> TacComplete (genarg_print t)
 *     | TacSolve ts -> TacSolve (List.map genarg_print ts)
 *     | TacTry t -> TacTry (genarg_print t)
 *     | TacOr (t1, t2) -> TacOr (genarg_print t1, genarg_print t2)
 *     | TacOnce t -> TacOnce (genarg_print t)
 *     | TacExactlyOnce t -> TacExactlyOnce (genarg_print t)
 *     | TacIfThenCatch (t1, t2, t3) -> TacIfThenCatch (genarg_print t1, genarg_print t2, genarg_print t3)
 *     | TacOrelse (t1, t2) -> TacOrelse (genarg_print t1, genarg_print t2)
 *     | TacDo (n, t) -> TacDo (n, genarg_print t)
 *     | TacTimeout (n, t) -> TacTimeout (n, genarg_print t)
 *     | TacTime (s, t) -> TacTime (s, genarg_print t)
 *     | TacRepeat t -> TacRepeat (genarg_print t)
 *     | TacProgress t -> TacProgress (genarg_print t)
 *     | TacShowHyps t -> TacShowHyps (genarg_print t)
 *     | TacAbstract (t, id) -> TacAbstract (genarg_print t, id)
 *     | TacId _ -> tac
 *     | TacFail _ -> tac
 *     | TacInfo t -> TacInfo (genarg_print t)
 *     | TacLetIn (flg, ts, t) ->
 *       TacLetIn (flg, List.map (fun (id, a) -> (id, genarg_print_args a)) ts, genarg_print t)
 *     | TacMatch (flg, t, ts) ->
 *       TacMatch (flg, genarg_print t, List.map (function
 *           | Pat (hyp, pat, a) -> Pat (hyp, pat, genarg_print a)
 *           | All a -> All (genarg_print a)) ts)
 *     | TacMatchGoal (flg, d, ts) ->
 *       TacMatchGoal (flg, d, List.map (function
 *           | Pat (hyp, pat, a) -> Pat (hyp, pat, genarg_print a)
 *           | All a -> All (genarg_print a)) ts)
 *     | TacFun (args, t) -> TacFun (args, genarg_print t)
 *     | TacArg CAst.{v} -> TacArg (CAst.make (genarg_print_args v))
 *     | TacSelect (i, t) -> TacSelect (i, genarg_print t)
 *     | TacML CAst.{v=(e, args)} -> TacML (CAst.make (e, List.map genarg_print_args args))
 *     | TacAlias CAst.{v=(id, args)} ->
 *       TacAlias (CAst.make (id, List.map genarg_print_args args))
 *   in genarg_print tac *)

let correct_kername id =
  try
    let _ = Tacenv.interp_ltac id in ArgArg (None, id), []
  with Not_found ->
    let kername_tolname id = CAst.make (Names.(Label.to_id (KerName.label id))) in
    ArgVar (kername_tolname id), [id]

let cook (tac : glob_tactic_expr) : glob_tactic_expr * Names.KerName.t list =
  let rec cook_atomic a =
    match a with
    | TacAssert (flg, b, by, pat, term) ->
      let by, ids = match by with
        | None -> None,  []
        | Some by -> match by with
          | None -> (Some None), []
          | Some by -> let by, ids = cook by in Some (Some by), ids in
      TacAssert (flg, b, by, pat, term), ids
    | TacRewrite (flg1, ts, i, d) ->
      let d, ids = match d with
        | None -> None, []
        | Some d -> let d, ids = cook d in Some d, ids in
      TacRewrite (flg1, ts, i, d), ids
    | _ -> a, []
  and cook_args args = List.fold_right (fun a (args, ids) ->
      let a, ids' = cook_arg a in a::args, ids@ids') args ([], [])
  and cook_arg x =
    match x with
    | TacGeneric g ->
      let f ids arg = let ret, ids' = cook arg in
        ids'@ids, ret in
      let ls, res = Witness_whitelist.fold_genarg_tactic f g [] in
      TacGeneric res, ls
    | Reference (ArgArg (_, id)) ->
      let id, ids = correct_kername id in
      Reference id, ids
    | TacCall CAst.{v=(id, args)} ->
      let id, ids = match id with
        | Locus.ArgArg (_, id) -> correct_kername id
        | Locus.ArgVar _ -> id, [] in
      let args, ids' = cook_args args in
      TacCall (CAst.make (id, args)), ids@ids'
    | Tacexp t -> let t, ids = cook t in Tacexp t, ids
    | _ -> x,  []
  and cook_tacs tacs = List.fold_right (fun t (tacs, ids) ->
      let t, ids' = cook t in t::tacs, ids'@ids) tacs ([], [])
  and cook_tacs' tacs = let tacs, ids = Array.fold_right (fun t (tacs, ids) ->
      let t, ids' = cook t in t::tacs, ids'@ids) tacs ([], [])
    in  Array.of_list tacs, ids
  and cook_match mats = List.fold_right (fun m (mats, ids) ->
      let p, ids' = match m with
        | All t -> let t, ids = cook t in All t, ids
        | Pat (c, p, t) -> let t, ids = cook t in Pat (c, p, t), ids in
      m::mats, ids@ids') mats ([], [])
  and cook (tac : glob_tactic_expr) : glob_tactic_expr * Names.KerName.t list =
    match tac with
    | TacAtom CAst.{v} ->
      let v, ids = cook_atomic v in
      TacAtom (CAst.make v), ids
    | TacThen (t1, t2)  ->
      let t1, ids1 = cook t1 in
      let t2, ids2 = cook t2 in
      TacThen (t1, t2), ids1@ids2
    | TacDispatch tl ->
      let tl, ids = cook_tacs tl in
      TacDispatch tl, ids
    | TacExtendTac (tl1, t, tl2) ->
      let tl1, ids1 = cook_tacs' tl1 in
      let t, ids2 = cook t in
      let tl2, ids3 = cook_tacs' tl2 in
      TacExtendTac (tl1, t, tl2), ids1@ids2@ids3
    | TacThens (t1, tl) ->
      let t1, ids1 = cook t1 in
      let tl, ids2 = cook_tacs tl in
      TacThens (t1, tl), ids1@ids2
    | TacThens3parts (t1, tl1, t2, tl2) ->
      let t1, ids1 = cook t1 in
      let tl1, ids2 = cook_tacs' tl1 in
      let t2, ids3 = cook t2 in
      let tl2, ids4 = cook_tacs' tl2 in
      TacThens3parts (t1, tl1, t2, tl2), ids1@ids2@ids3@ids4
    | TacFirst ts ->
      let ts, ids = cook_tacs ts in
      TacFirst (ts), ids
    | TacComplete t ->
      let t, ids = cook t in
      TacComplete t, ids
    | TacSolve ts ->
      let ts, ids = cook_tacs ts in
      TacSolve ts, ids
    | TacTry t ->
      let t, ids = cook t in
      TacTry t, ids
    | TacOr (t1, t2) ->
      let t1, ids1 = cook t1 in
      let t2, ids2 = cook t2 in
      TacOr (t1, t2), ids1@ids2
    | TacOnce t ->
      let t, ids = cook t in
      TacOnce t, ids
    | TacExactlyOnce t ->
      let t, ids = cook t in
      TacExactlyOnce t, ids
    | TacIfThenCatch (t1, t2, t3) ->
      let t1, ids1 = cook t1 in
      let t2, ids2 = cook t2 in
      let t3, ids3 = cook t3 in
      TacIfThenCatch (t1, t2, t3), ids1@ids2@ids3
    | TacOrelse (t1, t2) ->
      let t1, ids1 = cook t1 in
      let t2, ids2 = cook t2 in
      TacOrelse (t1, t2), ids1@ids2
    | TacDo (n, t) ->
      let t, ids = cook t in
      TacDo (n, t), ids
    | TacTimeout (n, t) ->
      let t, ids = cook t in
      TacTimeout (n, t), ids
    | TacTime (s, t) ->
      let t, ids = cook t in
      TacTime (s, t), ids
    | TacRepeat t ->
      let t, ids = cook t in
      TacRepeat t, ids
    | TacProgress t ->
      let t, ids = cook t in
      TacProgress t, ids
    | TacShowHyps t ->
      let t, ids = cook t in
      TacShowHyps t, ids
    | TacAbstract (t, id) ->
      let t, ids = cook t in
      TacAbstract (t, id), ids
    | TacId _ -> tac, []
    | TacFail _ -> tac, []
    | TacInfo t ->
      let t, ids = cook t in
      TacInfo t, ids
    | TacLetIn (flg, ts, t) ->
      let t, ids1 = cook t in
      let lns, args = List.split ts in
      let args, ids2 = cook_args args in
      TacLetIn (flg, List.combine lns args, t), ids1@ids2
    | TacMatch (flg, t, ts) ->
      let ts, ids = cook_match ts in
      TacMatch (flg, t, ts), ids
    | TacMatchGoal (flg, d, ts) ->
      let ts, ids = cook_match ts in
      TacMatchGoal (flg, d, ts), ids
    | TacFun (args, t) ->
      let t, ids = cook t in
      TacFun (args, t), ids
    | TacArg CAst.{v} ->
      let v, ids = cook_arg v in
      TacArg (CAst.make v), ids
    | TacSelect (i, t) ->
      let t, ids = cook t in
      TacSelect (i, t), ids
    | TacML CAst.{v=(e, args)} ->
      let args, ids = cook_args args in
      TacML (CAst.make (e, args)), ids
    | TacAlias CAst.{v=(id, args)} ->
      let args, ids = cook_args args in
      if Tacenv.check_alias id then TacAlias (CAst.make (id, args)), ids else
        let lid = CAst.make (Names.(Label.to_id (KerName.label id))) in
        TacArg (CAst.make (TacCall (CAst.make (ArgVar lid, args)))), id::ids
  in cook tac

let tactic_traversable t =
  try
    ignore (cook t); true
  with Witness_whitelist.UnknownWitnessError wit ->
    false

let warnProblem tacstr =
  Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                            str "the following tactic. Please report. " ++ tacstr))

let discharge env tac =
  if tactic_traversable tac then tac else
    let tacstr = Pptactic.pr_glob_tactic env tac in
    warnProblem tacstr;
    TacArg (CAst.make (TacGeneric (in_gen (glbwit wit_pr_arg) (PrString (Pp.string_of_ppcmds tacstr)))))

let rebuild tac =
  match tac with
  | TacArg (CAst.{v = TacGeneric (GenArg _ as g)}) when has_type g (Glbwit wit_pr_arg) ->
    let PrString str = out_gen (glbwit wit_pr_arg) g in
    (try
      let raw = Pcoq.parse_string Pltac.tactic str in
      let ist = Tacintern.make_empty_glob_sign () in
      Tacintern.intern_tactic_or_tacarg ist raw, true, []
    with e ->
      warnProblem (Pp.str str); TacId [], false, [])
  | _ ->
    try
      let tac, ls = cook tac in tac, false, ls
    with Witness_whitelist.UnknownWitnessError wit ->
      (* An exception can only occur if `tactic_traversable` is false,
         which means that `discharge` would have printed. Therefore,
         it must be the case that `discharge` was never executed
         (due to no Ltac's being defined in the section) *)
      (* We can raise a warning about missing witnesses though *)
      let tacstr = Pptactic.pr_glob_tactic (Global.env ()) tac in
      warnProblem tacstr;
      tac, false, []
