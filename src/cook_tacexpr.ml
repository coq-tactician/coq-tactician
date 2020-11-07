open Ltac_plugin
open Tacexpr
open Locus
open Util
open Geninterp
open Genarg
open Gendischarge

module OList = List
open DischargeMonad

let correct_kername id =
  try
    let _ = Tacenv.interp_ltac id in return (ArgArg (None, id))
  with Not_found ->
    let kername_tolname id = CAst.make (Names.(Label.to_id (KerName.label id))) in
    let* _ = log id in
    return (ArgVar (kername_tolname id))

let discharge_genarg_tactic s
    ((GenArg (Glbwit wit, _)) as g : glevel generic_argument)
  : glevel generic_argument discharged =
  let rec aux ((GenArg (Glbwit wit, _)) as g) = match wit with
    | ListArg wit as witl ->
      let ls = out_gen (Glbwit witl) g in
      let+ ls = List.map (fun x ->
          let+ res = aux (in_gen (Glbwit wit) x)
          in out_gen (Glbwit wit) res) ls in
      in_gen (Glbwit witl) ls
    | OptArg wit as wito ->
      let e = out_gen (Glbwit wito) g in
      let+ e = match e with
        | None -> return None
        | Some e -> let+ e = aux (in_gen (Glbwit wit) e) in
          Some (out_gen (Glbwit wit) e) in
      in_gen (Glbwit wito) e
    | PairArg (wit1, wit2) as witp ->
      let e1, e2 = out_gen (Glbwit witp) g in
      let+ e1 = aux (in_gen (Glbwit wit1) e1)
      and+ e2 = aux (in_gen (Glbwit wit2) e2) in
      let e1 = out_gen (Glbwit wit1) e1 in
      let e2 = out_gen (Glbwit wit2) e2 in
      in_gen (Glbwit witp) (e1, e2)
    | ExtraArg _ -> generic_discharge s g
  in aux g

let cook s (tac : glob_tactic_expr) : glob_tactic_expr discharged =
  let rec cook_atomic a =
    match a with
    | TacAssert (flg, b, by, pat, term) ->
      let+ by = match by with
        | None -> return None
        | Some by -> match by with
          | None -> return (Some None)
          | Some by -> let+ by = cook by in
            Some (Some by) in
      TacAssert (flg, b, by, pat, term)
    | TacRewrite (flg1, ts, i, d) ->
      let+ d = match d with
        | None -> return None
        | Some d -> let+ d = cook d in Some d in
      TacRewrite (flg1, ts, i, d)
    | _ -> return a
  and cook_args args = List.map cook_arg args
  and cook_arg x =
    match x with
    | TacGeneric g ->
      let+ g = discharge_genarg_tactic s g in
      TacGeneric g
    | Reference (ArgArg (_, id)) ->
      let* id = correct_kername id in
      return (Reference id)
    | TacCall CAst.{v=(id, args); _} ->
      let* id = match id with
        | Locus.ArgArg (_, id) -> correct_kername id
        | Locus.ArgVar _ -> return id in
      let* args = cook_args args in
      return (TacCall (CAst.make (id, args)))
    | Tacexp t -> let* t = cook t in return (Tacexp t)
    | _ -> return x
  and cook_tacs (tacs : glob_tactic_expr list) : glob_tactic_expr list discharged =
    List.map cook tacs
  and cook_tacs' tacs =
    map Array.of_list (List.map cook (Array.to_list tacs))
  and cook_match mats = List.map (function
        | All t -> let+ t = cook t in All t
        | Pat (c, p, t) -> let+ t = cook t in Pat (c, p, t)) mats
  and cook (tac : glob_tactic_expr) : glob_tactic_expr discharged =
    match tac with
    | TacAtom CAst.{v; _} ->
      let+ v = cook_atomic v in
      TacAtom (CAst.make v)
    | TacThen (t1, t2)  ->
      let+ t1 = cook t1
      and+ t2 = cook t2 in
      TacThen (t1, t2)
    | TacDispatch tl ->
      let+ tl = cook_tacs tl in
      TacDispatch tl
    | TacExtendTac (tl1, t, tl2) ->
      let+ tl1 = cook_tacs' tl1
      and+ t   = cook t
      and+ tl2 = cook_tacs' tl2 in
      TacExtendTac (tl1, t, tl2)
    | TacThens (t1, tl) ->
      let+ t1 = cook t1
      and+ tl = cook_tacs tl in
      TacThens (t1, tl)
    | TacThens3parts (t1, tl1, t2, tl2) ->
      let+ t1 = cook t1
      and+ tl1 = cook_tacs' tl1
      and+ t2 = cook t2
      and+ tl2 = cook_tacs' tl2 in
      TacThens3parts (t1, tl1, t2, tl2)
    | TacFirst ts ->
      let+ ts = cook_tacs ts in
      TacFirst (ts)
    | TacComplete t ->
      let+ t = cook t in
      TacComplete t
    | TacSolve ts ->
      let+ ts = cook_tacs ts in
      TacSolve ts
    | TacTry t ->
      let+ t = cook t in
      TacTry t
    | TacOr (t1, t2) ->
      let+ t1 = cook t1
      and+ t2 = cook t2 in
      TacOr (t1, t2)
    | TacOnce t ->
      let+ t = cook t in
      TacOnce t
    | TacExactlyOnce t ->
      let+ t = cook t in
      TacExactlyOnce t
    | TacIfThenCatch (t1, t2, t3) ->
      let+ t1 = cook t1
      and+ t2 = cook t2
      and+ t3 = cook t3 in
      TacIfThenCatch (t1, t2, t3)
    | TacOrelse (t1, t2) ->
      let+ t1 = cook t1
      and+ t2 = cook t2 in
      TacOrelse (t1, t2)
    | TacDo (n, t) ->
      let+ t = cook t in
      TacDo (n, t)
    | TacTimeout (n, t) ->
      let+ t = cook t in
      TacTimeout (n, t)
    | TacTime (s, t) ->
      let+ t = cook t in
      TacTime (s, t)
    | TacRepeat t ->
      let+ t = cook t in
      TacRepeat t
    | TacProgress t ->
      let+ t = cook t in
      TacProgress t
    | TacShowHyps t ->
      let+ t = cook t in
      TacShowHyps t
    | TacAbstract (t, id) ->
      let t, ids = cook t in
      TacAbstract (t, id), ids
    | TacId _ -> return tac
    | TacFail _ -> return tac
    | TacInfo t ->
      let+ t = cook t in
      TacInfo t
    | TacLetIn (flg, ts, t) ->
      let lns, args = OList.split ts in
      let+ t = cook t
      and+ args = cook_args args in
      TacLetIn (flg, OList.combine lns args, t)
    | TacMatch (flg, t, ts) ->
      let+ ts = cook_match ts in
      TacMatch (flg, t, ts)
    | TacMatchGoal (flg, d, ts) ->
      let+ ts = cook_match ts in
      TacMatchGoal (flg, d, ts)
    | TacFun (args, t) ->
      let+ t = cook t in
      TacFun (args, t)
    | TacArg CAst.{v; _} ->
      let+ v = cook_arg v in
      TacArg (CAst.make v)
    | TacSelect (i, t) ->
      let+ t = cook t in
      TacSelect (i, t)
    | TacML CAst.{v=(e, args); _} ->
      let+ args = cook_args args in
      TacML (CAst.make (e, args))
    | TacAlias CAst.{v=(id, args); _} ->
      let+ args = cook_args args in
      if Tacenv.check_alias id then TacAlias (CAst.make (id, args)) else
        let lid = CAst.make (Names.(Label.to_id (KerName.label id))) in
        TacArg (CAst.make (TacCall (CAst.make (ArgVar lid, args))))
  in cook tac

(* TODO: This is a huge hack *)

type pr_string = PrString of string
let wit_pr_arg : (Empty.t, pr_string, Empty.t) Genarg.genarg_type =
  let wit = Genarg.create_arg "pr_arg" in
  let () = register_val0 wit None in
  wit

let tactic_traversable t =
  try
    ignore (cook Names.KNset.empty t); true
  with UnknownWitnessError wit ->
    Feedback.msg_warning (pr_argument_type wit);
    false

let warnProblem tacstr =
  Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                            str "the following tactic. Please report. " ++ tacstr))

let discharge env tac =
  if tactic_traversable tac then tac else
    let tacstr = Pptactic.pr_glob_tactic env tac in
    warnProblem tacstr;
    TacArg (CAst.make (TacGeneric (in_gen (glbwit wit_pr_arg) (PrString (Pp.string_of_ppcmds tacstr)))))

let rebuild s tac =
  match tac with
  | TacArg (CAst.{v = TacGeneric (GenArg _ as g); _}) when has_type g (Glbwit wit_pr_arg) ->
    let PrString str = out_gen (glbwit wit_pr_arg) g in
    (try
      let raw = Pcoq.parse_string Pltac.tactic str in
      let ist = Tacintern.make_empty_glob_sign () in
      Tacintern.intern_tactic_or_tacarg ist raw, true, Names.KNset.empty
     with e ->
       Feedback.msg_warning (Pp.str (Printexc.to_string e));
       warnProblem (Pp.str str); TacId [], false, Names.KNset.empty)
  | _ ->
    try
      let tac, ls = cook s tac in tac, false, ls
    with UnknownWitnessError wit ->
      (* An exception can only occur if `tactic_traversable` is false,
         which means that `discharge` would have printed. Therefore,
         it must be the case that `discharge` was never executed
         (due to no Ltac's being defined in the section) *)
      (* We can raise a warning about missing witnesses though *)
      Feedback.msg_warning (pr_argument_type wit);
      let tacstr = Pptactic.pr_glob_tactic (Global.env ()) tac in
      warnProblem tacstr;
      tac, false, Names.KNset.empty
