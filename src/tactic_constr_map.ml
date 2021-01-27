open Ltac_plugin
open Tacexpr
open Tactypes
open Constrexpr
open Glob_term
open Locus
open Tactics
open Context
open Genredexpr
open Pattern_ops
open Util
open Names
open Nameops
open Glob_ops
open CAst

(* Begin taken and modified from Glob_ops.v *)
let collide_id l id = List.exists (fun (id',id'') -> Id.equal id id' || Id.equal id id'') l
let test_id l id = if collide_id l id then raise UnsoundRenaming
let test_na l na = Name.iter (test_id l) na
let update_subst na l =
  let in_range id l = List.exists (fun (_,id') -> Id.equal id id') l in
  let l' = Name.fold_right Id.List.remove_assoc na l in
  Name.fold_right
    (fun id _ ->
       if in_range id l' then
         let id' = Namegen.next_ident_away_from id (fun id' -> in_range id' l') in
         Name id', (id,id')::l
       else na,l)
    na (na,l)
let rename_var l id =
  try
    Id.List.assoc id l
  with Not_found ->
    id
let force c = DAst.make ?loc:c.CAst.loc (DAst.get c)
let rec rename_glob_vars l c = force @@ DAst.map_with_loc (fun ?loc -> function
  | GVar id as r ->
      let id' = rename_var l id in
      if id == id' then r else GVar id'
  | GRef (GlobRef.VarRef id,_) as r -> r
  | GProd (na,bk,t,c) ->
      let na',l' = update_subst na l in
      GProd (na',bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLambda (na,bk,t,c) ->
      let na',l' = update_subst na l in
      GLambda (na',bk,rename_glob_vars l t,rename_glob_vars l' c)
  | GLetIn (na,b,t,c) ->
      let na',l' = update_subst na l in
      GLetIn (na',rename_glob_vars l b,Option.map (rename_glob_vars l) t,rename_glob_vars l' c)
  (* Lazy strategy: we fail if a collision with renaming occurs, rather than renaming further *)
  | GCases (ci,po,tomatchl,cls) ->
      let test_pred_pat (na,ino) =
        test_na l na; Option.iter (fun {v=(_,nal); _} -> List.iter (test_na l) nal) ino in
      let test_clause idl = List.iter (test_id l) idl in
      let po = Option.map (rename_glob_vars l) po in
      let tomatchl = Util.List.map_left (fun (tm,x) -> test_pred_pat x; (rename_glob_vars l tm,x)) tomatchl in
      let cls = Util.List.map_left (CAst.map (fun (idl,p,c) -> test_clause idl; (idl,p,rename_glob_vars l c))) cls in
      GCases (ci,po,tomatchl,cls)
  | GLetTuple (nal,(na,po),c,b) ->
     List.iter (test_na l) (na::nal);
     GLetTuple (nal,(na,Option.map (rename_glob_vars l) po),
                rename_glob_vars l c,rename_glob_vars l b)
  | GIf (c,(na,po),b1,b2) ->
     test_na l na;
     GIf (rename_glob_vars l c,(na,Option.map (rename_glob_vars l) po),
          rename_glob_vars l b1,rename_glob_vars l b2)
  | GRec (k,idl,decls,bs,ts) ->
     Array.iter (test_id l) idl;
     GRec (k,idl,
           Array.map (List.map (fun (na,k,bbd,bty) ->
             test_na l na; (na,k,Option.map (rename_glob_vars l) bbd,rename_glob_vars l bty))) decls,
           Array.map (rename_glob_vars l) bs,
           Array.map (rename_glob_vars l) ts)
  | _ -> DAst.get (map_glob_constr (rename_glob_vars l) c)
  ) c
(* End taken and modified from Glob_ops.v *)

let context_to_vars lc = List.map (function
    | Named.Declaration.LocalAssum (id, _) -> id.binder_name
    | Named.Declaration.LocalDef (id,_, _) -> id.binder_name) lc

let hd_default ls x = match ls with
  | [] -> x
  | x::_ -> x

let find_in_lc x lc_vars =
  Option.default (hd_default lc_vars (Names.Id.of_string "_"))
    (List.find_opt (fun y -> Names.Id.equal x y) lc_vars)

let replace_free_variables (lc : EConstr.named_context) t =
  let free = Names.Id.Set.elements (Glob_ops.free_glob_vars t) in
  (*print_endline "free";
    List.iter (fun id -> print_endline (Names.Id.to_string id)) free;*)
  let lc_vars = context_to_vars lc in
  let map = List.map (fun x -> (x, find_in_lc x lc_vars)) free in
  rename_glob_vars map t

let replace_pattern_free_variables (lc : EConstr.named_context) p =
  let free = Names.Id.Set.elements (pattern_free_vars p) in
  print_endline "free2";
    List.iter (fun id -> print_endline (Names.Id.to_string id)) free;
  let lc_vars = context_to_vars lc in
  let map = List.map (fun x -> (x, find_in_lc x lc_vars)) free in
  pattern_rename_vars map p

let id_map f id =
  let lc_vars = context_to_vars f in
  find_in_lc id lc_vars

let id_map2 f id = CAst.map (id_map f) id

let constr_and_expr_map f ((glb_constr : glob_constr), (constr_expr : constr_expr option)) : glob_constr * Constrexpr.constr_expr option =
  (replace_free_variables f glb_constr, None)

let binding_map f =
  CAst.map (fun (b,c) ->
      b, constr_and_expr_map f c)

let bindings_map f = function
  | NoBindings -> NoBindings
  | ImplicitBindings l -> ImplicitBindings (List.map (constr_and_expr_map f) l)
  | ExplicitBindings l -> ExplicitBindings (List.map (binding_map f) l)

let with_bindings_map f (c, bl) = (constr_and_expr_map f c, bindings_map f bl)
let with_bindings_arg_map f ((clear, c) : g_trm with_bindings_arg) : g_trm with_bindings_arg =
  (clear, with_bindings_map f c)

let intro_pattern_naming_map f p = p (* TODO: anonymize this if possible *)
let new_name_map f id = id (* TODO: anonymize this if possible *)

let rec intro_pattern_action_map f = function
  | IntroWildcard -> IntroWildcard
  | IntroOrAndPattern p -> IntroOrAndPattern (intro_pattern_orand_map f p)
  | IntroInjection p -> IntroInjection (List.map (CAst.map (intro_pattern_map f)) p)
  | IntroApplyOn (c, p) ->
    IntroApplyOn (CAst.map (constr_and_expr_map f) c, CAst.map (intro_pattern_map f) p)
  | IntroRewrite b -> IntroRewrite b
and intro_pattern_orand_map f = function
    IntroOrPattern ls -> IntroOrPattern (List.map (List.map (CAst.map (intro_pattern_map f))) ls)
  | IntroAndPattern ls -> IntroAndPattern (List.map (CAst.map (intro_pattern_map f)) ls)
and intro_pattern_map f = function
  | IntroForthcoming b -> IntroForthcoming b
  | IntroNaming p -> IntroNaming (intro_pattern_naming_map f p)
  | IntroAction p -> IntroAction (intro_pattern_action_map f p)

let apply_in_map f (id, pattern) = (id_map2 f id, Option.map (CAst.map (intro_pattern_map f)) pattern)

let with_occurrences_map f (o, c) = (o, constr_and_expr_map f c)

let or_var_map f = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar x -> ArgVar x

let quantified_hypothesis_map f = function
  | AnonHyp n -> AnonHyp n
  | NamedHyp x -> NamedHyp (id_map f x)

let core_destruction_arg_map f = function
  | Tactics.ElimOnConstr (gc, ce) -> ElimOnConstr (constr_and_expr_map f gc, ce)
  | Tactics.ElimOnIdent id -> ElimOnIdent (CAst.map (id_map f) id)
  | Tactics.ElimOnAnonHyp n -> ElimOnAnonHyp n

let induction_clause_map f (((cflg, da), (eqn, p), ce) : ('k, 'i) induction_clause) =
  ((cflg, core_destruction_arg_map f da),
   (Option.map (CAst.map (intro_pattern_naming_map f)) eqn,
    Option.map (or_var_map (CAst.map (intro_pattern_orand_map f))) p), ce)

let g_pat_map f (id, c, p) = (Names.Id.Set.map (id_map f) id, constr_and_expr_map f c, replace_pattern_free_variables f p) (* TODO: What to do with 'p' (Pattern.constr_pattern)*)

let clause_expr_map f { onhyps = oh; concl_occs = oe } =
  {onhyps = Option.map (List.map (fun ((o, id), l) -> ((o, id_map2 f id), l))) oh; concl_occs = oe}

let inversion_strength_map f = function
    NonDepInversion (k, ids, p) -> NonDepInversion (k, List.map (id_map2 f) ids, Option.map (or_var_map (CAst.map (intro_pattern_orand_map f))) p)
  | DepInversion (k, c, p) -> DepInversion (k, Option.map (constr_and_expr_map f) c, Option.map (or_var_map (CAst.map (intro_pattern_orand_map f))) p)
  | InversionUsing (c, ids) -> InversionUsing (constr_and_expr_map f c, List.map (id_map2 f) ids)

let match_pattern_map f = function
  | Term x -> Term (g_pat_map f x)
  | Subterm (id, x) -> Subterm (id, g_pat_map f x)

let match_context_hyps_map f = function
  | Hyp (id, p) -> Hyp (id, match_pattern_map f p)
  | Def (id, p1, p2) -> Def (id, match_pattern_map f p1, match_pattern_map f p2)

let match_rule_map f re (x : (Ltac_plugin.Tacexpr.g_pat,
 Ltac_plugin.Tacexpr.g_dispatch Ltac_plugin.Tacexpr.gen_tactic_expr)
Ltac_plugin.Tacexpr.match_rule) = match x with
  | Pat (x, y, z) -> Pat (List.map (match_context_hyps_map f) x, match_pattern_map f y, re z)
  | All x -> All (re x)

let may_eval_map f (x: (Ltac_plugin.Tacexpr.g_trm, Ltac_plugin.Tacexpr.g_cst,
 Ltac_plugin.Tacexpr.g_pat)
                        Genredexpr.may_eval) = match x with
  | ConstrTerm x -> ConstrTerm (constr_and_expr_map f x)
  | ConstrEval (r, c) -> ConstrEval (r, (constr_and_expr_map f c)) (* TODO: r should be mapped here, too much effort*)
  | ConstrContext (id, c) -> ConstrContext (id, constr_and_expr_map f c)
  | ConstrTypeOf c -> ConstrTypeOf (constr_and_expr_map f c)

let rec tacarg_map f re (a : Ltac_plugin.Tacexpr.g_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg) : Ltac_plugin.Tacexpr.g_dispatch Ltac_plugin.Tacexpr.gen_tactic_arg = match a with
  | TacGeneric a -> TacGeneric a (* TODO: Can we do something here? *)
  | ConstrMayEval c -> ConstrMayEval (may_eval_map f c)
  | Reference x -> Reference x
  | TacCall x -> TacCall (CAst.map (fun (x, y) -> (x, List.map (tacarg_map f re) y)) x)
  | TacFreshId ls -> TacFreshId ls
  | Tacexp t -> Tacexp (re t)
  | TacPretype t -> TacPretype (constr_and_expr_map f t)
  | TacNumgoals -> TacNumgoals

let rec atomic_map (f : EConstr.named_context) (t : glob_atomic_tactic_expr) : glob_atomic_tactic_expr =
  match t with
  | TacIntroPattern (ev, l) -> TacIntroPattern (ev, List.map (CAst.map (intro_pattern_map f)) l)
  | TacApply (a, ev, cb, cl) ->
    TacApply (a, ev, List.map (with_bindings_arg_map f) cb, Option.map (apply_in_map f) cl)
  | TacElim (ev, cb, cbo) -> TacElim (ev, with_bindings_arg_map f cb, Option.map (with_bindings_map f) cbo)
  | TacCase (ev, cb) -> TacCase (ev, with_bindings_arg_map f cb)
  | TacMutualFix (id, n, l) -> TacMutualFix (id, n, List.map (fun (id, n, t) -> (id, n, constr_and_expr_map f t)) l)
  | TacMutualCofix (id, l) -> TacMutualCofix (id, List.map (fun (id, t) -> (id, constr_and_expr_map f t)) l)
  | TacAssert (ev, b, otac, na, c) -> TacAssert (ev, b, Option.map (Option.map (tactic_constr_map f)) otac,
                                                 Option.map (CAst.map (intro_pattern_map f)) na,
                                                 constr_and_expr_map f c)
  | TacGeneralize cl -> TacGeneralize (List.map (fun (wo, id) -> (with_occurrences_map f wo, new_name_map f id)) cl)
  | TacLetTac (ev, id, c, clp, b, eqpat) -> TacLetTac (ev, id, constr_and_expr_map f c, clause_expr_map f clp, b,
                                                       Option.map (CAst.map (intro_pattern_naming_map f )) eqpat)
  | TacInductionDestruct (isrec, ev, (l, el)) ->
    TacInductionDestruct (isrec, ev, (List.map (induction_clause_map f) l, Option.map (with_bindings_map f) el))
  | TacReduce (r, cl) -> TacReduce (r, clause_expr_map f cl) (* TODO: r should be mapped here, but too much effort *)
  | TacChange (check, op, c, cl) -> TacChange (check, Option.map (g_pat_map f) op, constr_and_expr_map f c,
                                               clause_expr_map f cl)
  | TacRewrite (ev, l, cl, by) ->
    TacRewrite (ev, List.map (fun (b, eq, x) -> (b, eq, with_bindings_arg_map f x)) l,
                clause_expr_map f cl, Option.map (tactic_constr_map f) by)
  | TacInversion (a, b) -> TacInversion (inversion_strength_map f a, quantified_hypothesis_map f b)

and tactic_constr_map (f : EConstr.named_context) (tac : glob_tactic_expr) : glob_tactic_expr =
  match tac with
  | TacAtom { CAst.v= t ; _ } -> TacAtom (CAst.make @@ atomic_map f t)
  | TacFun (ids, t) -> TacFun (ids, tactic_constr_map f t)
  | TacLetIn (r, l, u) -> TacLetIn (r, List.map (fun (id, t) -> (id, t)) l, tactic_constr_map f u)
  | TacMatchGoal (lz, lr, lmr) -> TacMatchGoal (lz, lr, List.map (match_rule_map f (tactic_constr_map f)) lmr)
  | TacMatch (lz, c, lmr) ->
    TacMatch (lz, tactic_constr_map f c, List.map (match_rule_map f (tactic_constr_map f)) lmr)
  | TacId ls -> TacId ls
  | TacFail (flg, n, ls) -> TacFail (flg, n, ls)
  | TacProgress tac -> TacProgress (tactic_constr_map f tac)
  | TacShowHyps tac -> TacShowHyps (tactic_constr_map f tac)
  | TacAbstract (tac, s) -> TacAbstract (tactic_constr_map f tac, s)
  | TacThen (t1, t2) -> TacThen (tactic_constr_map f t1, tactic_constr_map f t2)
  | TacDispatch tl -> TacDispatch (List.map (tactic_constr_map f) tl)
  | TacExtendTac (tf, t, tl) -> TacExtendTac (Array.map (tactic_constr_map f) tf, tactic_constr_map f t,
                                              Array.map (tactic_constr_map f) tl)
  | TacThens (t, tl) -> TacThens (tactic_constr_map f t, List.map (tactic_constr_map f) tl)
  | TacThens3parts (t1, tf, t2, tl) -> TacThens3parts (tactic_constr_map f t1, Array.map (tactic_constr_map f) tf,
                                                       tactic_constr_map f t2, Array.map (tactic_constr_map f) tl)
  | TacDo (n, tac) -> TacDo (n, tactic_constr_map f tac)
  | TacTimeout (n, tac) -> TacTimeout (n, tactic_constr_map f tac)
  | TacTime (s, tac) -> TacTime (s, tactic_constr_map f tac)
  | TacTry tac -> TacTry (tactic_constr_map f tac)
  | TacInfo tac -> TacInfo (tactic_constr_map f tac)
  | TacRepeat tac -> TacRepeat (tactic_constr_map f tac)
  | TacOr (t1, t2) -> TacOr (tactic_constr_map f t1, tactic_constr_map f t2)
  | TacOnce tac -> TacOnce (tactic_constr_map f tac)
  | TacExactlyOnce tac -> TacExactlyOnce (tactic_constr_map f tac)
  | TacIfThenCatch (tac, tact, tace) -> TacIfThenCatch (tactic_constr_map f tac, tactic_constr_map f tact,
                                                        tactic_constr_map f tace)
  | TacOrelse (t1, t2) -> TacOrelse (tactic_constr_map f t1, tactic_constr_map f t2)
  | TacFirst l -> TacFirst (List.map (tactic_constr_map f) l)
  | TacSolve l -> TacSolve (List.map (tactic_constr_map f) l)
  | TacComplete tac -> TacComplete (tactic_constr_map f tac)
  | TacArg a -> TacArg (CAst.map (tacarg_map f (tactic_constr_map f)) a)
  | TacSelect (s, tac) -> TacSelect (s, tactic_constr_map f tac)
  | TacAlias x -> TacAlias (CAst.map (fun (id, args) -> (id, List.map (tacarg_map f (tactic_constr_map f)) args)) x)
  | TacML x -> TacML (CAst.map (fun (id, args) -> (id, List.map (tacarg_map f (tactic_constr_map f)) args)) x)
