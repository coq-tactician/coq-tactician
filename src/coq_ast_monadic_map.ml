open Ltac_plugin
open Tacexpr
open Tactypes
open Tacexpr_functor
open Glob_term_functor
open Constrexpr_functor
open Pattern_functor
open Locus
open Tactics
open Genredexpr
open Genarg
open Monad_util

module O = Glob_term
module J = Constrexpr

module Mapper (M: Monad.Def) = struct
  include WithMonadNotations(M)
  open Monad.Make(M)

  let array_map f xs = let+ xs = List.map f (Array.to_list xs) in Array.of_list xs
  let option_map f = function
    | None -> return None
    | Some x -> let+ x = f x in Some x

  let cast_map f CAst.{loc; v} =
    let+ v = f v in
    CAst.make ?loc v

  let thunk_map f x =
    let+ v = f (DAst.get_thunk x) in
    DAst.Value v

  let dast_map f x = cast_map (thunk_map f) x

  let or_var_map f = function
    | ArgArg x ->
      let+ x = f x in
      ArgArg x
    | ArgVar id -> return @@ ArgVar id

  let union_map f g = function
    | Util.Inl x ->
      let+ x = f x in
      Util.Inl x
    | Util.Inr x ->
      let+ x =  g x in
      Util.Inr x

  let intro_pattern_expr_map m = function
    | IntroForthcoming b -> return @@ IntroForthcoming b
    | IntroNaming ng -> return @@ IntroNaming ng
    | IntroAction a ->
      let+ a  = m#intro_pattern_action_expr a in
      IntroAction a

  let intro_pattern_action_expr_map m = function
    | IntroWildcard -> return @@ IntroWildcard
    | IntroOrAndPattern oap ->
      let+ oap = m#or_and_intro_pattern_expr oap in
      IntroOrAndPattern oap
    | IntroInjection ls ->
      let+ ls = List.map (cast_map m#intro_pattern_expr) ls in
      IntroInjection ls
    | IntroApplyOn (cstr, pat) ->
      let+ cstr = cast_map m#constr cstr
      and+ pat = cast_map m#intro_pattern_expr pat in
      IntroApplyOn (cstr, pat)
    | IntroRewrite d -> return @@ IntroRewrite d

  let or_and_intro_pattern_expr_map m = function
    | IntroOrPattern pats ->
      let+ pats = List.map (List.map (cast_map m#intro_pattern_expr)) pats in
      IntroOrPattern pats
    | IntroAndPattern pats ->
      let+ pats = List.map (cast_map m#intro_pattern_expr) pats in
      IntroAndPattern pats

  let explicit_bindings_map f bndgs =
    List.map (cast_map (fun (qh, x) ->
        let+ x =  f x in
        qh, x)) bndgs

  let bindings_map f = function
    | ImplicitBindings xs ->
      let+ xs = List.map f xs in
      ImplicitBindings xs
    | ExplicitBindings bndgs ->
      let+ bndgs = explicit_bindings_map f bndgs in
      ExplicitBindings bndgs
    | NoBindings -> return @@ NoBindings

  let with_bindings_map f (x, bndgs) =
    let+ x =  f x
    and+ bndgs = bindings_map f bndgs in
    (x, bndgs)

  let with_bindings_arg_map f (cf, bndgs) =
    let+ bndgs = with_bindings_map f bndgs in
    (cf, bndgs)

  let occurrences_gen_map f = function
    | AllOccurrences -> return AllOccurrences
    | AtLeastOneOccurrence -> return AtLeastOneOccurrence
    | AllOccurrencesBut ls ->
      let+ ls = List.map f ls in
      AllOccurrencesBut ls
    | NoOccurrences -> return NoOccurrences
    | OnlyOccurrences ls ->
      let+ ls = List.map f ls in
      OnlyOccurrences ls

  let occurrences_expr_map oe = occurrences_gen_map (or_var_map (fun x -> x)) oe

  let with_occurrences_map f (oe, x) =
    let+ x = f x in
    (oe, x)

  let hyp_location_expr_map f (x, hf) =
    let+ x = with_occurrences_map f x in
    (x, hf)

  let clause_expr_map f { onhyps; concl_occs } =
    let+ onhyps = option_map (List.map (hyp_location_expr_map f)) onhyps in
    { onhyps; concl_occs }

  let core_destruction_arg_map f = function
    | ElimOnConstr x ->
      let+ x = f x in
      ElimOnConstr x
    | ElimOnIdent id -> return @@ ElimOnIdent id
    | ElimOnAnonHyp i -> return @@ ElimOnAnonHyp i

  let destruction_arg_map f (cf, da) =
    let+ da = core_destruction_arg_map f da in
    (cf, da)

  let induction_clause_map f g m ((da, (eqn, pat), ce) : 'a induction_clause) =
    let+ da = destruction_arg_map (with_bindings_map f) da
    and+ pat = option_map (or_var_map (cast_map m#or_and_intro_pattern_expr)) pat
    and+ ce = option_map (clause_expr_map g) ce in
    (da, (eqn, pat), ce)

  let induction_clause_list_map f g h m ((ics, using) : 'a induction_clause_list) =
    let+ ics = List.map (induction_clause_map g h m) ics
    and+ using = option_map (with_bindings_map f) using in
    (ics, using)

  let glob_red_flag_map f ({ rConst; _ } as flg) =
    let+ rConst = List.map f rConst in
    { flg with rConst }

  let red_expr_gen_map f g h = function
    | Red b -> return @@ Red b
    | Hnf -> return @@ Hnf
    | Simpl (gf, occ) ->
      let+ gf = glob_red_flag_map g gf
      and+ occ = option_map (with_occurrences_map (union_map g h)) occ in
      Simpl (gf, occ)
    | Cbv gf ->
      let+ gf = glob_red_flag_map g gf in
      Cbv gf
    | Cbn gf ->
      let+ gf = glob_red_flag_map g gf in
      Cbn gf
    | Lazy gf ->
      let+ gf = glob_red_flag_map g gf in
      Lazy gf
    | Unfold ls ->
      let+ ls = List.map (with_occurrences_map g) ls in
      Unfold ls
    | Fold ls ->
      let+ ls = List.map f ls in
      Fold ls
    | Pattern ls ->
      let+ ls = List.map (with_occurrences_map f) ls in
      Pattern ls
    | ExtraRedExpr str -> return @@ ExtraRedExpr str
    | CbvVm occ ->
      let+ occ = option_map (with_occurrences_map (union_map g h)) occ in
      CbvVm occ
    | CbvNative occ ->
      let+ occ = option_map (with_occurrences_map (union_map g h)) occ in
      CbvNative occ

  let inversion_strength_map f h m = function
    | NonDepInversion (ik, ids, pat) ->
      let+ ids = List.map h ids
      and+ pat = option_map (or_var_map (cast_map m#or_and_intro_pattern_expr)) pat in
      NonDepInversion (ik, ids, pat)
    | DepInversion (ik, id, pat) ->
      let+ id = option_map f id
      and+ pat = option_map (or_var_map (cast_map m#or_and_intro_pattern_expr)) pat in
      DepInversion (ik, id, pat)
    | InversionUsing (c, ids) ->
      let+ c = f c
      and+ ids = List.map h ids in
      InversionUsing (c, ids)

  let gen_atomic_tactic_expr_map m (t : 'a gen_atomic_tactic_expr) =
    match t with
    | TacIntroPattern (ef, ip) ->
      let+ ip = List.map (cast_map m#intro_pattern_expr) ip in
      TacIntroPattern (ef, ip)
    | TacApply (af, ef, apps, pat) ->
      let+ apps = List.map (with_bindings_arg_map m#term) apps
      and+ pat = option_map (fun (id, pat) ->
          let+ id = m#name id
          and+ pat = option_map (cast_map m#intro_pattern_expr) pat in
          id, pat) pat in
      TacApply (af, ef, apps, pat)
    | TacElim (ef, trm, using) ->
      let+ trm = with_bindings_arg_map m#term trm
      and+ using = option_map (with_bindings_map m#term) using in
      TacElim (ef, trm, using)
    | TacCase (ef, trm) ->
      let+ trm = with_bindings_arg_map m#term trm in
      TacCase (ef, trm)
    | TacMutualFix (id, n, funs) ->
      let+ funs = List.map (fun (id, n, trm) ->
          let+ trm = m#term trm in
          id, n, trm) funs in
      TacMutualFix (id, n, funs)
    | TacMutualCofix (id, funs) ->
      let+ funs = List.map (fun (id, trm) ->
          let+ trm = m#term trm in
          id, trm) funs in
      TacMutualCofix (id, funs)
    | TacAssert (ef, flg, by, pat, trm) ->
      let+ by = option_map (option_map m#tacexpr) by
      and+ pat = option_map (cast_map m#intro_pattern_expr) pat
      and+ trm = m#term trm in
      TacAssert (ef, flg, by, pat, trm)
    | TacGeneralize trms ->
      let+ trms = List.map (fun (trm, id) ->
          let+ trm = with_occurrences_map m#term trm in
          trm, id) trms in
      TacGeneralize trms
    | TacLetTac (ef, id, trm, ce, lif, pat) ->
      let+ trm = m#term trm
      and+ ce = clause_expr_map m#name ce in
      TacLetTac (ef, id, trm, ce, lif, pat)
    | TacInductionDestruct (rf, ef, ics) ->
      let+ ics = induction_clause_list_map m#term m#dterm m#name m ics in
      TacInductionDestruct (rf, ef, ics)
    | TacReduce (red, id) ->
      let+ red = red_expr_gen_map m#term m#constant m#pattern red
      and+ id = clause_expr_map m#name id in
      TacReduce (red, id)
    | TacChange (cg, pat, trm, cls) ->
      let+ pat = option_map m#pattern pat
      and+ trm = m#dterm trm
      and+ cls = clause_expr_map m#name cls in
      TacChange (cg, pat, trm, cls)
    | TacRewrite (ef, rews, cls, by) ->
      let+ rews = List.map (fun (b, mult, trm) ->
          let+ trm = with_bindings_arg_map m#dterm trm in
          b, mult, trm) rews
      and+ cls = clause_expr_map m#name cls
      and+ by = option_map m#tacexpr by in
      TacRewrite (ef, rews, cls, by)
    | TacInversion (is, qh) ->
      let+ is = inversion_strength_map m#term m#name m is in
      TacInversion (is, qh)

  let may_eval_map f g h = function
    | ConstrTerm x ->
      let+ x = f x in
      ConstrTerm x
    | ConstrEval (red, x) ->
      let+ red = red_expr_gen_map f g h red
      and+ x = f x in
      ConstrEval (red, x)
    | ConstrContext (id, x) ->
      let+ x = f x in
      ConstrContext (id, x)
    | ConstrTypeOf x ->
      let+ x = f x in
      ConstrTypeOf x

  let gen_tactic_arg_map m (t : 'a gen_tactic_arg) =
    match t with
    | TacGeneric gen ->
      let+ gen = m#genarg gen in
      TacGeneric gen
    | ConstrMayEval me ->
      let+ me = may_eval_map m#term m#constant m#pattern me in
      ConstrMayEval me
    | Reference r ->
      let+ r = m#reference r in
      Reference r
    | TacCall c ->
      let+ c = cast_map (fun (r, args) ->
          let+ r = m#reference r
          and+ args = List.map m#tacarg args in
          r, args) c in
      TacCall c
    | TacFreshId id -> return @@ TacFreshId id
    | Tacexp t ->
      let+ t = m#tacexpr t in
      Tacexp t
    | TacPretype term ->
      let+ term = m#term term in
      TacPretype term
    | TacNumgoals -> return TacNumgoals

  let match_pattern_map f = function
    | Term x ->
      let+ x = f x in
      Term x
    | Subterm (id, x) ->
      let+ x = f x in
      Subterm (id, x)

  let match_context_hyps f = function
    | Hyp (id, pat) ->
      let+ pat = match_pattern_map f pat in
      Hyp (id, pat)
    | Def (id, pat1, pat2) ->
      let+ pat1 = match_pattern_map f pat1
      and+ pat2 = match_pattern_map f pat2 in
      Def (id, pat1, pat2)

  let match_rule_map f g = function
    | Pat (mch, mp, t) ->
      let+ mch = List.map (match_context_hyps f) mch
      and+ mp = match_pattern_map f mp
      and+ t = g t in
      Pat (mch, mp, t)
    | All t ->
      let+ t = g t in
      All t

  let message_token_map f = function
    | MsgString str -> return @@ MsgString str
    | MsgInt i -> return @@ MsgInt i
    | MsgIdent x ->
      let+ x = f x in
      MsgIdent x

  let gen_tactic_fun_ast_map f (ids, t) =
    let+ t = f t in
    ids, t

  let gen_tactic_expr_map m (t : 'a gen_tactic_expr) =
    let f = m#tacexpr in
    let lm = List.map f in
    let am = array_map f in
    match t with
    | TacAtom a ->
      let+ a = cast_map (gen_atomic_tactic_expr_map m) a in
      TacAtom a
    | TacThen (t1, t2) ->
      let+ t1 = f t1
      and+ t2 = f t2 in
      TacThen (t1, t2)
    | TacDispatch ts ->
      let+ ts = lm ts in
      TacDispatch ts
    | TacExtendTac (ts1, t, ts2) ->
      let+ ts1 = am ts1
      and+ t = f t
      and+ ts2 = am ts2 in
      TacExtendTac (ts1, t, ts2)
    | TacThens (t, ts) ->
      let+ t = f t
      and+ ts = lm ts in
      TacThens (t, ts)
    | TacThens3parts (t1, ts1, t2, ts2) ->
      let+ t1 = f t1
      and+ ts1 = am ts1
      and+ t2 = f t2
      and+ ts2 = am ts2 in
      TacThens3parts (t1, ts1, t2, ts2)
    | TacFirst ts ->
      let+ ts = lm ts in
      TacFirst ts
    | TacComplete t ->
      let+ t = f t in
      TacComplete t
    | TacSolve ts ->
      let+ ts = lm ts in
      TacSolve ts
    | TacTry t ->
      let+ t = f t in
      TacTry t
    | TacOr (t1, t2) ->
      let+ t1 = f t1
      and+ t2 = f t2 in
      TacOr (t1, t2)
    | TacOnce t ->
      let+ t = f t in
      TacOnce t
    | TacExactlyOnce t ->
      let+ t = f t in
      TacExactlyOnce t
    | TacIfThenCatch (t1, t2, t3) ->
      let+ t1 = f t1
      and+ t2 = f t2
      and+ t3 = f t3 in
      TacIfThenCatch (t1, t2, t3)
    | TacOrelse (t1, t2) ->
      let+ t1 = f t1
      and+ t2 = f t2 in
      TacOrelse (t1, t2)
    | TacDo (n, t) ->
      let+ t = f t in
      TacDo (n, t)
    | TacTimeout (n, t) ->
      let+ t = f t in
      TacTimeout (n, t)
    | TacTime (s, t) ->
      let+ t = f t in
      TacTime (s, t)
    | TacRepeat t ->
      let+ t = f t in
      TacRepeat t
    | TacProgress t ->
      let+ t = f t in
      TacProgress t
    | TacShowHyps t ->
      let+ t = f t in
      TacShowHyps t
    | TacAbstract (t, id) ->
      let+ t = f t in
      TacAbstract (t, id)
    | TacId ms ->
      let+ ms = List.map (message_token_map m#name) ms in
      TacId ms
    | TacFail (gf, l, ms) ->
      let+ ms = List.map (message_token_map m#name) ms in
      TacFail (gf, l, ms)
    | TacInfo t ->
      let+ t = f t in
      TacInfo t
    | TacLetIn (rc, args, body) ->
      let+ args = List.map (fun (id, arg) ->
          let+ arg = m#tacarg arg in
          id, arg) args
      and+ body = f body in
      TacLetIn (rc, args, body)
    | TacMatch (lf, t, mr) ->
      let+ t = f t
      and+ mr = List.map (match_rule_map m#pattern f) mr in
      TacMatch (lf, t, mr)
    | TacMatchGoal (lf, d, mr) ->
      let+ mr = List.map (match_rule_map m#pattern f) mr in
      TacMatchGoal (lf, d, mr)
    | TacFun ast ->
      let+ ast = gen_tactic_fun_ast_map f ast in
      TacFun ast
    | TacArg arg ->
      let+ arg = cast_map m#tacarg arg in
      TacArg arg
    | TacSelect (s, t) ->
      let+ t = f t in
      TacSelect (s, t)
    | TacML ml ->
      let+ ml = cast_map (fun (mle, args) ->
          let+ args = List.map m#tacarg args in
          mle, args) ml in
      TacML ml
    | TacAlias al ->
      let+ al = cast_map (fun (id, args) ->
          let+ args = List.map m#tacarg args in
          id, args) al in
      TacAlias al

  let tomatch_tuple_g_map m (c, pat) =
    let+ c = m#glob_constr_g c in
    c, pat

  let tomatch_tuples_g_map m = List.map (tomatch_tuple_g_map m)

  let cases_clause_g_map m cl =
    cast_map (fun (ids, pats, c) ->
        let+ pats = List.map m#cases_pattern_g pats
        and+ c = m#glob_constr_g c in
        ids, pats, c) cl

  let cases_clauses_g_map m = List.map (cases_clause_g_map m)

  let glob_decl_g_map m (id, bk, typ, term) =
    let+ typ = option_map m#glob_constr_g typ
    and+ term = m#glob_constr_g term in
    (id, bk, typ, term)

  let cases_pattern_r_map m = function
    | PatVar id -> return @@ PatVar id
    | PatCstr (cs, cps, id) ->
      let+ cps = List.map m#cases_pattern_g cps in
      PatCstr (cs, cps, id)

  let cast_type_map f = function
    | O.CastConv x ->
      let+ x = f x in
      O.CastConv x
    | O.CastVM x ->
      let+ x = f x in
      O.CastVM x
    | O.CastCoerce -> return O.CastCoerce
    | O.CastNative x ->
      let+ x = f x in
      O.CastNative x

  let glob_constr_r_map m =
    let r = m#glob_constr_g in
    function
    | GRef (c, l) -> return @@ GRef (c, l)
    | GVar v -> return @@ GVar v
    | GEvar (v, substs) ->
      let+ substs = List.map (fun (id, c) ->
          let+ c = r c in
          id, c) substs in
      GEvar (v, substs)
    | GPatVar v -> return @@ GPatVar v
    | GApp (f, args) ->
      let+ f = r f
      and+ args = List.map r args in
      GApp (f, args)
    | GLambda (id, bk, typ, term) ->
      let+ typ = r typ
      and+ term = r term in
      GLambda (id, bk, typ, term)
    | GProd (id, bk, typ, term) ->
      let+ typ = r typ
      and+ term = r term in
      GProd (id, bk, typ, term)
    | GLetIn (id, abs, typ, term) ->
      let+ abs = r abs
      and+ typ = option_map r typ
      and+ term = r term in
      GLetIn (id, abs, typ, term)
    | GCases (cs, c, tt, cc) ->
      let+ c = option_map r c
      and+ tt = tomatch_tuples_g_map m tt
      and+ cc = cases_clauses_g_map m cc in
      GCases (cs, c, tt, cc)
    | GLetTuple (ids, (id, c), abs, term) ->
      let+ c = option_map r c
      and+ abs = r abs
      and+ term = r term in
      GLetTuple (ids, (id, c), abs, term)
    | GIf (abs, (id, c), term1, term2) ->
      let+ abs = r abs
      and+ c = option_map r c
      and+ term1 = r term1
      and+ term2 = r term2 in
      GIf (abs, (id, c), term1, term2)
    | GRec (fk, ids, decls, typs, terms) ->
      let+ decls = array_map (List.map (glob_decl_g_map m)) decls
      and+ typs = array_map r typs
      and+ terms = array_map r terms in
      GRec (fk, ids, decls, typs, terms)
    | GSort s -> return @@ GSort s
    | GHole (ek, pat, gen) ->
      let+ gen = option_map m#genarg gen in
      GHole (ek, pat, gen)
    | GCast (c, ct) ->
      let+ c = r c
      and+ ct = cast_type_map r ct in
      GCast (c, ct)
    | GInt i -> return @@ GInt i
    | GFloat f -> return @@ GFloat f

  let cases_pattern_notation_substitution_map m (subterms, recn) =
    let+ subterms = List.map m#cases_pattern_expr subterms
    and+ recn = List.map (List.map m#cases_pattern_expr) recn in
    subterms, recn

  let cases_pattern_expr_r_map m =
    let r = m#cases_pattern_expr in
    function
    | CPatAlias (pat, id) ->
      let+ pat = r pat in
      CPatAlias (pat, id)
    | CPatCstr (ind, pats1, pats2) ->
      let+ pats1 = option_map (List.map r) pats1
      and+ pats2 = List.map r pats2 in
      CPatCstr (ind, pats1, pats2)
    | CPatAtom ind -> return @@ CPatAtom ind
    | CPatOr ls ->
      let+ ls = List.map r ls in
      CPatOr ls
    | CPatNotation (n, subst, pats) ->
      let+ subst = cases_pattern_notation_substitution_map m subst
      and+ pats = List.map r pats in
      CPatNotation (n, subst, pats)
    | CPatPrim p -> return @@ CPatPrim p
    | CPatRecord ls ->
      let+ ls = List.map (fun (id, pat) ->
          let+ pat = r pat in
          id, pat) ls in
      CPatRecord ls
    | CPatDelimiters (d, pat) ->
      let+ pat = r pat in
      CPatDelimiters (d, pat)
    | CPatCast (pat, c) ->
      let+ pat = r pat
      and+ c = m#constr_expr c in
      CPatCast (pat, c)

  let case_expr_map m (c, asc, inc) =
    let+ c = m#constr_expr c
    and+ inc = option_map m#cases_pattern_expr inc in
    c, asc, inc

  let branch_expr_map m be =
    cast_map (fun (pat, c) ->
        let+ pat = List.map (List.map m#cases_pattern_expr) pat
        and+ c = m#constr_expr c in
        pat, c) be

  let local_binder_expr_map m = function
    | CLocalAssum (ids, bk, c) ->
      let+ c = m#constr_expr c in
      CLocalAssum (ids, bk, c)
    | CLocalDef (id, term, typ) ->
      let+ term = m#constr_expr term
      and+ typ = option_map m#constr_expr typ in
      CLocalDef (id, term, typ)
    | CLocalPattern pat ->
      let+ pat = cast_map (fun (pat, c) ->
          let+ pat = m#cases_pattern_expr pat
          and+ c = option_map m#constr_expr c in
          pat, c) pat in
      CLocalPattern pat

  let recursion_order_expr_r_map m = function
    | CStructRec id -> return @@ CStructRec id
    | CWfRec (id, c) ->
      let+ c = m#constr_expr c in
      CWfRec (id, c)
    | CMeasureRec (id, meas, rel) ->
      let+ meas = m#constr_expr meas
      and+ rel = option_map m#constr_expr rel in
      CMeasureRec (id, meas, rel)

  let recursion_order_expr_map m = cast_map (recursion_order_expr_r_map m)

  let fix_expr_map m (id, ro, lb, c1, c2) =
    let+ ro = option_map (recursion_order_expr_map m) ro
    and+ lb = List.map (local_binder_expr_map m) lb
    and+ c1 = m#constr_expr c1
    and+ c2 = m#constr_expr c2 in
    id, ro, lb, c1, c2

  let cofix_expr_map m (id, lb, c1, c2) =
    let+ lb = List.map (local_binder_expr_map m) lb
    and+ c1 = m#constr_expr c1
    and+ c2 = m#constr_expr c2 in
    id, lb, c1, c2

  let constr_notation_substitution_map m (subterms, recn, bind, recbind) =
    let+ subterms = List.map m#constr_expr subterms
    and+ recn = List.map (List.map m#constr_expr) recn
    and+ bind = List.map m#cases_pattern_expr bind
    and+ recbind = List.map (List.map (local_binder_expr_map m)) recbind in
    subterms, recn, bind, recbind

  let constr_expr_r_map m =
    let r = m#constr_expr in
    function
    | CRef (re, i) -> return @@ CRef (re, i)
    | CFix (id, fe) ->
      let+ fe = List.map (fix_expr_map m) fe in
      CFix (id, fe)
    | CCoFix (id, cfe) ->
      let+ cfe = List.map (cofix_expr_map m) cfe in
      CCoFix (id, cfe)
    | CProdN (lb, c) ->
      let+ lb = List.map (local_binder_expr_map m) lb
      and+ c = r c in
      CProdN (lb, c)
    | CLambdaN (lb, c) ->
      let+ lb = List.map (local_binder_expr_map m) lb
      and+ c = r c in
      CLambdaN (lb, c)
    | CLetIn (id, abs, typ, term) ->
      let+ abs = r abs
      and+ typ = option_map r typ
      and+ term = r term in
      CLetIn (id, abs, typ, term)
    | CAppExpl (x, cs) ->
      let+ cs = List.map r cs in
      CAppExpl (x, cs)
    | CApp ((proj, func), args) ->
      let+ func = r func
      and+ args = List.map (fun (c, ex) ->
          let+ c = r c in
          c, ex) args in
      CApp ((proj, func), args)
    | CRecord ls ->
      let+ ls = List.map (fun (id, c) ->
          let+ c = r c in
          id, c) ls in
      CRecord ls
    | CCases (cs, ret, ces, bes) ->
      let+ ret = option_map r ret
      and+ ces = List.map (case_expr_map m) ces
      and+ bes = List.map (branch_expr_map m ) bes in
      CCases (cs, ret, ces, bes)
    | CLetTuple (ids, (id, c1), c2, c3) ->
      let+ c1 = option_map r c1
      and+ c2 = r c2
      and+ c3 = r c3 in
      CLetTuple (ids, (id, c1), c2, c3)
    | CIf (c1, (id, c2), c3, c4) ->
      let+ c1 = r c1
      and+ c2 = option_map r c2
      and+ c3 = r c3
      and+ c4 = r c4 in
      CIf (c1, (id, c2), c3, c4)
    | CHole (ek, pat, gen) ->
      let+ gen = option_map m#genarg gen in
      CHole (ek, pat, gen)
    | CPatVar id -> return @@ CPatVar id
    | CEvar (ev, substs) ->
      let+ substs = List.map (fun (id, c) ->
          let+ c = r c in
          id, c) substs in
      CEvar (ev, substs)
    | CSort s -> return @@ CSort s
    | CCast (c, ct) ->
      let+ c = r c
      and+ ct = cast_type_map r ct in
      CCast (c, ct)
    | CNotation (n, subst) ->
      let+ subst = constr_notation_substitution_map m subst in
      CNotation (n, subst)
    | CGeneralization (bk, ak, c) ->
      let+ c = r c in
      CGeneralization (bk, ak, c)
    | CPrim p -> return @@ CPrim p
    | CDelimiters (s, c) ->
      let+ c = r c in
      CDelimiters (s, c)

  let constr_pattern_r_map f = function
    | PRef r -> return @@ PRef r
    | PVar v -> return @@ PVar v
    | PEvar (ev, substs) ->
      let+ substs = array_map f substs in
      PEvar (ev, substs)
    | PRel i -> return @@ PRel i
    | PApp (func, args) ->
      let+ func = f func
      and+ args = array_map f args in
      PApp (func, args)
    | PSoApp (pv, args) ->
      let+ args = List.map f args in
      PSoApp (pv, args)
    | PProj (p, a) ->
      let+ a = f a in
      PProj (p, a)
    | PLambda (id, typ, term) ->
      let+ typ = f typ
      and+ term = f term in
      PLambda (id, typ, term)
    | PProd (id, typ, term) ->
      let+ typ = f typ
      and+ term = f term in
      PProd (id, typ, term)
    | PLetIn (id, abs, typ, term) ->
      let+ abs = f abs
      and+ typ = option_map f typ
      and+ term = f term in
      PLetIn (id, abs, typ, term)
    | PSort s -> return @@ PSort s
    | PMeta p -> return @@ PMeta p
    | PIf (disc, tr, fa) ->
      let+ disc = f disc
      and+ tr = f tr
      and+ fa = f fa in
      PIf (disc, tr, fa)
    | PCase (pc, p1, p2, cs) ->
      let+ p1 = f p1
      and+ p2 = f p2
      and+ cs = List.map (fun (ci, ars, c) ->
          let+ c = f c in
          ci, ars, c) cs in
      PCase (pc, p1, p2, cs)
    | PFix (is, (ids, typs, terms)) ->
      let+ typs = array_map f typs
      and+ terms = array_map f terms in
      PFix (is, (ids, typs, terms))
    | PCoFix (i, (ids, typs, terms)) ->
      let+ typs = array_map f typs
      and+ terms = array_map f terms in
      PCoFix (i, (ids, typs, terms))
    | PInt i -> return @@ PInt i
    | PFloat f -> return @@ PFloat f

  let glob_arg_cata list_comb opt_comb pair_comb (extra_comb : glevel generic_argument -> 'x)
      (g : 'a generic_argument) =
    let rec aux ((GenArg (Glbwit wit, v)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Glbwit witl) g in
        let ls = List.map (fun x ->
            aux (in_gen (Glbwit wit) x)) ls in list_comb ls
      | OptArg wit as wito ->
        let e = out_gen (Glbwit wito) g in
        opt_comb @@ (match e with
            | None -> None
            | Some e -> Some (aux (in_gen (Glbwit wit) e)))
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Glbwit witp) g in
        let e1 = aux (in_gen (Glbwit wit1) e1)
        and e2 = aux (in_gen (Glbwit wit2) e2) in
        pair_comb (e1, e2)
      | ExtraArg _ -> extra_comb g
    in aux g

  let raw_arg_cata list_comb opt_comb pair_comb (extra_comb : rlevel generic_argument -> 'x)
      (g : 'a generic_argument) =
    let rec aux ((GenArg (Rawwit wit, v)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Rawwit witl) g in
        let ls = List.map (fun x ->
            aux (in_gen (Rawwit wit) x)) ls in list_comb ls
      | OptArg wit as wito ->
        let e = out_gen (Rawwit wito) g in
        opt_comb @@ (match e with
            | None -> None
            | Some e -> Some (aux (in_gen (Rawwit wit) e)))
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Rawwit witp) g in
        let e1 = aux (in_gen (Rawwit wit1) e1)
        and e2 = aux (in_gen (Rawwit wit2) e2) in
        pair_comb (e1, e2)
      | ExtraArg _ -> extra_comb g
    in aux g

end
