open Ltac_plugin
open Tacexpr
open Locus
open Util
open Genarg
open Tactypes
open Glob_term
open Genredexpr
open Pattern
open Constrexpr
open Tactics
open Tactician_util
open Genintern
open Loc
open Names

module type MapDef = sig
  include MonadNotations

  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t

  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t map
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : Loc.t option map
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer }

  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    }

  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }

  val map_sort : string
  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) gen_map

end

module MapDefTemplate (M: Monad.Def) = struct
  include WithMonadNotations(M)

  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t
  type 'a map = 'a -> 'a t
  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t map
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : Loc.t option map
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer }
    let none_transformer x f = f x
  let default_mapper =
    { glob_tactic = none_transformer
    ; raw_tactic = none_transformer
    ; glob_atomic_tactic = none_transformer
    ; raw_atomic_tactic = none_transformer
    ; glob_tactic_arg = none_transformer
    ; raw_tactic_arg = none_transformer
    ; cast = id
    ; constant = id
    ; mutind = id
    ; short_name = id
    ; located = id
    ; constr_pattern = none_transformer
    ; constr_expr = none_transformer
    ; glob_constr = none_transformer }
  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    }
  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }
end

module type GenMap = sig
  type raw
  type glob
  module M : functor (M : MapDef) -> sig
    open M
    val raw_map : recursor -> raw map
    val glob_map : recursor -> glob map
  end
end

let generic_identity_map (type r) (type g)
    (_ : (r, g, 't) genarg_type) : (module GenMap with type raw = r and type glob = g) =
(module struct
  type raw = r
  type glob = g
  module M = functor (M : MapDef) -> struct
    open M
    let raw_map _ r = return r
    let glob_map _ r = return r
  end
end)

module MapObj =
struct
  type ('raw, 'glb, 'top) obj = (module GenMap with type raw = 'raw and type glob = 'glb) option
  let name = "map"
  let default _ = Some None
end

module Map = Register (MapObj)

let generic_map = Map.obj
let register_generic_map w k = Map.register0 w (Some k)
let register_generic_map_identity w =
  register_generic_map w (generic_identity_map w)

module MakeMapper (M: MapDef) = struct
  open M

  module OList = List
  open Monad.Make(M)

  module MapObj =
  struct
    type ('raw, 'glb, 'top) obj = ('raw, 'glb) gen_map option
    let name = "map"
    let default _ = Some None
  end

  module Map = Register (MapObj)

  let map (type r) (type g) wit =
    match Map.obj wit with
    | None ->
      (match generic_map wit with
      | None -> default wit
      | Some (module G : GenMap with type raw = r and type glob = g) ->
        let module M = G.M(M) in
        let x =  {raw = M.raw_map; glb = M.glob_map} in
        Map.register0 wit (Some x); x)
    | Some x -> x

  let generic_raw_map m g
    : rlevel generic_argument t =
    let rec aux ((GenArg (Rawwit wit, v)) as g) = match wit with
      | ListArg wit as witl ->
        let ls = out_gen (Rawwit witl) g in
        let+ ls = List.map (fun x ->
            let+ res = aux (in_gen (Rawwit wit) x)
            in out_gen (Rawwit wit) res) ls in
        in_gen (Rawwit witl) ls
      | OptArg wit as wito ->
        let e = out_gen (Rawwit wito) g in
        let+ e = match e with
          | None -> return None
          | Some e -> let+ e = aux (in_gen (Rawwit wit) e) in
            Some (out_gen (Rawwit wit) e) in
        in_gen (Rawwit wito) e
      | PairArg (wit1, wit2) as witp ->
        let e1, e2 = out_gen (Rawwit witp) g in
        let+ e1 = aux (in_gen (Rawwit wit1) e1)
        and+ e2 = aux (in_gen (Rawwit wit2) e2) in
        let e1 = out_gen (Rawwit wit1) e1 in
        let e2 = out_gen (Rawwit wit2) e2 in
        in_gen (Rawwit witp) (e1, e2)
      | ExtraArg _ ->
        let+ v =((map wit).raw m v) in
        in_gen (rawwit wit) v
    in aux g

  let generic_glob_map m g
    : glevel generic_argument t =
    let rec aux ((GenArg (Glbwit wit, v)) as g) = match wit with
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
      | ExtraArg _ ->
        let+ v =((map wit).glb m v) in
        in_gen (glbwit wit) v
    in aux g

  let mcast m f CAst.{loc; v} =
    let* v = f v in m.cast (CAst.make ?loc v)
  let mdast m f CAst.{loc; v} =
    let* v = f (DAst.get_thunk v) in
    m.cast (DAst.make ?loc v)
  let located_map m f (l, x) =
    let+ l = m.located l
    and+ x = f x in
    (l, x)

  let array_map f xs = let+ xs = List.map f (Array.to_list xs) in Array.of_list xs
  let option_map f = function
    | None -> return None
    | Some x -> let+ x = f x in Some x

  let rec cases_pattern_r_map m = function
    | PatVar n -> return (PatVar n)
    | PatCstr (c, ps, id) ->
      let+ ps = List.map (cases_pattern_g_map m) ps in
      PatCstr (c, ps, id)
  and cases_pattern_g_map m p = mdast m (cases_pattern_r_map m) p

  let cast_type_map f = function
    | CastConv x ->
      let+ x = f x in
      CastConv x
    | CastVM x ->
      let+ x = f x in
      CastConv x
    | CastCoerce -> return CastCoerce
    | CastNative x ->
      let+ x = f x in
      CastNative x

  let or_var_map m f = function
    | ArgArg x ->
      let+ x = f x in
      ArgArg x
    | ArgVar l ->
      let+ l = m.cast l in
      ArgVar l
  let bindings_map m f = function
    | ImplicitBindings ls ->
      let+ ls = List.map f ls in
      ImplicitBindings ls
    | ExplicitBindings ls ->
      let+ ls = List.map (mcast m (fun (qu, x) ->
          let+ x = f x in
          (qu, x))) ls in
      ExplicitBindings ls
    | NoBindings -> return NoBindings
  let with_bindings_map m f (x, b) =
    let+ x = f x
    and+ b = bindings_map m f b in
    (x, b)
  let with_bindings_arg_map m f (flg, b) =
    let+ b = with_bindings_map m f b in
    (flg, b)
  let occurrences_gen_map f = function
    | AllOccurrencesBut ls ->
      let+ ls = List.map f ls in
      AllOccurrencesBut ls
    | OnlyOccurrences ls ->
      let+ ls = List.map f ls in
      OnlyOccurrences ls
    | x -> return x
  let occurrences_expr_map m = occurrences_gen_map (or_var_map m id)
  let clause_expr_map m f {onhyps; concl_occs} =
    let+ onhyps = option_map (List.map (fun ((og, x), flg) ->
        let+ og = occurrences_expr_map m og
        and+ x = f x in
        ((og, x), flg))) onhyps
    and+ concl_occs = occurrences_expr_map m concl_occs in
    {onhyps; concl_occs}

  let rec intro_pattern_expr_map m f = function
    | IntroAction x ->
      let+ x = intro_pattern_action_expr_map m f x in
      IntroAction x
    | x -> return x
  and intro_pattern_action_expr_map m f = function
    | IntroOrAndPattern x ->
      let+ x = or_and_intro_pattern_expr_map m f x in
      IntroOrAndPattern x
    | IntroInjection ls ->
      let+ ls = List.map (mcast m (intro_pattern_expr_map m f)) ls in
      IntroInjection ls
    | IntroApplyOn (c, p) ->
      let+ c = mcast m f c
      and+ p = mcast m (intro_pattern_expr_map m f) p in
      IntroApplyOn (c, p)
    | x -> return x
  and or_and_intro_pattern_expr_map m f = function
    | IntroOrPattern x ->
      let+ x = List.map (List.map (mcast m (intro_pattern_expr_map m f))) x in
      IntroOrPattern x
    | IntroAndPattern x ->
      let+ x = List.map (mcast m (intro_pattern_expr_map m f)) x in
      IntroAndPattern x

  let core_destruction_arg_map m f = function
    | ElimOnConstr x ->
      let+ x = f x in
      ElimOnConstr x
    | ElimOnIdent l ->
      let+ l = m.cast l in
      ElimOnIdent l
    | x -> return x
  let destruction_arg_map m f (flg, x) =
    let+ x = core_destruction_arg_map m f x in
    (flg, x)
  let induction_clause_map m f g ((da, (intro1, intro2), cl) : ('dconstr, 'id) induction_clause)
    : ('dconstr, 'id) induction_clause t =
    let+ da = destruction_arg_map m (with_bindings_map m f) da
    and+ intro1 = option_map m.cast intro1
    and+ intro2 = option_map (or_var_map m (mcast m (or_and_intro_pattern_expr_map m f))) intro2
    and+ cl = option_map (clause_expr_map m g) cl in
    (da, (intro1, intro2), cl)
  let inversion_strength_map m f g h = function
    | NonDepInversion (ik, ids, intro) ->
      let+ ids = List.map h ids
      and+ intro = option_map (or_var_map m (mcast m (or_and_intro_pattern_expr_map m g))) intro in
      NonDepInversion (ik, ids, intro)
    | DepInversion (ik, c, intro) ->
      let+ c = option_map f c
      and+ intro = option_map (or_var_map m (mcast m (or_and_intro_pattern_expr_map m g))) intro in
      DepInversion (ik, c, intro)
    | InversionUsing (c, ids) ->
      let+ c = f c
      and+ ids = List.map h ids in
      InversionUsing (c, ids)

  let match_pattern_map f = function
    | Term t ->
      let+ t = f t in
      Term t
    | Subterm (id, t) ->
      let+ t = f t in
      Subterm (id, t)

  let match_context_hyps m f = function
    | Hyp (id, mp) ->
      let+ id = m.cast id
      and+ mp = match_pattern_map f mp in
      Hyp (id, mp)
    | Def (id, mp1, mp2) ->
      let+ id = m.cast id
      and+ mp1 = match_pattern_map f mp1
      and+ mp2 = match_pattern_map f mp2 in
      Def (id, mp1, mp2)

  let or_by_notation_r_map f = function
    | AN x -> let+ x = f x in AN x
    | ByNotation x -> return (ByNotation x)

  let or_by_notation_map m f = mcast m (or_by_notation_r_map f)

  let and_short_name_map m f (x, l) =
    let+ x = f x
    and+ l = option_map m.cast l >>= m.short_name in
    (x, l)

  let union_map f g = function
    | Inl x -> let+ x = f x in Inl x
    | Inr x -> let+ x = g x in Inr x

  let red_expr_gen_map m f g h = function
    | Simpl (flg, x) ->
      let+ x = option_map (fun (oc, x) ->
          let+ x = union_map g h x in
          (oc, x)) x in
      Simpl (flg, x)
    | Fold t ->
      let+ t = List.map f t in
      Fold t
    | Pattern x ->
      let+ x = List.map (fun (x, y) ->
          let+ x = occurrences_expr_map m x
          and+ y = f y in
          (x, y)) x in
      Pattern x
    | CbvVm x ->
      let+ x = option_map (fun (oc, x) ->
          let+ x = union_map g h x in
          (oc, x)) x in
      CbvVm x
    | CbvNative x ->
      let+ x = option_map (fun (oc, x) ->
          let+ x = union_map g h x in
          (oc, x)) x in
      CbvNative x
    | Unfold x ->
      let+ x = List.map (fun (x, y) ->
          let+ x = occurrences_expr_map m x
          and+ y = g y in
          (x, y)) x in
      Unfold x
    | x -> return x

  let may_eval_map m f g h = function
    | ConstrTerm t ->
      let+ t = f t in
      ConstrTerm t
    | ConstrEval (red, t) ->
      let+ red = red_expr_gen_map m f g h red
      and+ t = f t in
      ConstrEval (red, t)
    | ConstrContext (id, t) ->
      let+ t = f t in
      ConstrContext (id, t)
    | ConstrTypeOf t ->
      let+ t = f t in
      ConstrTypeOf t

  let evaluable_global_reference_map m = function
    | EvalConstRef c ->
      let+ c = m.constant c in
      EvalConstRef c
    | EvalVarRef id -> return (EvalVarRef id)

  let glob_sort_name_map m = function
    | GType li ->
      let+ li = m.cast li in
      GType li
    | x -> return x

  let glob_sort_expr_map f = function
    | UAnonymous x -> return (UAnonymous x)
    | UNamed x ->
      let+ x = f x in
      UNamed x

  let globref_map m (r : GlobRef.t) =
    let open GlobRef in
    match r with
    | VarRef _ -> return r
    | ConstRef c ->
      let+ c = m.constant c in
      ConstRef c
    | IndRef (c, i) ->
      let+ c = m.mutind c in
      IndRef (c, i)
    | ConstructRef ((c, i), j) ->
      let+ c = m.mutind c in
      ConstructRef ((c, i), j)

  let glob_level_map m = glob_sort_expr_map (glob_sort_name_map m)

  type 'a tactic_mapper = {
    tactic_map   : 'tacexpr map;
    generic_map  : 'lev generic_argument map;
    trm_map      : 'trm map;
    dtrm_map     : 'dtrm map;
    pat_map      : 'pat map;
    ref_map      : 'ref map;
    cst_map      : 'cst map;
    nam_map      : 'nam map;
    tactic       : 'a gen_tactic_expr transformer;
    atomic_tactic : 'a gen_atomic_tactic_expr transformer;
    tactic_arg   : 'a gen_tactic_arg transformer;
    u            : mapper
  }
    constraint 'a = <
      term      :'trm;
      dterm     :'dtrm;
      pattern   :'pat;
      constant  :'cst;
      reference :'ref;
      name      :'nam;
      tacexpr   :'tacexpr;
      level     :'lev
    >

  let rec glob_constr_r_map m r c' =
    let glob_constr_map = glob_constr_map m r in
    m.glob_constr c' @@ function
     | GRef (r, l) ->
       let+ r = globref_map m r
       and+ l = option_map (List.map (glob_level_map m)) l in
       GRef (r, l)
     | GVar _ as c -> return c
     | GEvar (e, xs) ->
       let+ xs = List.map (fun (l, c) ->
           let+ c = glob_constr_map c in
           (l, c)) xs in
       GEvar (e, xs)
     | GPatVar _ as c -> return c
     | GApp (c, cs) ->
       let+ c = glob_constr_map c
       and+ cs = List.map glob_constr_map cs in
       GApp (c, cs)
     | GLambda (id, bk, c1, c2) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = glob_constr_map c2 in
       GLambda (id, bk, c1, c2)
     | GProd (id, bk, c1, c2) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = glob_constr_map c2 in
       GProd (id, bk, c1, c2)
     | GLetIn (id, c1, c2, c3) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = option_map glob_constr_map c2
       and+ c3 = glob_constr_map c3 in
       GLetIn (id, c1, c2, c3)
     | GCases (cs, c, tt, cc) ->
       let+ c = option_map glob_constr_map c
       and+ tt = List.map (fun (c, (n, pp)) ->
           let+ c = glob_constr_map c
           and+ pp = option_map m.cast pp in
           (c, (n, pp))) tt
       and+ cc = List.map (mcast m (fun (ids, cps, c) ->
           let+ cps = List.map (cases_pattern_g_map m) cps
           and+ c = glob_constr_map c in
           (ids, cps, c))) cc in
       GCases (cs, c, tt, cc)
     | GLetTuple (ids, (id, c1), c2, c3) ->
       let+ c1 = option_map glob_constr_map c1
       and+ c2 = glob_constr_map c2
       and+ c3 = glob_constr_map c3 in
       GLetTuple (ids, (id, c1), c2, c3)
     | GIf (c1, (id, c2), c3, c4) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = option_map glob_constr_map c2
       and+ c3 = glob_constr_map c3
       and+ c4 = glob_constr_map c4 in
       GIf (c1, (id, c2), c3, c4)
     | GRec (fk, ids, decls, cs1, cs2) ->
       let+ decls = array_map (List.map (fun (id, bk, c1, c2) ->
           let+ c1 = option_map glob_constr_map c1
           and+ c2 = glob_constr_map c2 in
           (id, bk, c1, c2))) decls
       and+ cs1 = array_map glob_constr_map cs1
       and+ cs2 = array_map glob_constr_map cs2 in
       GRec (fk, ids, decls, cs1, cs2)
     | GSort _ as c -> return c
     | GHole (k, intr, gen) ->
       let+ gen = option_map (generic_glob_map (r m)) gen in
       GHole (k, intr, gen)
     | GCast (c1, c2) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = cast_type_map glob_constr_map c2 in
       GCast (c1, c2)
     | GInt _ as c -> return c
     | GFloat _ as c -> return c
  and glob_constr_map m r c = mdast m (glob_constr_r_map m r) c

  let rec cases_pattern_expr_r_map m r (case : cases_pattern_expr_r) =
    let cases_pattern_expr_map = cases_pattern_expr_map m r in
    match case with
    | CPatAlias (ca, l) ->
      let+ ca = cases_pattern_expr_map ca
      and+ l = m.cast l in
      CPatAlias (ca, l)
    | CPatCstr (id, cas1, cas2) ->
      let+ id = m.cast id
      and+ cas1 = option_map (List.map cases_pattern_expr_map) cas1
      and+ cas2 = List.map (cases_pattern_expr_map) cas2 in
      CPatCstr (id, cas1, cas2)
    | CPatAtom l ->
      let+ l = option_map m.cast l in
      CPatAtom l
    | CPatOr pas ->
      let+ pas = List.map cases_pattern_expr_map pas in
      CPatOr pas
    | CPatNotation (ns, (cas1, cas2), cas3) ->
      let+ cas1 = List.map cases_pattern_expr_map cas1
      and+ cas2 = List.map (List.map cases_pattern_expr_map) cas2
      and+ cas3 = List.map cases_pattern_expr_map cas3 in
      CPatNotation (ns, (cas1, cas2), cas3)
    | CPatPrim _ -> return case
    | CPatRecord xs ->
      let+ xs = List.map (fun (qu, ca) ->
          let+ qu = m.cast qu
          and+ ca = cases_pattern_expr_map ca in
          (qu, ca)) xs in
      CPatRecord xs
    | CPatDelimiters (d, c) ->
      let+ c = cases_pattern_expr_map c in
      CPatDelimiters (d, c)
    | CPatCast (c1, c2) ->
      let+ c1 = cases_pattern_expr_map c1
      and+ c2 = constr_expr_map m r c2 in
      CPatCast (c1, c2)
  and cases_pattern_expr_map m r = mcast m (cases_pattern_expr_r_map m r)
  and constr_expr_r_map m (r : mapper -> recursor) (c' : constr_expr_r) =
    let constr_expr_map = constr_expr_map m r in
    m.constr_expr c' @@ function
    | CRef (qu, i) ->
      let+ qu = m.cast qu in
      CRef (qu, i)
    | CFix (li, fix) ->
      let+ li = m.cast li
      and+ fix = List.map (fix_expr_map m r) fix in
      CFix (li, fix)
    | CCoFix (li, cofix) ->
     let+ li = m.cast li
     and+ cofix = List.map (cofix_expr_map m r) cofix in
     CCoFix (li, cofix)
    | CProdN (lb, c) ->
      let+ lb = List.map (local_binder_expr_map m r) lb
      and+ c = constr_expr_map c in
      CProdN (lb, c)
    | CLambdaN (lb, c) ->
      let+ lb = List.map (local_binder_expr_map m r) lb
      and+ c = constr_expr_map c in
      CLambdaN (lb, c)
    | CLetIn (l, c1, c2, c3) ->
      let+ l = m.cast l
      and+ c1 = constr_expr_map c1
      and+ c2 = option_map constr_expr_map c2
      and+ c3 = constr_expr_map c3 in
      CLetIn (l, c1, c2, c3)
    | CAppExpl ((flg, l, ie), cs) ->
      let+ l = m.cast l
      and+ cs = List.map constr_expr_map cs in
      CAppExpl ((flg, l, ie), cs)
    | CApp ((flg, c), cs) ->
      let+ c = constr_expr_map c
      and+ cs = List.map (fun (c, e) ->
          let+ c = constr_expr_map c in
          (c,e)) cs in
      CApp ((flg, c), cs)
    | CRecord xs ->
      let+ xs = List.map (fun (l, c) ->
        let+ l = m.cast l
        and+ c = constr_expr_map c in
        (l, c)) xs in
      CRecord xs
    | CCases (sty, c1, cs, bs) ->
      let+ c1 = option_map constr_expr_map c1
      and+ cs = List.map (fun (c, l, pat) ->
          let+ c = constr_expr_map c
          and+ l = option_map m.cast l
          and+ pat = option_map (cases_pattern_expr_map m r) pat in
        (c, l, pat)) cs
      and+ bs = List.map (mcast m (fun (cs, c) ->
          let+ cs = List.map (List.map (cases_pattern_expr_map m r)) cs
          and+ c = constr_expr_map c in
         (cs, c))) bs in
      CCases (sty, c1, cs, bs)
    | CLetTuple (ls, (l, c1), c2, c3) ->
      let+ ls = List.map m.cast ls
      and+ l = option_map m.cast l
      and+ c1 = option_map constr_expr_map c1
      and+ c2 = constr_expr_map c2
      and+ c3 = constr_expr_map c3 in
      CLetTuple (ls, (l, c1), c2, c3)
    | CIf (c1, (l, c2), c3, c4) ->
     let+ l = option_map m.cast l
     and+ c1 = constr_expr_map c1
     and+ c2 = option_map constr_expr_map c2
     and+ c3 = constr_expr_map c3
     and+ c4 = constr_expr_map c4 in
     CIf (c1, (l, c2), c3, c4)
    | CHole (k, intr, gen) ->
      let+ gen = option_map (generic_raw_map (r m)) gen in
      CHole (k, intr, gen)
    | CPatVar _ as c -> return c
    | CEvar (e, xs) ->
      let+ xs = List.map (fun (l, c) ->
          let+ c = constr_expr_map c in
          (l, c)) xs in
      CEvar (e, xs)
    | CSort _ as c -> return c
    | CCast (c, ct) ->
      let+ c = constr_expr_map c
      and+ ct = cast_type_map constr_expr_map ct in
      CCast (c, ct)
    | CNotation (ns, (cs1, cs2, ps, bs)) ->
      let+ cs1 = List.map constr_expr_map cs1
      and+ cs2 = List.map (List.map constr_expr_map) cs2
      and+ ps = List.map (cases_pattern_expr_map m r) ps
      and+ bs = List.map (List.map (local_binder_expr_map m r)) bs in
      CNotation (ns, (cs1, cs2, ps, bs))
    | CGeneralization (bk, ak, c) ->
      let+ c = constr_expr_map c in
      CGeneralization (bk, ak, c)
    | CPrim _ as c -> return c
    | CDelimiters (str, c) ->
     let+ c = constr_expr_map c in
     CDelimiters (str, c)
  and fix_expr_map m r (li, ord, bi, c1, c2) =
    let+ li = m.cast li
    and+ ord = option_map (recursion_order_expr m r) ord
    and+ bi = List.map (local_binder_expr_map m r) bi
    and+ c1 = (constr_expr_map m r) c1
    and+ c2 = (constr_expr_map m r) c2 in
    (li, ord, bi, c1, c2)
  and cofix_expr_map m r (li, bi, c1, c2) =
    let+ li = m.cast li
    and+ bi = List.map (local_binder_expr_map m r) bi
    and+ c1 = (constr_expr_map m r) c1
    and+ c2 = (constr_expr_map m r) c2 in
    (li, bi, c1, c2)
  and local_binder_expr_map m r = function
    | CLocalAssum (lis, bk, c) ->
      let+ lis = List.map m.cast lis
      and+ c = constr_expr_map m r c in
      CLocalAssum (lis, bk, c)
    | CLocalDef (li, c1, c2) ->
      let+ li = m.cast li
      and+ c1 = constr_expr_map m r c1
      and+ c2 = option_map (constr_expr_map m r) c2 in
      CLocalDef (li, c1, c2)
    | CLocalPattern c ->
      let+ c = mcast m (fun (ca, c) ->
          let+ ca = cases_pattern_expr_map m r ca
          and+ c = option_map (constr_expr_map m r) c in
          (ca, c)) c in
      CLocalPattern c
  and recursion_order_expr_r m r = function
    | CStructRec li ->
      let+ li = m.cast li in
      CStructRec li
    | CWfRec (li, c) ->
      let+ li = m.cast li
      and+ c = constr_expr_map m r c in
      CWfRec (li, c)
    | CMeasureRec (li, c1, c2) ->
      let+ li = option_map m.cast li
      and+ c1 = constr_expr_map m r c1
      and+ c2 = option_map (constr_expr_map m r) c2 in
      CMeasureRec (li, c1, c2)
  and recursion_order_expr m r x = mcast m (recursion_order_expr_r m r) x
  and constr_expr_map (m : mapper) r c =
    mcast m (constr_expr_r_map m r) c

  and constr_pattern_map m pat' =
    let constr_pattern_map = constr_pattern_map m in
    m.constr_pattern pat' @@ function
     | PRef r ->
       let+ r = globref_map m r in
       PRef r
     | PVar _ as pat -> return pat
     | PEvar (e, ps) ->
       let+ ps = array_map constr_pattern_map ps in
       PEvar (e, ps)
     | PRel _ as pat -> return pat
     | PApp (p, ps) ->
       let+ p = constr_pattern_map p
       and+ ps = array_map constr_pattern_map ps in
       PApp (p, ps)
     | PSoApp (id, ps) ->
       let+ ps = List.map constr_pattern_map ps in
       PSoApp (id, ps)
     | PProj (id, p) ->
       let+ p = constr_pattern_map p in
       PProj (id, p)
     | PLambda (id, p1, p2) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2 in
       PLambda (id, p1, p2)
     | PProd (id, p1, p2) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2 in
       PProd (id, p1, p2)
     | PLetIn (id, p1, p2, p3) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = option_map constr_pattern_map p2
       and+ p3 = constr_pattern_map p3 in
       PLetIn (id, p1, p2, p3)
     | PSort _ as pat -> return pat
     | PMeta _ as pat -> return pat
     | PIf (p1, p2, p3) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2
       and+ p3 = constr_pattern_map p3 in
       PIf (p1, p2, p3)
     | PCase (ci, p1, p2, ps) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2
       and+ ps = List.map (fun (i, bs, p) ->
           let+ p = constr_pattern_map p in
           (i, bs, p)) ps in
       PCase (ci, p1, p2, ps)
     | PFix (x, (ids, p1s, p2s)) ->
       let+ p1s = array_map constr_pattern_map p1s
       and+ p2s = array_map constr_pattern_map p2s in
       PFix (x, (ids, p1s, p2s))
     | PCoFix (i, (ids, p1s, p2s)) ->
       let+ p1s = array_map constr_pattern_map p1s
       and+ p2s = array_map constr_pattern_map p2s in
       PCoFix (i, (ids, p1s, p2s))
     | PInt _ as pat -> return pat
     | PFloat _ as pat -> return pat

  and glob_constr_and_expr_map m r ((gc, ce) : g_trm) =
    let+ gc = glob_constr_map m r gc
    and+ ce = option_map (constr_expr_map m r) ce in
    (gc, ce)
  and g_pat_map m r ((ids, c, cp) : g_pat) =
    let+ c = glob_constr_and_expr_map m r c
    and+ cp = constr_pattern_map m cp in
    (ids, c, cp)

  and tactic_arg_map (m : 'a tactic_mapper) tac' =
    m.tactic_arg tac' @@ function
     | TacGeneric genarg ->
       let+ genarg = m.generic_map genarg in
       TacGeneric genarg
     | ConstrMayEval x ->
       let+ x = may_eval_map m.u m.trm_map m.cst_map m.pat_map x in
       ConstrMayEval x
     | Reference r ->
       let+ r = m.ref_map r in
       Reference r
     | TacCall c ->
       let+ c = mcast m.u (fun (ref, args) ->
           let+ ref = m.ref_map ref
           and+ args = List.map (tactic_arg_map m) args in (ref, args)) c in
       TacCall c
     | TacFreshId _ as tac -> return tac
     | Tacexp t ->
       let+ t = m.tactic_map t in
       Tacexp t
     | TacPretype t ->
       let+ t = m.trm_map t in
       TacPretype t
     | TacNumgoals as tac -> return tac
  and match_rule_map (m : 'a tactic_mapper) tac = List.map (function
      | Pat (hyps, pat, t) ->
        let+ hyps = List.map (match_context_hyps m.u m.pat_map) hyps
        and+ pat = match_pattern_map m.pat_map pat
        and+ t = m.tactic_map t in
        Pat (hyps, pat, t)
      | All t ->
        let+ t = m.tactic_map t in
        All t) tac
  and atomic_tactic_map
      (m : 'a tactic_mapper) (tac' : 'a gen_atomic_tactic_expr) : 'a gen_atomic_tactic_expr t =
    m.atomic_tactic tac' @@ function
     | TacIntroPattern (flg, intros) ->
       let+ intros = List.map (mcast m.u (intro_pattern_expr_map m.u m.trm_map)) intros in
       TacIntroPattern (flg, intros)
     | TacApply (flg1, flg2, bi, intro) ->
       let+ bi = List.map (with_bindings_arg_map m.u m.trm_map) bi
       and+ intro = option_map (fun (l, intro) ->
           let+ l = m.u.cast l
           and+ intro = option_map (mcast m.u (intro_pattern_expr_map m.u m.trm_map)) intro in
           (l, intro)) intro in
       TacApply (flg1, flg2, bi, intro)
     | TacElim (flg, c1, c2) ->
       let+ c1 = with_bindings_arg_map m.u m.trm_map c1
       and+ c2 = option_map (with_bindings_map m.u m.trm_map) c2 in
       TacElim (flg, c1, c2)
     | TacCase (flg, c) ->
       let+ c = with_bindings_arg_map m.u m.trm_map c in
       TacCase (flg, c)
     | TacMutualFix (id, n, fs) ->
       let+ fs = List.map (fun (id, n, c) ->
           let+ c = m.trm_map c in
           (id, n, c)) fs in
       TacMutualFix (id, n, fs)
     | TacMutualCofix (id, fs) ->
       let+ fs = List.map (fun (id, c) ->
           let+ c = m.trm_map c in
           (id, c)) fs in
       TacMutualCofix (id, fs)
     | TacAssert (flg1, flg2, t, intro, c) ->
       let+ t = option_map (option_map m.tactic_map) t
       and+ intro = option_map (mcast m.u (intro_pattern_expr_map m.u m.trm_map)) intro
       and+ c = m.trm_map c in
       TacAssert (flg1, flg2, t, intro, c)
     | TacGeneralize xs ->
       let+ xs = List.map (fun ((oe, c), id) ->
           let+ oe = occurrences_expr_map m.u oe
           and+ c = m.trm_map c in
           ((oe, c), id)) xs in
       TacGeneralize xs
     | TacLetTac (flg1, id, c, cl, flg2, intro) ->
       let+ c = m.trm_map c
       and+ cl = clause_expr_map m.u m.u.cast cl
       and+ intro = option_map m.u.cast intro in
       TacLetTac (flg1, id, c, cl, flg2, intro)
     | TacInductionDestruct (flg1, flg2, (indc, c)) ->
       let+ indc = List.map (induction_clause_map m.u m.trm_map m.u.cast) indc
       and+ c = option_map (with_bindings_map m.u m.trm_map) c in
       TacInductionDestruct (flg1, flg2, (indc, c))
     | TacReduce (rede, cl) ->
       let+ rede = red_expr_gen_map m.u m.trm_map m.cst_map m.pat_map rede
       and+ cl = clause_expr_map m.u m.u.cast cl in
       TacReduce (rede, cl)
     | TacChange (flg, pat, c, cl) ->
       let+ pat = option_map m.pat_map pat
       and+ c = m.trm_map c
       and+ cl = clause_expr_map m.u m.u.cast cl in
       TacChange (flg, pat, c, cl)
     | TacRewrite (flg1, bis, cl, t) ->
       let+ bis = List.map (fun (flg, mu, bi) ->
           let+ bi = with_bindings_arg_map m.u m.trm_map bi in
           (flg, mu, bi)) bis
       and+ cl = clause_expr_map m.u m.u.cast cl
       and+ t = option_map m.tactic_map t in
       TacRewrite (flg1, bis, cl, t)
     | TacInversion (is, qh) ->
       let+ is = inversion_strength_map m.u m.trm_map m.trm_map m.u.cast is in
       TacInversion (is, qh)
  and tactic_map
      (m : 'a tactic_mapper) (tac' : 'a gen_tactic_expr) : 'a gen_tactic_expr t =
    m.tactic tac' @@ function
     | TacInfo t ->
       let+ t = m.tactic_map t in
       TacInfo t
     | TacAtom a ->
       let+ a = mcast m.u (atomic_tactic_map m) a in
       TacAtom a
     | TacThen (t1, t2)  ->
       let+ t1 = m.tactic_map t1
       and+ t2 = m.tactic_map t2 in
       TacThen (t1, t2)
     | TacDispatch tl ->
       let+ tl = List.map m.tactic_map tl in
       TacDispatch tl
     | TacExtendTac (tl1, t, tl2) ->
       let+ tl1 = array_map m.tactic_map tl1
       and+ t   = m.tactic_map t
       and+ tl2 = array_map m.tactic_map tl2 in
       TacExtendTac (tl1, t, tl2)
     | TacThens (t1, tl) ->
       let+ t1 = m.tactic_map t1
       and+ tl = List.map m.tactic_map tl in
       TacThens (t1, tl)
     | TacThens3parts (t1, tl1, t2, tl2) ->
       let+ t1 = m.tactic_map t1
       and+ tl1 = array_map m.tactic_map tl1
       and+ t2 = m.tactic_map t2
       and+ tl2 = array_map m.tactic_map tl2 in
       TacThens3parts (t1, tl1, t2, tl2)
     | TacFirst ts ->
       let+ ts = List.map m.tactic_map ts in
       TacFirst ts
     | TacComplete t ->
       let+ t = m.tactic_map t in
       TacComplete t
     | TacSolve ts ->
       let+ ts = List.map m.tactic_map ts in
       TacSolve ts
     | TacTry t ->
       let+ t = m.tactic_map t in
       TacTry t
     | TacOr (t1, t2) ->
       let+ t1 = m.tactic_map t1
       and+ t2 = m.tactic_map t2 in
       TacOr (t1, t2)
     | TacOnce t ->
       let+ t = m.tactic_map t in
       TacOnce t
     | TacExactlyOnce t ->
       let+ t = m.tactic_map t in
       TacExactlyOnce t
     | TacIfThenCatch (t1, t2, t3) ->
       let+ t1 = m.tactic_map t1
       and+ t2 = m.tactic_map t2
       and+ t3 = m.tactic_map t3 in
       TacIfThenCatch (t1, t2, t3)
     | TacOrelse (t1, t2) ->
       let+ t1 = m.tactic_map t1
       and+ t2 = m.tactic_map t2 in
       TacOrelse (t1, t2)
     | TacDo (n, t) ->
       let+ t = m.tactic_map t in
       TacDo (n, t)
     | TacTimeout (n, t) ->
       let+ t = m.tactic_map t in
       TacTimeout (n, t)
     | TacTime (s, t) ->
       let+ t = m.tactic_map t in
       TacTime (s, t)
     | TacRepeat t ->
       let+ t = m.tactic_map t in
       TacRepeat t
     | TacProgress t ->
       let+ t = m.tactic_map t in
       TacProgress t
     | TacShowHyps t ->
       let+ t = m.tactic_map t in
       TacShowHyps t
     | TacAbstract (t, id) ->
       let+ t = m.tactic_map t in
       TacAbstract (t, id)
     | TacId _ as tac -> return tac
     | TacFail _ as tac -> return tac
     | TacLetIn (flg, ts, t) ->
       let lns, args = OList.split ts in
       let+ t = m.tactic_map t
       and+ args = List.map (tactic_arg_map m) args in
       TacLetIn (flg, OList.combine lns args, t)
     | TacMatch (flg, t, ts) ->
       let+ t = m.tactic_map t
       and+ ts = (match_rule_map m) ts in
       TacMatch (flg, t, ts)
     | TacMatchGoal (flg, d, ts) ->
       let+ ts = (match_rule_map m) ts in
       TacMatchGoal (flg, d, ts)
     | TacFun (args, t) ->
       let+ t = m.tactic_map t in
       TacFun (args, t)
     | TacArg c ->
       let+ c = mcast m.u (fun a -> (tactic_arg_map m) a) c in
       TacArg c
     | TacSelect (i, t) ->
       let+ t = m.tactic_map t in
       TacSelect (i, t)
     | TacML c ->
       let+ c = mcast m.u (fun (ml, args) ->
           let+ args = List.map (tactic_arg_map m) args in (ml, args)) c in
       TacML c
     | TacAlias c ->
       let+ c = mcast m.u (fun (id, args) ->
           let+ args = List.map (tactic_arg_map m) args in (id, args)) c in
       TacAlias c

  let rec recursor m =
    { option_map = option_map
    ; cast_map = (fun f -> mcast m f)
    ; constant_map = m.constant
    ; mutind_map = m.mutind
    ; short_name_map = (fun f -> m.short_name f)
    ; or_var_map = (fun f -> or_var_map m f)
    ; intro_pattern_expr_map = (fun f -> intro_pattern_expr_map m f)
    ; constr_expr_map = constr_expr_map m recursor
    ; glob_constr_and_expr_map = glob_constr_and_expr_map m recursor
    ; bindings_map = (fun f -> bindings_map m f)
    ; with_bindings_map = (fun f -> with_bindings_map m f)
    ; located_map = (fun f -> located_map m f)
    ; clause_expr_map = (fun f -> clause_expr_map m f)
    ; destruction_arg_map = (fun f -> destruction_arg_map m f)
    ; raw_tactic_expr_map = raw_tactic_expr_map m
    ; glob_tactic_expr_map = glob_tactic_expr_map m
    }
  and raw_tactic_mapper m = {
    tactic_map   = raw_tactic_expr_map m;
    trm_map      = constr_expr_map m recursor;
    dtrm_map     = constr_expr_map m recursor;
    pat_map      = constr_expr_map m recursor;
    ref_map      = m.cast;
    nam_map      = m.cast;
    cst_map      = or_by_notation_map m m.cast;
    generic_map  = generic_raw_map (recursor m);
    u            = m;
    tactic       = m.raw_tactic;
    atomic_tactic = m.raw_atomic_tactic;
    tactic_arg   = m.raw_tactic_arg
  }
  and raw_tactic_expr_map m tac =
    tactic_map (raw_tactic_mapper m) tac
  and glob_tactic_mapper m = {
    tactic_map   = glob_tactic_expr_map m;
    trm_map      = glob_constr_and_expr_map m recursor;
    dtrm_map     = glob_constr_and_expr_map m recursor;
    pat_map      = g_pat_map m recursor;
    ref_map      = or_var_map m (fun (_, id) -> return (None, id));
    nam_map      = m.cast;
    cst_map      = or_var_map m (and_short_name_map m (evaluable_global_reference_map m));
    generic_map  = generic_glob_map (recursor m);
    u            = m;
    tactic       = m.glob_tactic;
    atomic_tactic = m.glob_atomic_tactic;
    tactic_arg    = m.glob_tactic_arg
  }
  and glob_tactic_expr_map m tac =
    tactic_map (glob_tactic_mapper m) tac

  let glob_tactic_arg_map m tac = tactic_arg_map (glob_tactic_mapper m) tac
  let glob_atomic_tactic_map m tac = atomic_tactic_map (glob_tactic_mapper m) tac
  let raw_tactic_arg_map m tac = tactic_arg_map (raw_tactic_mapper m) tac
  let raw_atomic_tactic_map m tac = atomic_tactic_map (raw_tactic_mapper m) tac
  let glob_constr_map m = glob_constr_map m recursor
  let constr_expr_map m = constr_expr_map m recursor
end
