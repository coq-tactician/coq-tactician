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
open Monad_util
open Genintern
open Loc
open Names
open Goal_select
open Namegen

module type MapDef = sig
  include MonadNotations

  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t

  val with_binders : Id.t list -> 'a -> ('a -> 'a t) -> ((Id.t -> Id.t) * 'a) t

  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t t -> 'a CAst.t t
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : 'a. (Loc.t option * 'a) t -> (Loc.t option * 'a) t
    ; variable : Id.t map
    ; qualid : (DirPath.t * Id.t) map
    (* Guaranteed not be at least partially qualified (otherwise variable is called) *)
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer
    ; glob_constr_and_expr : Genintern.glob_constr_and_expr transformer
    ; glob_constr_pattern_and_expr : Genintern.glob_constr_pattern_and_expr transformer
    }

  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; variable_map : Id.t map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; glob_constr_pattern_and_expr_map : glob_constr_pattern_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    ; qualid_map : Libnames.qualid map
    ; globref_map : GlobRef.t map
    ; quantified_hypothesis_map : quantified_hypothesis map
    ; red_expr_gen_map : 'a 'b 'c. 'a map -> 'b map -> 'c map -> ('a, 'b, 'c) red_expr_gen map
    }

  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }

  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) gen_map

end

module MapDefTemplate (M: Monad.Def) = struct
  module OList = List
  include WithMonadNotations(M)

  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t
  type 'a map = 'a -> 'a t
  let with_binders _ a cont = map (fun x -> (fun x -> x), x) @@ cont a
  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t t -> 'a CAst.t t
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : 'a. (Loc.t option * 'a) t -> (Loc.t option * 'a) t
    ; variable : Id.t map
    ; qualid : (DirPath.t * Id.t) map
    (* Guaranteed not be at least partially qualified (otherwise variable is called) *)
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer
    ; glob_constr_and_expr : Genintern.glob_constr_and_expr transformer
    ; glob_constr_pattern_and_expr : Genintern.glob_constr_pattern_and_expr transformer
    }
  let none_transformer x f = f x
  let default_mapper =
    { glob_tactic = none_transformer
    ; raw_tactic = none_transformer
    ; glob_atomic_tactic = none_transformer
    ; raw_atomic_tactic = none_transformer
    ; glob_tactic_arg = none_transformer
    ; raw_tactic_arg = none_transformer
    ; cast = (fun x -> x)
    ; constant = id
    ; mutind = id
    ; short_name = id
    ; located = (fun x -> x)
    ; variable = id
    ; qualid = id
    ; constr_pattern = none_transformer
    ; constr_expr = none_transformer
    ; glob_constr = none_transformer
    ; glob_constr_and_expr = none_transformer
    ; glob_constr_pattern_and_expr = none_transformer
    }
  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; variable_map : Id.t map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; glob_constr_pattern_and_expr_map : glob_constr_pattern_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    ; qualid_map : Libnames.qualid map
    ; globref_map : GlobRef.t map
    ; quantified_hypothesis_map : quantified_hypothesis map
    ; red_expr_gen_map : 'a 'b 'c. 'a map -> 'b map -> 'c map -> ('a, 'b, 'c) red_expr_gen map
    }
  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }
  (* These are witnesses that are known to be unmappable at the moment *)
  let exclude = ["ssrrwarg"; "ssrintros_ne"; "ssrhint3arg"]
  let warnProblem wit =
    let pp = pr_argument_type wit in
    let pps = Pp.string_of_ppcmds pp in
    if OList.exists (fun w -> String.equal w pps) exclude then () else
      Feedback.msg_warning (Pp.(str "Tactician is having problems with " ++
                                str "the following tactic. Please report. " ++
                                pr_argument_type wit))
  let default wit = { raw = (fun _ -> warnProblem (ArgumentType wit); id)
                    ; glb = (fun _ -> warnProblem (ArgumentType wit); id)}
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

  let filter_placeholders = OList.map_filter (function
      | Name.Name id -> Some id
      | Name.Anonymous -> None )
  let filter_lnames ls =
    let ls = OList.map (fun CAst.{v; _} -> v) ls in
    filter_placeholders ls
  let name_id_map f = function
    | Name.Anonymous -> Name.Anonymous
    | Name.Name id -> Name.Name (f id)

  let rec cases_pattern_expr_r_id_map f (case : cases_pattern_expr_r) =
    let cases_pattern_expr_id_map = cases_pattern_expr_id_map f in
    match case with
    | CPatAlias (ca, l) ->
      CPatAlias (cases_pattern_expr_id_map ca, CAst.map (name_id_map f) l)
    | CPatCstr (id, cas1, cas2) ->
      (* id is not a variable *)
      let cas1 = Option.map (OList.map cases_pattern_expr_id_map) cas1 in
      let cas2 = OList.map (cases_pattern_expr_id_map) cas2 in
      CPatCstr (id, cas1, cas2)
    | CPatAtom l ->
      (* TODO: I would expect this to always be a binder, since CPatCstr already handles
         constructors. However, sinse this is a qualid, this assumption is clearly faulty,
         and what I do here is likely wrong. Most likely, it is dependent on the context
         whether or not this is a binder *)
      let l = Option.map (fun qu ->
          let dp, id = Libnames.repr_qualid qu in
          if DirPath.is_empty dp then Libnames.make_qualid ?loc:qu.loc dp (f id) else qu
        ) l in
      CPatAtom l
    | CPatOr pas ->
      CPatOr (OList.map cases_pattern_expr_id_map pas)
    | CPatNotation (ns, (cas1, cas2), cas3) ->
      let cas1 = OList.map cases_pattern_expr_id_map cas1 in
      let cas2 = OList.map (OList.map cases_pattern_expr_id_map) cas2 in
      let cas3 = OList.map cases_pattern_expr_id_map cas3 in
      CPatNotation (ns, (cas1, cas2), cas3)
    | CPatPrim _ -> case
    | CPatRecord xs ->
      let xs = OList.map (fun (qu, ca) ->
          (* qu is not a variable *)
          qu, cases_pattern_expr_id_map ca) xs in
      CPatRecord xs
    | CPatDelimiters (d, c) ->
      CPatDelimiters (d, cases_pattern_expr_id_map c)
    | CPatCast (c1, c2) ->
      CPatCast (cases_pattern_expr_id_map c1, c2)
  and cases_pattern_expr_id_map f c =
    CAst.map (cases_pattern_expr_r_id_map f) c
  let local_binder_expr_id_map f : local_binder_expr -> local_binder_expr = function
    | CLocalAssum (lis, bk, c) ->
      CLocalAssum (OList.map ((CAst.map (name_id_map f))) lis, bk, c)
    | CLocalDef (li, c1, c2) ->
      CLocalDef (CAst.map (name_id_map f) li, c1, c2)
    | CLocalPattern pat ->
      CLocalPattern (CAst.map (fun (ca, c) -> cases_pattern_expr_id_map f ca, c) pat)

  let mcast m f CAst.{loc; v} =
    m.cast (let+ v = f v in CAst.make ?loc v)
  let mdast m f CAst.{loc; v} =
    m.cast (let+ v = f (DAst.get_thunk v) in
            DAst.make ?loc v)
  let located_map m f (l, x) =
    m.located (let+ x = f x in
               (l, x))

  let array_map f xs = let+ xs = List.map f (Array.to_list xs) in Array.of_list xs
  let array_combine xs ys = Array.of_list (OList.combine (Array.to_list xs) (Array.to_list ys))
  let array_split xs =
    let x1, x2 = OList.split (Array.to_list xs) in
    Array.of_list x1, Array.of_list x2
  let option_map f = function
    | None -> return None
    | Some x -> let+ x = f x in Some x

  let name_map m = function
    | Name.Anonymous -> return Name.Anonymous
    | Name.Name id ->
      let+ id = m.variable id in
      Name.Name id

  let qualid_map m (CAst.{loc; _} as q) =
    let d, id = Libnames.repr_qualid q in
    if DirPath.is_empty d then
      m.cast (let+ id = m.variable id in
              Libnames.make_qualid ?loc DirPath.empty id)
    else m.cast (let+ d, id = m.qualid (d, id) in Libnames.make_qualid ?loc d id)

  let rec cases_pattern_r_map m = function
    | PatVar n -> return (PatVar n, [])
    | PatCstr (c, ps, id) ->
      let+ ps = List.map (cases_pattern_g_map m) ps in
      let ps, bndrs = OList.split ps in
      PatCstr (c, ps, id), id :: OList.concat bndrs
  and cases_pattern_g_map m p =
    let+ p = mdast m (cases_pattern_r_map m) p in
    let p', bndrs = DAst.get p in
    DAst.map (fun _ -> p') p, bndrs

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
      let+ l = mcast m m.variable l in
      ArgVar l
  let quantified_hypothesis_map m = function
    | AnonHyp _ as x -> return x
    | NamedHyp id ->
      let+ id = m.variable id in
      NamedHyp id
  let bindings_map m f = function
    | ImplicitBindings ls ->
      let+ ls = List.map f ls in
      ImplicitBindings ls
    | ExplicitBindings ls ->
      let+ ls = List.map (mcast m (fun (qu, x) ->
          let+ qu = quantified_hypothesis_map m qu
          and+ x = f x in
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

  let intro_pattern_naming_expr_map m = function
    (* We see neither of these as binders. The first should be already bound by a `let id := fresh in ..`.
       The second is just a name suggestion and cannot be used as a binder *)
    | IntroIdentifier id ->
      let+ id = m.variable id in
      IntroIdentifier id
    | IntroFresh id ->
      let+ id = m.variable id in
      IntroIdentifier id
    | IntroAnonymous as x -> return x

  let rec intro_pattern_expr_map m f = function
    | IntroNaming n ->
      let+ n = intro_pattern_naming_expr_map m n in
      IntroNaming n
    | IntroAction x ->
      let+ x = intro_pattern_action_expr_map m f x in
      IntroAction x
    | IntroForthcoming _ as x -> return x
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
      let+ l = mcast m m.variable l in
      ElimOnIdent l
    | x -> return x
  let destruction_arg_map m f (flg, x) =
    let+ x = core_destruction_arg_map m f x in
    (flg, x)
  let induction_clause_map m f g ((da, (intro1, intro2), cl) : ('dconstr, 'id) induction_clause)
    : ('dconstr, 'id) induction_clause t =
    let+ da = destruction_arg_map m (with_bindings_map m f) da
    and+ intro1 = option_map (mcast m (intro_pattern_naming_expr_map m)) intro1
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
      Term t, []
    | Subterm (id, t) ->
      let+ t = f t in
      Subterm (id, t), Option.cata (fun id -> [id]) [] id
  let match_pattern_id_map f = function
    | Term t -> Term t
    | Subterm (id, t) ->
      Subterm (Option.map f id, t)

  let match_context_hyps_map m f = function
    | Hyp (id, mp) ->
      let+ id = m.cast @@ return id
      and+ mp, bnds = match_pattern_map f mp in
      Hyp (id, mp), filter_lnames [id] @ bnds
    | Def (id, mp1, mp2) ->
      let+ id = m.cast @@ return id
      and+ mp1, bnds1 = match_pattern_map f mp1
      and+ mp2, bnds2 = match_pattern_map f mp2 in
      Def (id, mp1, mp2), filter_lnames [id] @ bnds2@bnds1
  let match_context_hyps_id_map f = function
    | Hyp (id, mp) ->
      Hyp (CAst.map (name_id_map f) id, match_pattern_id_map f mp)
    | Def (id, mp1, mp2) ->
      Def (CAst.map (name_id_map f) id, match_pattern_id_map f mp1, match_pattern_id_map f mp2)

  let or_by_notation_r_map f = function
    | AN x -> let+ x = f x in AN x
    | ByNotation x -> return (ByNotation x)

  let or_by_notation_map m f = mcast m (or_by_notation_r_map f)

  let and_short_name_map m f (x, l) =
    let+ x = f x
    and+ l = option_map (mcast m m.variable) l >>= m.short_name in
    (x, l)

  let union_map f g = function
    | Inl x -> let+ x = f x in Inl x
    | Inr x -> let+ x = g x in Inr x

  let glob_red_flag_map f ({ rConst; _ } as flag) =
    let+ rConst = List.map f rConst in
    { flag with rConst }

  let red_expr_gen_map m f g h = function
    | Simpl (flg, x) ->
      let+ flg = glob_red_flag_map g flg
      and+ x = option_map (fun (oc, x) ->
          let+ oc = occurrences_expr_map m oc
          and+ x = union_map g h x in
          (oc, x)) x in
      Simpl (flg, x)
    | Cbv flg ->
      let+ flg = glob_red_flag_map g flg in
      Cbv flg
    | Cbn flg ->
      let+ flg = glob_red_flag_map g flg in
      Cbn flg
    | Lazy flg ->
      let+ flg = glob_red_flag_map g flg in
      Lazy flg
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
          let+ oc = occurrences_expr_map m oc
          and+ x = union_map g h x in
          (oc, x)) x in
      CbvVm x
    | CbvNative x ->
      let+ x = option_map (fun (oc, x) ->
          let+ oc = occurrences_expr_map m oc
          and+ x = union_map g h x in
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
      (* Tactic `context`, not the construct in a match, and therefore a variable and not a binder *)
      let+ id = mcast m m.variable id
      and+ t = f t in
      ConstrContext (id, t)
    | ConstrTypeOf t ->
      let+ t = f t in
      ConstrTypeOf t

  let evaluable_global_reference_map m = function
    | EvalConstRef c ->
      let+ c = m.constant c in
      EvalConstRef c
    | EvalVarRef id ->
      let+ id = m.variable id in
      EvalVarRef id

  let glob_sort_name_map m = function
    | GType li ->
      let+ li = m.cast @@ return li in
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
    | VarRef id ->
      let+ id = m.variable id in
      VarRef id
    | ConstRef c ->
      let+ c = m.constant c in
      ConstRef c
    | IndRef (c, i) ->
      let+ c = m.mutind c in
      IndRef (c, i)
    | ConstructRef ((c, i), j) ->
      let+ c = m.mutind c in
      ConstructRef ((c, i), j)

  let goal_select_map m = function
    | SelectId id ->
      let+ id = m.variable id in
      SelectId id
    | x -> return x

  let message_token_map f = function
    | MsgIdent id ->
      let+ id = f id in MsgIdent id
    | x -> return x

  let glob_level_map m = glob_sort_expr_map (glob_sort_name_map m)

  type 'a tactic_mapper = {
    tactic_map   : 'tacexpr map;
    generic_map  : 'lev generic_argument map;
    trm_map      : 'trm map;
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
     | GVar id ->
       let+ id = m.variable id in
       GVar id
     | GEvar (e, xs) ->
       (* We do not see existential variables as variables
          Also, we leave the ids of their foreign context alone *)
       let+ xs = List.map (fun (l, c) ->
           let+ c = glob_constr_map c in
           (l, c)) xs in
       GEvar (e, xs)
     | GPatVar _ as c -> return c (* Not regarded as a variable *)
     | GApp (c, cs) ->
       let+ c = glob_constr_map c
       and+ cs = List.map glob_constr_map cs in
       GApp (c, cs)
     | GLambda (id, bk, typ, term) ->
       let+ typ = glob_constr_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term glob_constr_map in
       GLambda (name_id_map id_f id, bk, typ, term)
     | GProd (id, bk, typ, term) ->
       let+ typ = glob_constr_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term glob_constr_map in
       GProd (name_id_map id_f id, bk, typ, term)
     | GLetIn (id, b, typ, term) ->
       let+ b = glob_constr_map b
       and+ typ = option_map glob_constr_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term glob_constr_map in
       GLetIn (name_id_map id_f id, b, typ, term)
     | GCases (cs, c, tt, cc) ->
       let bndrs = OList.concat @@ OList.map (fun (_, (id, pp)) ->
           let bndrs = Option.cata (fun CAst.{v=(_, bndrs); _} -> bndrs) [] pp in
           filter_placeholders (id::bndrs))
           tt in
       let+ c = option_map (fun c ->
           let+ ids_f, c = with_binders bndrs c glob_constr_map in
           (* Binders should not and cannot be changed here *)
           OList.iter (fun id -> assert (Id.equal id @@ ids_f id)) bndrs;
           c) c
       and+ tt = List.map (fun (c, (n, pp)) ->
           let+ c = glob_constr_map c
           and+ pp = option_map
               (fun x -> mcast m (fun ((i, j), nls) ->
                                 let+ i = m.mutind i in (i, j), nls) x) pp in
           (c, (n, pp))) tt
       and+ cc = List.map (mcast m (fun (ids, cps, c) ->
           (* TODO: It might be that `ids` is all the variables in `cps`, but this is
              unclear from the description in Glob_terms. There it says `ids` is all free variables of `c` *)
           let* cps = List.map (cases_pattern_g_map m) cps in
           let cps, bndrs = OList.split cps in
           let+ ids_f, c = with_binders (filter_placeholders @@ OList.concat bndrs) c glob_constr_map in
           (OList.map ids_f ids, cps, c))) cc in
       GCases (cs, c, tt, cc)
     | GLetTuple (ids, (id, c1), c2, c3) ->
       let bndrs = filter_placeholders (id :: ids) in
       let+ c1 = option_map glob_constr_map c1
       and+ c2 = glob_constr_map c2
       and+ ids_f, c3 = with_binders bndrs c3 glob_constr_map in
       GLetTuple (OList.map (name_id_map ids_f) ids, (name_id_map ids_f id, c1), c2, c3)
     | GIf (c1, (id, c2), c3, c4) ->
       let bndrs = filter_placeholders [id] in
       let+ c1 = glob_constr_map c1
       and+ c2 = option_map (fun c2 -> with_binders bndrs c2 glob_constr_map) c2
       and+ c3 = glob_constr_map c3
       and+ c4 = glob_constr_map c4 in
       let id = Option.default id @@ Option.map (fun (id_f, _) -> name_id_map id_f id) c2 in
       let c2 = Option.map snd c2 in
       GIf (c1, (id, c2), c3, c4)
     | GRec (fk, ids, decls, typs, terms) ->
       let+ typs = array_map glob_constr_map typs
       and+ terms = array_map (fun (dec, (t, decls)) ->
           let bndrs = filter_placeholders @@ OList.map (fun (id, _, _, _) -> id) decls in
           let* ids_f, t = with_binders bndrs t glob_constr_map in
           let+ decls = List.map (fun (id, bk, c1, c2) ->
               let+ c1 = option_map glob_constr_map c1
               and+ c2 = glob_constr_map c2 in
               name_id_map ids_f id, bk, c1, c2) decls in
           ids_f dec, (t, decls))
           (array_combine ids (array_combine terms decls)) in
       let ids, terms = array_split terms in
       let terms, decls = array_split terms in
       GRec (fk, ids, decls, typs, terms)
     | GSort _ as c -> return c
     | GHole (k, intr, gen) ->
       (* TODO: Sometime we have to deal with some of these evar kinds *)
       let+ gen = option_map (generic_glob_map (r m)) gen
       and+ intr = intro_pattern_naming_expr_map m intr in
       GHole (k, intr, gen)
     | GCast (c1, c2) ->
       let+ c1 = glob_constr_map c1
       and+ c2 = cast_type_map glob_constr_map c2 in
       GCast (c1, c2)
     | GInt _ as c -> return c
     | GFloat _ as c -> return c
  and glob_constr_map m r c = mdast m (glob_constr_r_map m r) c

  let explicitation_map m = function
    | ExplByPos (i, id) ->
      let+ id = option_map m.variable id in
      ExplByPos (i, id)
    | ExplByName id ->
      let+ id = m.variable id in
      ExplByName id

  let rec cases_pattern_expr_r_map m r (case : cases_pattern_expr_r) =
    let cases_pattern_expr_map = cases_pattern_expr_map m r in
    match case with
    | CPatAlias (ca, l) ->
      let+ ca, bndrs = cases_pattern_expr_map ca
      and+ l = m.cast @@ return l in
      CPatAlias (ca, l), l::bndrs
    | CPatCstr (id, cas1, cas2) ->
      let+ id = m.cast @@ return id (* not a variable *)
      and+ cas1 = option_map (List.map cases_pattern_expr_map) cas1
      and+ cas2 = List.map (cases_pattern_expr_map) cas2 in
      let cas1, bndrs1 = Option.cata (fun cas1 ->
          let a, b = OList.split cas1 in Some a, b) (None, []) cas1 in
      let cas2, bndrs2 = OList.split cas2 in
      CPatCstr (id, cas1, cas2), OList.concat (bndrs1@bndrs2)
    | CPatAtom l ->
      (* TODO: I would expect this to always be a binder, since CPatCstr already handles
         constructors. However, sinse this is a qualid, this assumption is clearly faulty,
         and what I do here is likely wrong. Most likely, it is dependent on the context
         whether or not this is a binder *)
      let bndr = Option.cata (fun qu ->
          let dp, id = Libnames.repr_qualid qu in
          if DirPath.is_empty dp then [CAst.make (Name.Name id)] else []
        ) [] l in
      let+ l = option_map (qualid_map m) l in
      CPatAtom l, bndr
    | CPatOr pas ->
      let+ pas = List.map cases_pattern_expr_map pas in
      let pas, bndrs = OList.split pas in
      CPatOr pas, OList.concat bndrs
    | CPatNotation (ns, (cas1, cas2), cas3) ->
      let+ cas1 = List.map cases_pattern_expr_map cas1
      and+ cas2 = List.map (List.map cases_pattern_expr_map) cas2
      and+ cas3 = List.map cases_pattern_expr_map cas3 in
      let cas1, bndrs1 = OList.split cas1 in
      let cas2, bndrs2 = OList.split (OList.map OList.split cas2) in
      let cas3, bndrs3 = OList.split cas3 in
      CPatNotation (ns, (cas1, cas2), cas3), OList.concat (bndrs1 @ OList.concat bndrs2 @ bndrs3)
    | CPatPrim _ -> return (case, [])
    | CPatRecord xs ->
      let+ xs = List.map (fun (qu, ca) ->
          let+ qu = m.cast @@ return qu (* not a variable *)
          and+ ca,bndrs = cases_pattern_expr_map ca in
          (qu, ca), bndrs) xs in
      let xs, bndrs = OList.split xs in
      CPatRecord xs, OList.concat bndrs
    | CPatDelimiters (d, c) ->
      let+ c, bndrs = cases_pattern_expr_map c in
      CPatDelimiters (d, c), bndrs
    | CPatCast (c1, c2) ->
      let+ c1,bndrs = cases_pattern_expr_map c1
      and+ c2 = constr_expr_map m r c2 in
      CPatCast (c1, c2), bndrs
  and cases_pattern_expr_map m r c =
    let+ CAst.{loc; v=(c,bndrs)} = mcast m (cases_pattern_expr_r_map m r) c in
    CAst.make ?loc c, bndrs
  and constr_expr_r_map m (r : mapper -> recursor) (c' : constr_expr_r) =
    let constr_expr_map = constr_expr_map m r in
    m.constr_expr c' @@ function
    | CRef (qu, i) ->
      let+ qu = qualid_map m qu in
      CRef (qu, i)
    | CFix (li, fix) -> (* li represents the final choice of the cofixpoints, and is not a binder *)
      let bnds = OList.map (fun (id, _, _, _, _) -> CAst.(id.v)) fix in
      let+ li = m.cast @@ return li
      and+ fix = List.map (fix_expr_map bnds m r) fix in
      CFix (li, fix)
    | CCoFix (li, cofix) -> (* li represents the final choice of the cofixpoints, and is not a binder *)
      let bnds = OList.map (fun (id, _, _, _) -> CAst.(id.v)) cofix in
     let+ li = m.cast @@ return li
     and+ cofix = List.map (cofix_expr_map bnds m r) cofix in
     CCoFix (li, cofix)
    | CProdN (lb, c) ->
      let* lb = List.map (local_binder_expr_map m r) lb in
      let lb, bnds = OList.split lb in
      let+ ids_f, c = with_binders (OList.concat bnds) c constr_expr_map in
      CProdN (OList.map (local_binder_expr_id_map ids_f) lb, c)
    | CLambdaN (lb, c) ->
      let* lb = List.map (local_binder_expr_map m r) lb in
      let lb, bnds = OList.split lb in
      let+ ids_f, c = with_binders (OList.concat bnds) c constr_expr_map in
      CLambdaN (OList.map (local_binder_expr_id_map ids_f) lb, c)
    | CLetIn (l, b, typ, term) ->
      let* b = constr_expr_map b
      and+ typ = option_map constr_expr_map typ
      and+ id_f, term = with_binders (filter_lnames [l]) term constr_expr_map in
      let+ l = mcast m (fun id -> return (name_id_map id_f id)) l in
      CLetIn (l, b, typ, term)
    | CAppExpl ((flg, l, ie), cs) ->
      let+ l = qualid_map m l
      and+ cs = List.map constr_expr_map cs in
      CAppExpl ((flg, l, ie), cs)
    | CApp ((flg, c), cs) ->
      let+ c = constr_expr_map c
      and+ cs = List.map (fun (c, e) ->
          let+ c = constr_expr_map c
          and+ e = option_map (mcast m (explicitation_map m)) e in
          (c,e)) cs in
      CApp ((flg, c), cs)
    | CRecord xs ->
      let+ xs = List.map (fun (l, c) ->
        let+ l = qualid_map m l
        and+ c = constr_expr_map c in
        (l, c)) xs in
      CRecord xs
    | CCases (sty, c1, cs, bs) ->
      let* cs = List.map (fun (c, l, pat) ->
          let+ c = constr_expr_map c
          and+ l = option_map (fun x -> m.cast @@ return x) l
          and+ pat = option_map (cases_pattern_expr_map m r) pat in
          let l' = Option.cata (fun x -> [x]) [] l in
          let pat,bndrs = Option.cata (fun (pat, bndrs) -> Some pat, bndrs) (None, []) pat in
          (c, l, pat), l'@bndrs) cs in
      let cs,bndrs = OList.split cs in
      let+ c1 = option_map (fun c1 ->
          with_binders (filter_lnames @@ OList.concat bndrs) c1 constr_expr_map) c1
      and+ bs = List.map (mcast m (fun (cs, c) ->
          let* cs = List.map (List.map (cases_pattern_expr_map m r)) cs in
          let cs, bndrs = OList.split @@ OList.map OList.split cs in
          let+ ids_f, c = with_binders (filter_lnames @@ OList.concat @@ OList.concat bndrs) c constr_expr_map in
          let cs = OList.map (OList.map (cases_pattern_expr_id_map ids_f)) cs in
          cs, c)) bs in
      let cs = Option.default cs @@ Option.map (fun (ids_f, _) ->
          OList.map (fun (c, l, pat) ->
              c, Option.map (CAst.map (name_id_map ids_f)) l,
              Option.map (cases_pattern_expr_id_map ids_f) pat) cs
        ) c1 in
      let c1 = Option.map snd c1 in
      CCases (sty, c1, cs, bs)
    | CLetTuple (ls, (l, c1), c2, c3) ->
      let+ ls = List.map (fun x -> m.cast @@ return x) ls
      and+ l, c1 =
        let bndrs = filter_lnames (Option.cata (fun id -> [id]) [] l @ ls) in
        let+ c1 = option_map (fun c1 -> with_binders bndrs c1 constr_expr_map) c1 in
        let l = Option.map (fun l -> Option.default l @@
                             Option.map (fun (f, _) -> CAst.map (fun l -> name_id_map f l) l) c1) l in
        l, Option.map snd c1
      and+ c2 = constr_expr_map c2
      and+ id_f, c3 =
        let bndrs = filter_lnames ls in
        with_binders bndrs c3 constr_expr_map in
      CLetTuple (OList.map (CAst.map (name_id_map id_f)) ls, (l, c1), c2, c3)
    | CIf (c1, (l, c2), c3, c4) ->
      let bndrs = Option.cata (fun l -> [CAst.(l.v)]) [] l in
      let+ l = option_map (fun x -> m.cast @@ return x) l
      and+ c1 = constr_expr_map c1
      and+ c2 = option_map (fun c2 -> with_binders (filter_placeholders bndrs) c2 constr_expr_map) c2
      and+ c3 = constr_expr_map c3
      and+ c4 = constr_expr_map c4 in
      let l = Option.map (fun l -> Option.default l @@
                           Option.map (fun (f, _) -> CAst.map (fun l -> name_id_map f l) l) c2) l in
      let c2 = Option.map snd c2 in
      CIf (c1, (l, c2), c3, c4)
    | CHole (k, intr, gen) ->
      (* TODO: At some point we have to deal with some of these evar kinds *)
      let+ intr = intro_pattern_naming_expr_map m intr
      and+ gen = option_map (generic_raw_map (r m)) gen in
      CHole (k, intr, gen)
    | CPatVar _ as x -> (* Not regarded as a variable*)
      return x
    | CEvar (e, xs) ->
      (* We do not see existential variables as variables
         Also, we leave the ids of their foreign context alone *)
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
      (* TODO: Having the binders in the right location here seems very complicated *)
      let+ cs1 = List.map constr_expr_map cs1
      and+ cs2 = List.map (List.map constr_expr_map) cs2
      and+ ps = List.map (cases_pattern_expr_map m r) ps
      and+ bs = List.map (List.map (local_binder_expr_map m r)) bs in
      let ps, _ = OList.split ps in
      let bs, _ = OList.split (OList.map OList.split bs) in
      CNotation (ns, (cs1, cs2, ps, bs))
    | CGeneralization (bk, ak, c) ->
      let+ c = constr_expr_map c in
      CGeneralization (bk, ak, c)
    | CPrim _ as c -> return c
    | CDelimiters (str, c) ->
     let+ c = constr_expr_map c in
     CDelimiters (str, c)
  and fix_expr_map bnds m r (li, ord, bi, typ, term) =
    let* li = m.cast @@ return li
    (* TODO: The recursion annotation needs to be mapped with binders somehow *)
    and+ ord = option_map (recursion_order_expr m r) ord
    and+ bi = List.map (local_binder_expr_map m r) bi in
    let bi,bnds' = OList.split bi in
    let+ typ = constr_expr_map m r typ
    and+ ids_f, term = with_binders (OList.concat bnds' @ bnds) term @@ constr_expr_map m r in
    let li = CAst.map ids_f li in
    let bi = OList.map (local_binder_expr_id_map ids_f) bi in
    (li, ord, bi, typ, term)
  and cofix_expr_map bnds m r (li, bi, typ, term) =
    let* li = m.cast @@ return li
    and+ bi = List.map (local_binder_expr_map m r) bi in
    let bi,bnds' = OList.split bi in
    let+ typ = constr_expr_map m r typ
    and+ ids_f, term = with_binders (OList.concat bnds' @ bnds) term @@ constr_expr_map m r in
    let li = CAst.map ids_f li in
    let bi = OList.map (local_binder_expr_id_map ids_f) bi in
    (li, bi, typ, term)
  and local_binder_expr_map m r : local_binder_expr -> (local_binder_expr * Id.t list) t = function
    | CLocalAssum (lis, bk, c) ->
      let+ lis = List.map (fun x -> m.cast @@ return x) lis
      and+ c = constr_expr_map m r c in
      CLocalAssum (lis, bk, c), filter_lnames lis
    | CLocalDef (li, c1, c2) ->
      let+ li = m.cast @@ return li
      and+ c1 = constr_expr_map m r c1
      and+ c2 = option_map (constr_expr_map m r) c2 in
      CLocalDef (li, c1, c2), filter_lnames [li]
    | CLocalPattern CAst.{loc; v=(ca, c)} ->
      let+ CAst.{loc; v=(x, bndrs)} = m.cast (
        let+ ca,bndrs = cases_pattern_expr_map m r ca
        and+ c = option_map (constr_expr_map m r) c in
        CAst.make ?loc ((ca, c), bndrs)) in
      CLocalPattern (CAst.make ?loc x), filter_lnames bndrs
  and recursion_order_expr_r m r = function
    | CStructRec li ->
      let+ li = mcast m m.variable li in
      CStructRec li
    | CWfRec (li, c) ->
      let+ li = mcast m m.variable li
      and+ c = constr_expr_map m r c in
      CWfRec (li, c)
    | CMeasureRec (li, c1, c2) ->
      let+ li = option_map (mcast m m.variable) li
      and+ c1 = constr_expr_map m r c1
      and+ c2 = option_map (constr_expr_map m r) c2 in
      CMeasureRec (li, c1, c2)
  and recursion_order_expr m r x = mcast m (recursion_order_expr_r m r) x
  and constr_expr_map (m : mapper) r c : constr_expr t =
    mcast m (constr_expr_r_map m r) c

  and constr_pattern_map m pat' =
    let constr_pattern_map = constr_pattern_map m in
    m.constr_pattern pat' @@ function
     | PRef r ->
       let+ r = globref_map m r in
       PRef r
     | PVar id ->
       let+ id = m.variable id in
       PVar id
     | PEvar (e, ps) -> (* TODO: at some point we should do something with evars *)
       let+ ps = array_map constr_pattern_map ps in
       PEvar (e, ps)
     | PRel _ as pat -> (* TODO: Look up this variable *)
       return pat
     | PApp (p, ps) ->
       let+ p = constr_pattern_map p
       and+ ps = array_map constr_pattern_map ps in
       PApp (p, ps)
     | PSoApp (id, ps) -> (* TODO: This seems to be an existential variable *)
       let+ ps = List.map constr_pattern_map ps in
       PSoApp (id, ps)
     | PProj (id, p) ->
       let+ p = constr_pattern_map p in
       PProj (id, p)
     | PLambda (id, typ, term) ->
       let+ typ = constr_pattern_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term constr_pattern_map in
       PLambda (name_id_map id_f id, typ, term)
     | PProd (id, typ, term) ->
       let+ typ = constr_pattern_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term constr_pattern_map in
       PProd (name_id_map id_f id, typ, term)
     | PLetIn (id, bi, typ, term) ->
       let+ bi = constr_pattern_map bi
       and+ typ = option_map constr_pattern_map typ
       and+ id_f, term = with_binders (filter_placeholders [id]) term constr_pattern_map in
       PLetIn (name_id_map id_f id, bi, typ, term)
     | PSort _ as pat -> return pat
     | PMeta _ as pat -> (* TODO: Meta-existential variable *)
       return pat
     | PIf (p1, p2, p3) ->
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2
       and+ p3 = constr_pattern_map p3 in
       PIf (p1, p2, p3)
     | PCase (ci, p1, p2, ps) -> (* TODO: Probably some implicit de Bruijn indices here *)
       let+ p1 = constr_pattern_map p1
       and+ p2 = constr_pattern_map p2
       and+ ps = List.map (fun (i, bs, p) ->
           let+ p = constr_pattern_map p in
           (i, bs, p)) ps in
       PCase (ci, p1, p2, ps)
     | PFix (x, (ids, typs, terms)) ->
       let fids = filter_placeholders @@ Array.to_list ids in
       let+ typs = array_map constr_pattern_map typs
       and+ ids_f, terms = with_binders fids terms @@ array_map constr_pattern_map in
       PFix (x, (Array.map (name_id_map ids_f) ids, typs, terms))
     | PCoFix (i, (ids, typs, terms)) ->
       let fids = filter_placeholders @@ Array.to_list ids in
       let+ typs = array_map constr_pattern_map typs
       and+ ids_f, terms = with_binders fids terms @@ array_map constr_pattern_map in
       PCoFix (i, (Array.map (name_id_map ids_f) ids, typs, terms))
     | PInt _ as pat -> return pat
     | PFloat _ as pat -> return pat

  and glob_constr_and_expr_map m r (trm : g_trm) =
    m.glob_constr_and_expr trm @@ function (gc, ce) ->
    let+ gc = glob_constr_map m r gc
    and+ ce = option_map (constr_expr_map m r) ce in
    (gc, ce)
  and g_pat_map m r (pat : g_pat) =
    (* TODO: `ids` are variables, but unknown if binders. They do not appear to be used, so we ignore *)
    m.glob_constr_pattern_and_expr pat @@ function (ids, c, cp) ->
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
     | TacFreshId ids ->
       let+ ids = List.map (or_var_map m.u id) ids in
       TacFreshId ids
     | Tacexp t ->
       let+ t = m.tactic_map t in
       Tacexp t
     | TacPretype t ->
       let+ t = m.trm_map t in
       TacPretype t
     | TacNumgoals as tac -> return tac
  and match_rule_map (m : 'a tactic_mapper) tac = List.map (function
      | Pat (hyps, pat, t) ->
        let* hyps = List.map (match_context_hyps_map m.u m.pat_map) hyps
        and+ pat,bnds2 = match_pattern_map m.pat_map pat in
        let hyps,bnds1 = OList.split hyps in
        let bnds = OList.concat bnds1 @ bnds2 in
        let+ ids_f, t = with_binders bnds t m.tactic_map in
        Pat (OList.map (match_context_hyps_id_map ids_f) hyps, match_pattern_id_map ids_f pat, t)
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
           let+ l = mcast m.u m.u.variable l
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
       let+ id = m.u.variable id
       and+ fs = List.map (fun (id, n, c) ->
           let+ id = m.u.variable id
           and+ c = m.trm_map c in
           (id, n, c)) fs in
       TacMutualFix (id, n, fs)
     | TacMutualCofix (id, fs) ->
       let+ id = m.u.variable id
       and+ fs = List.map (fun (id, c) ->
           let+ id = m.u.variable id
           and+ c = m.trm_map c in
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
           and+ c = m.trm_map c
           and+ id = name_map m.u id in (* This is not a binder *)
           ((oe, c), id)) xs in
       TacGeneralize xs
     | TacLetTac (flg1, id, c, cl, flg2, intro) ->
       let+ id = name_map m.u id
       and+ c = m.trm_map c
       and+ cl = clause_expr_map m.u (mcast m.u m.u.variable) cl
       and+ intro = option_map (mcast m.u (intro_pattern_naming_expr_map m.u)) intro in
       TacLetTac (flg1, id, c, cl, flg2, intro)
     | TacInductionDestruct (flg1, flg2, (indc, c)) ->
       let+ indc = List.map (induction_clause_map m.u m.trm_map (mcast m.u m.u.variable)) indc
       and+ c = option_map (with_bindings_map m.u m.trm_map) c in
       TacInductionDestruct (flg1, flg2, (indc, c))
     | TacReduce (rede, cl) ->
       let+ rede = red_expr_gen_map m.u m.trm_map m.cst_map m.pat_map rede
       and+ cl = clause_expr_map m.u (mcast m.u m.u.variable) cl in
       TacReduce (rede, cl)
     | TacChange (flg, pat, c, cl) ->
       let+ pat = option_map m.pat_map pat
       and+ c = m.trm_map c
       and+ cl = clause_expr_map m.u (mcast m.u m.u.variable) cl in
       TacChange (flg, pat, c, cl)
     | TacRewrite (flg1, bis, cl, t) ->
       let+ bis = List.map (fun (flg, mu, bi) ->
           let+ bi = with_bindings_arg_map m.u m.trm_map bi in
           (flg, mu, bi)) bis
       and+ cl = clause_expr_map m.u (mcast m.u m.u.variable) cl
       and+ t = option_map m.tactic_map t in
       TacRewrite (flg1, bis, cl, t)
     | TacInversion (is, qh) ->
       let+ is = inversion_strength_map m.u m.trm_map m.trm_map (mcast m.u m.u.variable) is
       and+ qh = quantified_hypothesis_map m.u qh in
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
       let+ t = m.tactic_map t
       and+ id = option_map m.u.variable id in
       TacAbstract (t, id)
     | TacId msgs ->
       let+ msgs = List.map (fun x ->
           message_token_map m.nam_map x) msgs in
       TacId msgs
     | TacFail (flg, l, msgs) ->
       let+ msgs = List.map (fun x ->
           message_token_map m.nam_map x) msgs
       and+ l = or_var_map m.u id l in
       TacFail (flg, l, msgs)
     | TacLetIn (flg, ts, t) ->
       let lns, args = OList.split ts in
       let+ ids_f, t = with_binders (filter_lnames lns) t m.tactic_map
       and+ args = List.map (tactic_arg_map m) args in
       TacLetIn (flg, OList.combine (OList.map (CAst.map (name_id_map ids_f)) lns) args, t)
     | TacMatch (flg, t, ts) ->
       let+ t = m.tactic_map t
       and+ ts = (match_rule_map m) ts in
       TacMatch (flg, t, ts)
     | TacMatchGoal (flg, d, ts) ->
       let+ ts = (match_rule_map m) ts in
       TacMatchGoal (flg, d, ts)
     | TacFun (args, t) ->
       let bnds = filter_placeholders args in
       let+ ids_f, t = with_binders bnds t m.tactic_map in
       TacFun (OList.map (name_id_map ids_f) args, t)
     | TacArg c ->
       let+ c = mcast m.u (fun a -> (tactic_arg_map m) a) c in
       TacArg c
     | TacSelect (i, t) ->
       let+ t = m.tactic_map t
       and+ i = goal_select_map m.u i in
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
    ; glob_constr_pattern_and_expr_map = g_pat_map m recursor
    ; bindings_map = (fun f -> bindings_map m f)
    ; with_bindings_map = (fun f -> with_bindings_map m f)
    ; located_map = (fun f -> located_map m f)
    ; variable_map = m.variable
    ; clause_expr_map = (fun f -> clause_expr_map m f)
    ; destruction_arg_map = (fun f -> destruction_arg_map m f)
    ; raw_tactic_expr_map = raw_tactic_expr_map m
    ; glob_tactic_expr_map = glob_tactic_expr_map m
    ; qualid_map = qualid_map m
    ; globref_map = globref_map m
    ; quantified_hypothesis_map = quantified_hypothesis_map m
    ; red_expr_gen_map = (fun f g h -> red_expr_gen_map m f g h)
    }
  and raw_tactic_mapper m = {
    tactic_map   = raw_tactic_expr_map m;
    trm_map      = constr_expr_map m recursor;
    pat_map      = constr_expr_map m recursor;
    ref_map      = qualid_map m;
    nam_map      = mcast m m.variable;
    cst_map      = or_by_notation_map m (fun x -> m.cast @@ return x);
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
    pat_map      = g_pat_map m recursor;
    ref_map      = or_var_map m (fun x -> m.located @@ return x);
    nam_map      = mcast m m.variable;
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
