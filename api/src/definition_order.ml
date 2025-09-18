open Constr
open Names
open Declarations
open Context

let constr_in_order_traverse acc f g h c =
  let rec aux acc c =
    match Constr.kind c with
    | Var id -> h id acc
    | Const (c, _) -> f c acc
    | Constr.Ind ((m, _), _) -> g m acc
    | Constr.Construct (((m, _), _), _) -> g m acc
    | Constr.Proj (p, _) -> g (Projection.mind p) acc
    | _ -> Constr.fold (fun acc c -> aux acc c) acc c in
  aux acc c

let constant_in_order_traverse env acc f g h c =
  let { const_body; const_type; _ } = Environ.lookup_constant c env in
  let acc = constr_in_order_traverse acc f g h const_type in
  match const_body with
  | Undef _ -> acc
  | Def c -> constr_in_order_traverse acc f g h @@ Mod_subst.force_constr c
  | OpaqueDef c ->
    let c, _ = Opaqueproof.force_proof Library.indirect_accessor (Environ.opaque_tables env) c in
    constr_in_order_traverse acc f g h c
  | Primitive _ -> acc

let mutinductive_in_order_traverse env acc f g h m =
  let ({ mind_params_ctxt; mind_packets; mind_record; _ } as mb) =
    Environ.lookup_mind m env in
  let inds = Array.to_list mind_packets in
  List.fold_left (fun acc ({ mind_user_lc; _ } as ib) ->
      let acc = List.fold_left (fun acc typ -> constr_in_order_traverse acc f g h typ) acc @@
        Array.to_list mind_user_lc in
      let univs = Declareops.inductive_polymorphic_context mb in
      let inst = Univ.make_abstract_instance univs in
      let env = Environ.push_context ~strict:false (Univ.AUContext.repr univs) env in
      let typ = Inductive.type_of_inductive env ((mb, ib), inst) in
      constr_in_order_traverse acc f g h typ
    ) acc inds

let variable_in_order_traverse env acc f g h id =
  match Environ.lookup_named id env with
  | Named.Declaration.LocalAssum (_, typ) ->
    constr_in_order_traverse acc f g h typ
  | Named.Declaration.LocalDef (_, term, typ) ->
    constr_in_order_traverse (constr_in_order_traverse acc f g h term) f g h typ

type accum =
  { seen : GlobRef.Set.t
  ; order : GlobRef.t list }

let order env grs =
  let rec f c ({ seen; _ } as acc) =
    let cr = GlobRef.ConstRef c in
    if GlobRef.Set.mem cr seen || not @@ GlobRef.Set.mem cr grs then acc else
      let { seen; order } = constant_in_order_traverse env acc f g h c in
      { seen = GlobRef.Set.add (GlobRef.ConstRef c) seen; order = cr::order }
  and g m ({ seen; _ } as acc) =
    let mr = GlobRef.IndRef (m, 0) in
    if GlobRef.Set.mem mr seen || not @@ GlobRef.Set.mem mr grs then acc else
      let { seen; order } = mutinductive_in_order_traverse env acc f g h m in
        { seen = GlobRef.Set.add mr seen; order = mr::order }
  and h v ({ seen; _ } as acc) =
    let vr = GlobRef.VarRef v in
    if GlobRef.Set.mem vr seen || not @@ GlobRef.Set.mem vr grs then acc else
      let { seen; order } = variable_in_order_traverse env acc f g h v in
        { seen = GlobRef.Set.add vr seen; order = vr::order } in
  let acc = { seen = GlobRef.Set.empty; order = [] } in
  let { order; _ } = GlobRef.Set.fold (function
      | GlobRef.VarRef v -> h v
      | GlobRef.ConstRef c -> f c
      | GlobRef.IndRef (m, _) -> g m
      | GlobRef.ConstructRef _ -> assert false) grs acc in
  List.rev order
