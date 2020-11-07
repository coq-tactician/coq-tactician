open Names
open Nameops
open Glob_ops

let fold_pattern_with_binders g f v acc = function
  | Pattern.PEvar (_, ar) -> List.fold_right (f v) ar acc
  | Pattern.PApp (t, ar) -> Array.fold_right (f v) ar (f v t acc)
  | Pattern.PSoApp (i, ar) -> List.fold_right (f v) ar acc
  | Pattern.PProj (p, t) -> f v t acc
  | Pattern.PLambda (id, ty, te)
  | Pattern.PProd (id, ty, te) -> f (g id v) te (f v ty acc)
  | Pattern.PLetIn (id, t1, ty, t2) -> f (g id v) t2 (f v t1 (Option.fold_right (f v) ty acc))
  | Pattern.PIf (t1, t2, t3) -> f v t3 (f v t2 (f v t1 acc))
  | Pattern.PCase (i, t1, t2, ls) -> List.fold_right (fun (_, _, t) acc -> f v t acc) ls (f v t2 (f v t1 acc))
  | Pattern.PFix (_, (ids, ar1, ar2))
  | Pattern.PCoFix (_, (ids, ar1, ar2)) -> CErrors.anomaly (Pp.str "Tactician: Fixpoint patterns are buggy")
  | Pattern.PRef _ | Pattern.PVar _ | Pattern.PRel _
  | Pattern.PSort _ | Pattern.PMeta _ | Pattern.PInt _ | Pattern.PFloat _ -> acc
  | Pattern.PArray (ar, t1, t2) -> Array.fold_right (f v) ar (f v t1 (f v t2 acc))

(* Copied from glob_ops.ml *)
let collide_id l id = List.exists (fun (id',id'') -> Id.equal id id' || Id.equal id id'') l
let test_id l id = if collide_id l id then raise UnsoundRenaming
let test_na l na = Name.iter (test_id l) na
let pattern_free_vars p =

  let rec free_vars v p acc = match p with
    | Pattern.PVar id -> if Id.Set.mem id v then acc else Id.Set.add id acc
    | _ -> fold_pattern_with_binders (Name.fold_right Id.Set.add) free_vars v acc p in
  free_vars Id.Set.empty p Id.Set.empty

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

(* Partially from glob_ops.ml *)
let rec pattern_rename_vars l = function
  | Pattern.PVar id -> let id' = rename_var l id in
    Pattern.PVar id'
  | Pattern.PRef (GlobRef.VarRef id) as r ->
    if List.exists (fun (_, id') -> Id.equal id id') l then raise UnsoundRenaming
    else r
  | Pattern.PProd (id, ty, te) ->
    let id',l' = update_subst id l in
    Pattern.PProd (id', pattern_rename_vars l ty, pattern_rename_vars l' te)
  | Pattern.PLambda (id, ty, te) ->
    let id',l' = update_subst id l in
    Pattern.PLambda (id', pattern_rename_vars l ty, pattern_rename_vars l' te)
  | Pattern.PLetIn (id, t1, ty, t2) ->
    let id',l' = update_subst id l in
    Pattern.PLetIn (id', pattern_rename_vars l t1, Option.map (pattern_rename_vars l) ty, pattern_rename_vars l' t2)
  | Pattern.PCase (i, t1, t2, ls) ->
    Pattern.PCase (i, pattern_rename_vars l t1, pattern_rename_vars l t2,
                   List.map (fun (i, ar, t) -> (i, ar, pattern_rename_vars l t)) ls)
  | Pattern.PIf (t1, t2, t3) ->
    Pattern.PIf (pattern_rename_vars l t1, pattern_rename_vars l t2, pattern_rename_vars l t2)
  | Pattern.PFix _ | Pattern.PCoFix _ -> CErrors.anomaly (Pp.str "Tactician: Fixpoint patterns are buggy")
  | Pattern.PApp (t, ar) -> Pattern.PApp (pattern_rename_vars l t, Array.map (pattern_rename_vars l) ar)
  | Pattern.PSoApp (p, ar) -> Pattern.PSoApp (p, List.map (pattern_rename_vars l) ar)
  | Pattern.PProj (n, t) -> Pattern.PProj (n, pattern_rename_vars l t)
  | Pattern.PRef _ | Pattern.PRel _ | Pattern.PSort _ | Pattern.PMeta _ | Pattern.PInt _
  | Pattern.PEvar _ | Pattern.PFloat _ as p -> p
  | Pattern.PArray (ar, t1, t2) ->
    Pattern.PArray (Array.map (pattern_rename_vars l) ar, pattern_rename_vars l t1, pattern_rename_vars l t2)

