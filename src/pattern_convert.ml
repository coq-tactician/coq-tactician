open Pattern_functor

module O = Pattern

let constr_pattern_to_constr_pattern (t : O.constr_pattern) : constr_pattern =
  (* These functions only exist to verify that the two `constr_expr` types are isomorphic *)
  let rec constr_pattern_r_to_constr_pattern_r (t : O.constr_pattern) : 'a constr_pattern_r =
    let r = constr_pattern_r_to_constr_pattern_r in
    match t with
    | O.PRef a ->
      PRef a
    | O.PVar v ->
      PVar v
    | O.PEvar (a, b) ->
      PEvar (a, Array.map r b)
    | O.PRel a ->
      PRel a
    | O.PApp (a, b) ->
      PApp (r a, Array.map r b)
    | O.PSoApp (a, b) ->
      PSoApp (a, List.map r b)
    | O.PProj (a, b) ->
      PProj (a, r b)
    | O.PLambda (a, b, c) ->
      PLambda (a, r b, r c)
    | O.PProd (a, b, c) ->
      PProd (a, r b, r c)
    | O.PLetIn (a, b, c, d) ->
      PLetIn (a, r b, Option.map r c, r d)
    | O.PSort a ->
      PSort a
    | O.PMeta a ->
      PMeta a
    | O.PIf (a, b, c) ->
      PIf (r a, r b, r c)
    | O.PCase (a, b, c, d) ->
      PCase (a, r b, r c, List.map (fun (a, b, c) -> a, b, r c) d)
    | O.PFix (a, (b, c, d)) ->
      PFix (a, (b, Array.map r c, Array.map r d))
    | O.PCoFix (a, (b, c, d)) ->
      PCoFix (a, (b, Array.map r c, Array.map r d))
    | O.PInt a ->
      PInt a
    | O.PFloat a ->
      PFloat a in
  let convert_slowly () = constr_pattern_r_to_constr_pattern_r t
  [@@ocaml.warning "-26"]

  (* Dangerous black magic to speed things up *)
  in Obj.magic t

let constr_pattern_to_constr_pattern2 (t : constr_pattern) : O.constr_pattern =
  (* These functions only exist to verify that the two `constr_expr` types are isomorphic *)
  let rec constr_pattern_r_to_constr_pattern_r (t : 'a constr_pattern_r) : O.constr_pattern =
    let r = constr_pattern_r_to_constr_pattern_r in
    match t with
    | PRef a ->
      O.PRef a
    | PVar v ->
      O.PVar v
    | PEvar (a, b) ->
      O.PEvar (a, Array.map r b)
    | PRel a ->
      O.PRel a
    | PApp (a, b) ->
      O.PApp (r a, Array.map r b)
    | PSoApp (a, b) ->
      O.PSoApp (a, List.map r b)
    | PProj (a, b) ->
      O.PProj (a, r b)
    | PLambda (a, b, c) ->
      O.PLambda (a, r b, r c)
    | PProd (a, b, c) ->
      O.PProd (a, r b, r c)
    | PLetIn (a, b, c, d) ->
      O.PLetIn (a, r b, Option.map r c, r d)
    | PSort a ->
      O.PSort a
    | PMeta a ->
      O.PMeta a
    | PIf (a, b, c) ->
      O.PIf (r a, r b, r c)
    | PCase (a, b, c, d) ->
      O.PCase (a, r b, r c, List.map (fun (a, b, c) -> a, b, r c) d)
    | PFix (a, (b, c, d)) ->
      O.PFix (a, (b, Array.map r c, Array.map r d))
    | PCoFix (a, (b, c, d)) ->
      O.PCoFix (a, (b, Array.map r c, Array.map r d))
    | PInt a ->
      O.PInt a
    | PFloat a ->
      O.PFloat a in
  let convert_slowly () = constr_pattern_r_to_constr_pattern_r t
  [@@ocaml.warning "-26"]

  (* Dangerous black magic to speed things up *)
  in Obj.magic t
