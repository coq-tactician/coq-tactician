open Hh_term

let extract_consts (t : hhterm) : string list =
  let rec pom t acc =
    match t with
    | Id _ ->
      acc
    | Comb(Comb(Id "$Construct", x), Id c)
        (*when
          not (Hhlib.string_begins_with c "Coq.Init.Logic.")*) ->
      pom x (c :: acc)
    | Comb(Id x, Id c)
        when (x = "$Const" || x = "$Ind" || x = "$Var") (*&&
          not (Hhlib.string_begins_with c "Coq.Init.Logic.")*) ->
      (c :: acc)
    | Comb(x, y) ->
      pom y (pom x acc)
    | Abs(_) ->
      failwith "extract_consts"
  in
  List.sort_uniq compare (pom t [])

let rec top_feature = function
  | Comb(Comb(Id "$Construct", _), Id c)
  | Comb(Comb(Id "$Ind", Id c), _)
  | Comb(Id "$Const", Id c)
  | Comb(Id "$Var", Id c) -> c
  | Comb(Id "$Rel", Id _) -> "X"
  | Comb(Comb(Id "$App", t), _) -> top_feature t
  | _ -> ""

let extract_features (t : hhterm) : string list =
  let rec pom t acc =
    match t with
    | Id _ ->
      acc
    | Comb(Comb(Id "$Construct", x), Id c)
        (*when
          not (Hhlib.string_begins_with c "Coq.Init.Logic.")*) ->
      pom x (c :: acc)
    | Comb(Id x, Id c)
        (*when (x = "$Const" || x = "$Ind" || x = "$Var") &&
          not (Hhlib.string_begins_with c "Coq.Init.Logic.")*) ->
      (c :: acc)
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id c)), args)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id c), _)), args)
    | Comb(Comb(Id "$App", Comb(Id "$Var", Id c)), args)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Construct", _), Id c)), args) ->
      let rec app_fea acc = function
      | Id "$ConstrArray" -> acc
      | Comb(moreargs, arg) ->
         begin match top_feature arg with
         | "" -> app_fea acc moreargs
         | s -> app_fea ((c ^ "-" ^ s) :: acc) moreargs
         end
      | _ -> assert false
      in
      pom args (c :: (app_fea acc args))
    | Comb(x, y) ->
      pom y (pom x acc)
    | Abs(_) ->
      failwith "extract_features"
  in
  List.sort_uniq compare (pom t [])
