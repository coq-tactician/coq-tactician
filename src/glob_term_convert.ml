open Coq_ast_monadic_map
open Glob_term_functor
open Monad_util

module O = Glob_term

module M = Mapper(IdentityMonad)

let ( glob_constr_to_glob_constr
    , cases_pattern_to_cases_pattern ) :
  (O.glob_constr -> glob_constr) *
  (O.cases_pattern -> cases_pattern) =
  (* These functions only exist to verify that the two `glob_constr` types are isomorphic *)
  let rec cases_pattern_r_to_cases_pattern_r (p : 'a O.cases_pattern_r) =
    match p with
    | O.PatVar id ->
      PatVar id
    | O.PatCstr (co, pats, id) ->
      PatCstr (co, List.map cases_pattern_g_to_cases_pattern_g pats, id)
  and cases_pattern_g_to_cases_pattern_g pats =
    M.dast_map cases_pattern_r_to_cases_pattern_r pats
  and glob_constr_r_to_glob_constr_r (t : 'a O.glob_constr_r) : 'b glob_constr_r =
    let r = glob_constr_g_to_glob_constr_g in
    match t with
    | O.GRef (a, b) ->
      GRef (a, b)
    | O.GVar a ->
      GVar a
    | O.GEvar (a, b) ->
      GEvar (a, List.map (fun (id, c) -> id, r c) b)
    | O.GPatVar a ->
      GPatVar a
    | O.GApp (a, b) ->
      GApp (r a, List.map r b)
    | O.GLambda (a, b, c, d) ->
      GLambda (a, b, r c, r d)
    | O.GProd (a, b, c, d) ->
      GProd (a, b, r c, r d)
    | O.GLetIn (a, b, c, d) ->
      GLetIn (a, r b, Option.map r c, r d)
    | O.GCases (a, b, c, d) ->
      GCases (a, Option.map r b, tomatch_tuples_g_to_tomatch_tuples_g c, cases_clauses_g_to_cases_clauses_g d)
    | O.GLetTuple (a, (b, c), d, e) ->
      GLetTuple (a, (b, Option.map r c), r d, r e)
    | O.GIf (a, (b, c), d, e) ->
      GIf (r a, (b, Option.map r c), r d, r e)
    | O.GRec (a, b, c, d, e) ->
      GRec (a, b, Array.map (List.map glob_decl_g_to_glob_decl_g) c, Array.map r d, Array.map r e)
    | O.GSort a ->
      GSort a
    | O.GHole (a, b, c) ->
      GHole (a, b, c)
    | O.GCast (a, b) ->
      GCast (r a, M.cast_type_map r b)
    | O.GInt a ->
      GInt a
    | O.GFloat a ->
      GFloat a
  and glob_constr_g_to_glob_constr_g (t : 'a O.glob_constr_g) : glob_constr =
    M.dast_map glob_constr_r_to_glob_constr_r t
  and glob_decl_g_to_glob_decl_g ((id, bk, c1, c2) : 'a O.glob_decl_g) =
    id, bk, M.option_map glob_constr_g_to_glob_constr_g c1, glob_constr_g_to_glob_constr_g c2
  and tomatch_tuple_g_to_tomatch_tuple_g ((c, pat) : 'a O.tomatch_tuple_g) =
    glob_constr_g_to_glob_constr_g c, pat
  and tomatch_tuples_g_to_tomatch_tuples_g (t : 'a O.tomatch_tuples_g) =
    List.map tomatch_tuple_g_to_tomatch_tuple_g t
  and cases_clause_g_to_cases_clause_g (x : 'a O.cases_clause_g) =
    M.cast_map (fun (ids, pats, c) ->
        ids, List.map cases_pattern_g_to_cases_pattern_g pats, glob_constr_g_to_glob_constr_g c) x
  and cases_clauses_g_to_cases_clauses_g (t : 'a O.cases_clauses_g) =
    List.map cases_clause_g_to_cases_clause_g t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = glob_constr_g_to_glob_constr_g t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = cases_pattern_g_to_cases_pattern_g t
     [@@ocaml.warning "-26"]
     in Obj.magic t)

let ( glob_constr_to_glob_constr2
    , cases_pattern_to_cases_pattern2 ) :
  (glob_constr -> O.glob_constr) *
  (cases_pattern -> O.cases_pattern) =
  (* These functions only exist to verify that the two `glob_constr` types are isomorphic *)
  let rec cases_pattern_r_to_cases_pattern_r (p : 'a cases_pattern_r) =
    match p with
    | PatVar id ->
      O.PatVar id
    | PatCstr (co, pats, id) ->
      O.PatCstr (co, List.map cases_pattern_g_to_cases_pattern_g pats, id)
  and cases_pattern_g_to_cases_pattern_g pats =
    M.dast_map cases_pattern_r_to_cases_pattern_r pats
  and glob_constr_r_to_glob_constr_r (t : 'a glob_constr_r) : 'b O.glob_constr_r =
    let r = glob_constr_g_to_glob_constr_g in
    match t with
    | GRef (a, b) ->
      O.GRef (a, b)
    | GVar a ->
      O.GVar a
    | GEvar (a, b) ->
      O.GEvar (a, List.map (fun (id, c) -> id, r c) b)
    | GPatVar a ->
      O.GPatVar a
    | GApp (a, b) ->
      O.GApp (r a, List.map r b)
    | GLambda (a, b, c, d) ->
      O.GLambda (a, b, r c, r d)
    | GProd (a, b, c, d) ->
      O.GProd (a, b, r c, r d)
    | GLetIn (a, b, c, d) ->
      O.GLetIn (a, r b, Option.map r c, r d)
    | GCases (a, b, c, d) ->
      O.GCases (a, Option.map r b, tomatch_tuples_g_to_tomatch_tuples_g c, cases_clauses_g_to_cases_clauses_g d)
    | GLetTuple (a, (b, c), d, e) ->
      O.GLetTuple (a, (b, Option.map r c), r d, r e)
    | GIf (a, (b, c), d, e) ->
      O.GIf (r a, (b, Option.map r c), r d, r e)
    | GRec (a, b, c, d, e) ->
      O.GRec (a, b, Array.map (List.map glob_decl_g_to_glob_decl_g) c, Array.map r d, Array.map r e)
    | GSort a ->
      O.GSort a
    | GHole (a, b, c) ->
      O.GHole (a, b, c)
    | GCast (a, b) ->
      O.GCast (r a, M.cast_type_map r b)
    | GInt a ->
      O.GInt a
    | GFloat a ->
      O.GFloat a
  and glob_constr_g_to_glob_constr_g (t : glob_constr) : 'a O.glob_constr_g =
    M.dast_map glob_constr_r_to_glob_constr_r t
  and glob_decl_g_to_glob_decl_g ((id, bk, c1, c2) : 'a glob_decl_g) =
    id, bk, M.option_map glob_constr_g_to_glob_constr_g c1, glob_constr_g_to_glob_constr_g c2
  and tomatch_tuple_g_to_tomatch_tuple_g ((c, pat) : 'a tomatch_tuple_g) =
    glob_constr_g_to_glob_constr_g c, pat
  and tomatch_tuples_g_to_tomatch_tuples_g (t : 'a tomatch_tuples_g) =
    List.map tomatch_tuple_g_to_tomatch_tuple_g t
  and cases_clause_g_to_cases_clause_g (x : 'a cases_clause_g) =
    M.cast_map (fun (ids, pats, c) ->
        ids, List.map cases_pattern_g_to_cases_pattern_g pats, glob_constr_g_to_glob_constr_g c) x
  and cases_clauses_g_to_cases_clauses_g (t : 'a cases_clauses_g) =
    List.map cases_clause_g_to_cases_clause_g t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = glob_constr_g_to_glob_constr_g t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = cases_pattern_g_to_cases_pattern_g t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
