open Coq_ast_monadic_map
open Constrexpr_functor
open Monad_util

module O = Constrexpr

module M = Mapper(IdentityMonad)

let ( constr_expr_to_constr_expr
    , cases_pattern_expr_to_cases_pattern_expr) :
  (O.constr_expr -> constr_expr) *
  (O.cases_pattern_expr -> cases_pattern_expr) =
  (* These functions only exist to verify that the two `constr_expr` types are isomorphic *)
  let rec cases_pattern_notation_substitution_to_cases_pattern_notation_subsitution
      ((subterms, notations) : O.cases_pattern_notation_substitution) : 'b cases_pattern_notation_substitution =
    List.map cases_pattern_expr_to_cases_pattern_expr subterms, List.map (List.map cases_pattern_expr_to_cases_pattern_expr) notations
  and cases_pattern_expr_r_to_cases_pattern_expr_r (t : O.cases_pattern_expr_r) =
    let r = cases_pattern_expr_to_cases_pattern_expr in
    match t with
    | O.CPatAlias (a, b) ->
      CPatAlias (r a, b)
    | O.CPatCstr (a, b, c) ->
      CPatCstr (a, Option.map (List.map r) b, List.map r c)
    | O.CPatAtom a ->
      CPatAtom a
    | O.CPatOr a ->
      CPatOr (List.map r a)
    | O.CPatNotation (a, b, c) ->
      CPatNotation (a, cases_pattern_notation_substitution_to_cases_pattern_notation_subsitution b, List.map r c)
    | O.CPatPrim a ->
      CPatPrim a
    | O.CPatRecord a ->
      CPatRecord (List.map (fun (a, b) -> a, r b) a)
    | O.CPatDelimiters (a, b) ->
      CPatDelimiters (a, r b)
    | O.CPatCast (a, b) ->
      CPatCast (r a, constr_expr_to_constr_expr b)
  and case_expr_to_case_expr ((a, b, c) : O.case_expr) : 'a case_expr =
    constr_expr_to_constr_expr a, b, Option.map cases_pattern_expr_to_cases_pattern_expr c
  and branch_expr_to_branch_expr (a : O.branch_expr) : 'b branch_expr =
    CAst.map (fun (a, b) -> List.map (List.map cases_pattern_expr_to_cases_pattern_expr) a, constr_expr_to_constr_expr b) a
  and local_binder_expr_to_local_binder_expr (t : O.local_binder_expr) : 'b local_binder_expr = match t with
    | O.CLocalAssum (a, b, c) ->
      CLocalAssum (a, b, constr_expr_to_constr_expr c)
    | O.CLocalDef (a, b, c) ->
      CLocalDef (a, constr_expr_to_constr_expr b, Option.map constr_expr_to_constr_expr c)
    | O.CLocalPattern a ->
      CLocalPattern (CAst.map (fun (a, b) -> cases_pattern_expr_to_cases_pattern_expr a, Option.map constr_expr_to_constr_expr b) a)
  and recursion_order_expr_r_to_recursion_order_expr_r (t : O.recursion_order_expr_r) : 'a recursion_order_expr_r =
    match t with
    | O.CStructRec a ->
      CStructRec a
    | O.CWfRec (a, b) ->
      CWfRec (a, constr_expr_to_constr_expr b)
    | O.CMeasureRec (a, b, c) ->
      CMeasureRec (a, constr_expr_to_constr_expr b, Option.map constr_expr_to_constr_expr c)
  and recursion_order_expr_to_recursion_order_expr (t : O.recursion_order_expr) : 'a recursion_order_expr =
    CAst.map recursion_order_expr_r_to_recursion_order_expr_r t
  and fix_expr_to_fix_expr ((a, b, c, d, e) : O.fix_expr) : 'b fix_expr =
    a, Option.map recursion_order_expr_to_recursion_order_expr b, List.map local_binder_expr_to_local_binder_expr c,
    constr_expr_to_constr_expr d, constr_expr_to_constr_expr e
  and cofix_expr_to_cofix_expr ((a, b, c, d) : O.cofix_expr) : 'b cofix_expr =
    a, List.map local_binder_expr_to_local_binder_expr b, constr_expr_to_constr_expr c, constr_expr_to_constr_expr d
  and constr_notation_substitution_to_constr_notation_substitution ((a, b, c, d) : O.constr_notation_substitution) : 'b constr_notation_substitution =
    List.map constr_expr_to_constr_expr a, List.map (List.map constr_expr_to_constr_expr) b,
    List.map cases_pattern_expr_to_cases_pattern_expr c, List.map (List.map local_binder_expr_to_local_binder_expr) d
  and constr_expr_r_to_constr_expr_r (t : O.constr_expr_r) : 'b constr_expr_r =
    let r = constr_expr_to_constr_expr in
    match t with
    | O.CRef (a, b) ->
      CRef (a, b)
    | O.CFix (a, b) ->
      CFix (a, List.map fix_expr_to_fix_expr b)
    | O.CCoFix (a, b) ->
      CCoFix (a, List.map cofix_expr_to_cofix_expr b)
    | O.CProdN (a, b) ->
      CProdN (List.map local_binder_expr_to_local_binder_expr a, r b)
    | O.CLambdaN (a, b) ->
      CLambdaN (List.map local_binder_expr_to_local_binder_expr a, r b)
    | O.CLetIn (a, b, c, d) ->
      CLetIn (a, r b, Option.map r c, r d)
    | O.CAppExpl (a, b) ->
      CAppExpl (a, List.map r b)
    | O.CApp ((a, b), c) ->
      CApp ((a, r b), List.map (fun (a, b) -> r a, b) c)
    | O.CRecord a ->
      CRecord (List.map (fun (a, b) -> a, r b) a)
    | O.CCases (a, b, c, d) ->
      CCases (a, Option.map r b, List.map case_expr_to_case_expr c, List.map branch_expr_to_branch_expr d)
    | O.CLetTuple (a, (b, c), d, e) ->
      CLetTuple (a, (b, Option.map r c), r d, r e)
    | O.CIf (a, (b, c), d, e) ->
      CIf (r a, (b, Option.map r c), r d, r e)
    | O.CHole (a, b, c) ->
      CHole (a, b, c)
    | O.CPatVar a ->
      CPatVar a
    | O.CEvar (a, b) ->
      CEvar (a, List.map (fun (a, b) -> a, r b) b)
    | O.CSort a ->
      CSort a
    | O.CCast (a, b) ->
      CCast (r a, M.cast_type_map r b)
    | O.CNotation (a, b) ->
      CNotation (a, constr_notation_substitution_to_constr_notation_substitution b)
    | O.CGeneralization (a, b, c) ->
      CGeneralization (a, b, r c)
    | O.CPrim a ->
      CPrim a
    | O.CDelimiters (a, b) ->
      CDelimiters (a, r b)
  and cases_pattern_expr_to_cases_pattern_expr (t : O.cases_pattern_expr) : cases_pattern_expr =
    CAst.map cases_pattern_expr_r_to_cases_pattern_expr_r t
  and constr_expr_to_constr_expr (t : O.constr_expr) : constr_expr =
    CAst.map constr_expr_r_to_constr_expr_r t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = constr_expr_to_constr_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = cases_pattern_expr_to_cases_pattern_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)

let ( constr_expr_to_constr_expr2
    , cases_pattern_expr_to_cases_pattern_expr2) :
  (constr_expr -> O.constr_expr) *
  (cases_pattern_expr -> O.cases_pattern_expr) =
  (* These functions only exist to verify that the two `constr_expr` types are isomorphic *)
  let rec cases_pattern_notation_substitution_to_cases_pattern_notation_subsitution
      ((subterms, notations) : 'b cases_pattern_notation_substitution) : O.cases_pattern_notation_substitution =
    List.map cases_pattern_expr_to_cases_pattern_expr subterms, List.map (List.map cases_pattern_expr_to_cases_pattern_expr) notations
  and cases_pattern_expr_r_to_cases_pattern_expr_r (t : 'b cases_pattern_expr_r) =
    let r = cases_pattern_expr_to_cases_pattern_expr in
    match t with
    | CPatAlias (a, b) ->
      O.CPatAlias (r a, b)
    | CPatCstr (a, b, c) ->
      O.CPatCstr (a, Option.map (List.map r) b, List.map r c)
    | CPatAtom a ->
      O.CPatAtom a
    | CPatOr a ->
      O.CPatOr (List.map r a)
    | CPatNotation (a, b, c) ->
      O.CPatNotation (a, cases_pattern_notation_substitution_to_cases_pattern_notation_subsitution b, List.map r c)
    | CPatPrim a ->
      O.CPatPrim a
    | CPatRecord a ->
      O.CPatRecord (List.map (fun (a, b) -> a, r b) a)
    | CPatDelimiters (a, b) ->
      O.CPatDelimiters (a, r b)
    | CPatCast (a, b) ->
      O.CPatCast (r a, constr_expr_to_constr_expr b)
  and case_expr_to_case_expr ((a, b, c) : 'b case_expr) : O.case_expr =
    constr_expr_to_constr_expr a, b, Option.map cases_pattern_expr_to_cases_pattern_expr c
  and branch_expr_to_branch_expr (a : 'b branch_expr) : O.branch_expr =
    CAst.map (fun (a, b) -> List.map (List.map cases_pattern_expr_to_cases_pattern_expr) a, constr_expr_to_constr_expr b) a
  and local_binder_expr_to_local_binder_expr (t : 'b local_binder_expr) : O.local_binder_expr = match t with
    | CLocalAssum (a, b, c) ->
      O.CLocalAssum (a, b, constr_expr_to_constr_expr c)
    | CLocalDef (a, b, c) ->
      O.CLocalDef (a, constr_expr_to_constr_expr b, Option.map constr_expr_to_constr_expr c)
    | CLocalPattern a ->
      O.CLocalPattern (CAst.map (fun (a, b) -> cases_pattern_expr_to_cases_pattern_expr a, Option.map constr_expr_to_constr_expr b) a)
  and recursion_order_expr_r_to_recursion_order_expr_r (t : 'b recursion_order_expr_r) : O.recursion_order_expr_r =
    match t with
    | CStructRec a ->
      O.CStructRec a
    | CWfRec (a, b) ->
      O.CWfRec (a, constr_expr_to_constr_expr b)
    | CMeasureRec (a, b, c) ->
      O.CMeasureRec (a, constr_expr_to_constr_expr b, Option.map constr_expr_to_constr_expr c)
  and recursion_order_expr_to_recursion_order_expr (t : 'b recursion_order_expr) : O.recursion_order_expr =
    CAst.map recursion_order_expr_r_to_recursion_order_expr_r t
  and fix_expr_to_fix_expr ((a, b, c, d, e) : 'b fix_expr) : O.fix_expr =
    a, Option.map recursion_order_expr_to_recursion_order_expr b, List.map local_binder_expr_to_local_binder_expr c,
    constr_expr_to_constr_expr d, constr_expr_to_constr_expr e
  and cofix_expr_to_cofix_expr ((a, b, c, d) : 'b cofix_expr) : O.cofix_expr =
    a, List.map local_binder_expr_to_local_binder_expr b, constr_expr_to_constr_expr c, constr_expr_to_constr_expr d
  and constr_notation_substitution_to_constr_notation_substitution ((a, b, c, d) : 'b constr_notation_substitution) : O.constr_notation_substitution =
    List.map constr_expr_to_constr_expr a, List.map (List.map constr_expr_to_constr_expr) b,
    List.map cases_pattern_expr_to_cases_pattern_expr c, List.map (List.map local_binder_expr_to_local_binder_expr) d
  and constr_expr_r_to_constr_expr_r (t : 'b constr_expr_r) : O.constr_expr_r =
    let r = constr_expr_to_constr_expr in
    match t with
    | CRef (a, b) ->
      O.CRef (a, b)
    | CFix (a, b) ->
      O.CFix (a, List.map fix_expr_to_fix_expr b)
    | CCoFix (a, b) ->
      O.CCoFix (a, List.map cofix_expr_to_cofix_expr b)
    | CProdN (a, b) ->
      O.CProdN (List.map local_binder_expr_to_local_binder_expr a, r b)
    | CLambdaN (a, b) ->
      O.CLambdaN (List.map local_binder_expr_to_local_binder_expr a, r b)
    | CLetIn (a, b, c, d) ->
      O.CLetIn (a, r b, Option.map r c, r d)
    | CAppExpl (a, b) ->
      O.CAppExpl (a, List.map r b)
    | CApp ((a, b), c) ->
      O.CApp ((a, r b), List.map (fun (a, b) -> r a, b) c)
    | CRecord a ->
      O.CRecord (List.map (fun (a, b) -> a, r b) a)
    | CCases (a, b, c, d) ->
      O.CCases (a, Option.map r b, List.map case_expr_to_case_expr c, List.map branch_expr_to_branch_expr d)
    | CLetTuple (a, (b, c), d, e) ->
      O.CLetTuple (a, (b, Option.map r c), r d, r e)
    | CIf (a, (b, c), d, e) ->
      O.CIf (r a, (b, Option.map r c), r d, r e)
    | CHole (a, b, c) ->
      O.CHole (a, b, c)
    | CPatVar a ->
      O.CPatVar a
    | CEvar (a, b) ->
      O.CEvar (a, List.map (fun (a, b) -> a, r b) b)
    | CSort a ->
      O.CSort a
    | CCast (a, b) ->
      O.CCast (r a, M.cast_type_map r b)
    | CNotation (a, b) ->
      O.CNotation (a, constr_notation_substitution_to_constr_notation_substitution b)
    | CGeneralization (a, b, c) ->
      O.CGeneralization (a, b, r c)
    | CPrim a ->
      O.CPrim a
    | CDelimiters (a, b) ->
      O.CDelimiters (a, r b)
  and cases_pattern_expr_to_cases_pattern_expr (t : cases_pattern_expr) : O.cases_pattern_expr =
    CAst.map cases_pattern_expr_r_to_cases_pattern_expr_r t
  and constr_expr_to_constr_expr (t : constr_expr) : O.constr_expr =
    CAst.map constr_expr_r_to_constr_expr_r t in

  (* Dangerous black magic to speed things up *)
  (fun t ->
     let convert_slowly () = constr_expr_to_constr_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
  ,
  (fun t ->
     let convert_slowly () = cases_pattern_expr_to_cases_pattern_expr t
     [@@ocaml.warning "-26"]
     in Obj.magic t)
