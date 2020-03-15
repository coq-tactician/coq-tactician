open Names
open Term

open Libnames
open Nametab
open Globnames
open Constr
open Context

exception HammerError of string

 type hhterm =
   Id of string (* may be a constant or variable *)
 | Comb of hhterm * hhterm
 | Abs of string * hhterm * hhterm;; (* name of introduced id, type and subterm *)
(* Abs never occurs in Coq terms *)

type hhdef =
  hhterm (* "name" term; use get_hhdef_name to extract the name string *) *
    hhterm (* kind; Comb(Id "$Sort", Id "$Prop") if type is a proposition *) *
    hhterm Lazy.t (* type *) *
    hhterm Lazy.t (* term: definiens (value or proof term) *)

let get_hhterm_name (c : hhterm) : string =
  match c with
  | Comb(Comb(Id "$Construct", _), Id constrname) ->
    constrname
  | Comb(Id "$Const", Id name) ->
    name
  | Comb(Comb(Id "$Ind", Id indname), _) ->
    indname
  | Comb(Id "$Var", Id name) ->
    name
  | _ ->
    ""

let (++) f g x = f(g(x))

let mk_id x = Id x
let mk_app x y = Comb(x, y)
let mk_comb (x, y) = mk_app x y

let tuple (l : hhterm list) =
  match l with
  | [] -> assert false
  | [h] -> h
  | h :: t ->
    List.fold_left mk_app h t

let get_hhdef_name ((c, _, _, _) : hhdef) : string =
  get_hhterm_name c

let rec string_of_hhterm t =
  match t with
  | Id(s) -> s
  | Comb(x, y) -> string_of_hhterm x ^ " @ (" ^ string_of_hhterm y ^ ")"
  | Abs(s, x, y) -> "\\" ^ s ^ "." ^ string_of_hhterm y

(*
let get_current_context () =
  try
    Pfedit.get_current_goal_context ()
  with _ ->
    (Evd.empty, Global.env ())
*)

let hhterm_of_global glob =
  mk_id (string_of_path (path_of_global (Globnames.canonical_gr glob)))

let hhterm_of_sort s = match Sorts.family s with
  | InProp -> mk_id "$Prop"
  | InSProp -> mk_id "$SProp"
  | InSet  -> mk_id "$Set"
  | InType -> mk_id "$Type"

let hhterm_of_constant c =
  tuple [mk_id "$Const"; hhterm_of_global (ConstRef c)]

let hhterm_of_inductive i =
  tuple [mk_id "$Ind"; hhterm_of_global (IndRef i);
         mk_id (string_of_int (Inductiveops.inductive_nparams (Global.env ()) i))]

let hhterm_of_construct cstr =
  tuple [mk_id "$Construct"; hhterm_of_inductive (fst cstr); hhterm_of_global (ConstructRef cstr)]

let hhterm_of_var v =
  tuple [mk_id "$Var"; hhterm_of_global (VarRef v)]

let hhterm_of_intarray a =
  tuple ((mk_id "$IntArray") :: (List.map mk_id (List.map string_of_int (Array.to_list a))))

let hhterm_of_caseinfo ci =
  let {ci_ind = ci_ind; ci_npar = ci_npar; ci_cstr_ndecls = ci_cstr_ndecls;
       ci_cstr_nargs = ci_cstr_nargs; ci_pp_info = ci_pp_info} = ci
  in
  tuple [mk_id "$CaseInfo"; hhterm_of_inductive ci_ind;
         mk_id (string_of_int ci_npar);
         hhterm_of_intarray ci_cstr_ndecls;
         hhterm_of_intarray ci_cstr_nargs]

(* Unsafe *)
let hhterm_of_name name = match name with
  | Name.Name id -> tuple [mk_id "$Name"; mk_id (Id.to_string id)]
  | Name.Anonymous  -> tuple [mk_id "$Name"; mk_id "$Anonymous"]

let hhterm_of_namearray a =
  tuple ((mk_id "$NameArray") :: (List.map hhterm_of_name (Array.to_list a)))

let hhterm_of_bool b =
  if b then mk_app (mk_id "$Bool") (mk_id "$True")
  else mk_app (mk_id "$Bool") (mk_id "$False")

let rec hhterm_of (t : Constr.constr) : hhterm =
  match Constr.kind t with
  | Rel n -> tuple [mk_id "$Rel"; mk_id (string_of_int n)]
  | Meta n -> raise (HammerError "Metavariables not supported.")
  | Var v -> hhterm_of_var v
  | Sort s -> tuple [mk_id "$Sort"; hhterm_of_sort s]
  | Cast (ty1,ck,ty2) -> tuple [mk_id "$Cast"; hhterm_of ty1; hhterm_of ty2]
  | Prod (na,ty,c)    ->
     tuple [mk_id "$Prod"; hhterm_of_name na.binder_name; hhterm_of ty; hhterm_of c]
  | Lambda (na,ty,c)  ->
     tuple [mk_id "$Lambda"; hhterm_of_name na.binder_name; hhterm_of ty; hhterm_of c]
  | LetIn (na,b,ty,c) ->
     tuple [mk_id "$LetIn"; hhterm_of_name na.binder_name; hhterm_of b; hhterm_of ty; hhterm_of c]
  | App (f,args)      ->
     tuple [mk_id "$App"; hhterm_of f; hhterm_of_constrarray args]
  | Const (c,u)       -> hhterm_of_constant c
  | Proj (p,c)        -> tuple [mk_id "$Proj";
                                tuple [hhterm_of_constant (Projection.constant p);
                                       hhterm_of_bool (Projection.unfolded p)];
                                hhterm_of c]
                         (* TODO: projections not really supported *)
  | Evar (evk,cl)     -> mk_id "Existentialvar"
  | Ind (ind,u)       -> hhterm_of_inductive ind
  | Construct (ctr,u) -> hhterm_of_construct ctr
  | Case (ci,p,c,bl)  ->
      tuple ([mk_id "$Case"; hhterm_of_caseinfo ci ; hhterm_of p;
        hhterm_of c; hhterm_of_constrarray bl])
  | Fix (nvn,recdef) -> tuple [mk_id "$Fix";
                               hhterm_of_intarray (fst nvn);
                               mk_id (string_of_int (snd nvn));
                               hhterm_of_precdeclaration recdef]
  | CoFix (n,recdef) -> tuple [mk_id "$CoFix";
                               mk_id (string_of_int n);
                               hhterm_of_precdeclaration recdef]
  | Int n            -> mk_id ("$Uint63." ^ (Uint63.to_string n))
  | Float f          -> mk_id ("$Float." ^ (Float64.to_string f))
and hhterm_of_constrarray a =
  tuple ((mk_id "$ConstrArray") :: List.map hhterm_of (Array.to_list a))
and hhterm_of_precdeclaration (a,b,c) =
  tuple [(mk_id "$PrecDeclaration") ; hhterm_of_namearray (Array.map (fun a -> a.binder_name) a);
         hhterm_of_constrarray b; hhterm_of_constrarray c]

let econstr_to_constr x = EConstr.to_constr ~abort_on_undefined_evars:false Evd.empty x
