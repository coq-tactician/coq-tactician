open Names
open Libnames

module O = Constrexpr

type 'a cases_pattern_notation_substitution =
  'cases_pattern_expr list *     (* for constr subterms *)
  'cases_pattern_expr list list  (* for recursive notations *)
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type 'a cases_pattern_expr_r =
  | CPatAlias of 'cases_pattern_expr * lname
  | CPatCstr  of qualid
    * 'cases_pattern_expr list option * 'cases_pattern_expr list
  (** [CPatCstr (_, c, Some l1, l2)] represents [(@ c l1) l2] *)
  | CPatAtom of qualid option
  | CPatOr   of 'cases_pattern_expr list
  | CPatNotation of O.notation * 'a cases_pattern_notation_substitution
    * 'cases_pattern_expr list (** CPatNotation (_, n, l1 ,l2) represents
                                  (notation n applied with substitution l1)
                                  applied to arguments l2 *)
  | CPatPrim   of O.prim_token
  | CPatRecord of (qualid * 'cases_pattern_expr) list
  | CPatDelimiters of string * 'cases_pattern_expr
  | CPatCast   of 'cases_pattern_expr * 'constr_expr
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type 'a case_expr = 'constr_expr                 (* expression that is being matched *)
              * lname option                (* as-clause *)
              * 'cases_pattern_expr option   (* in-clause *)
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type 'a branch_expr =
  ('cases_pattern_expr list list * 'constr_expr) CAst.t
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

(* Anonymous defs allowed ?? *)
type 'a local_binder_expr =
  | CLocalAssum   of lname list * O.binder_kind * 'constr_expr
  | CLocalDef     of lname * 'constr_expr * 'constr_expr option
  | CLocalPattern of ('cases_pattern_expr * 'constr_expr option) CAst.t
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type 'a recursion_order_expr_r =
  | CStructRec of lident
  | CWfRec of lident * 'constr_expr
  | CMeasureRec of lident option * 'constr_expr * 'constr_expr option (** argument, measure, relation *)
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >
type 'a recursion_order_expr = 'a recursion_order_expr_r CAst.t
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type 'a fix_expr =
    lident * 'a recursion_order_expr option *
      'a local_binder_expr list * 'constr_expr * 'constr_expr
    constraint 'a = <
      constr_expr:'constr_expr;
      cases_pattern_expr:'cases_pattern_expr;
      genarg:'genarg
    >

type 'a cofix_expr =
    lident * 'a local_binder_expr list * 'constr_expr * 'constr_expr
    constraint 'a = <
      constr_expr:'constr_expr;
      cases_pattern_expr:'cases_pattern_expr;
      genarg:'genarg
    >


type 'a constr_notation_substitution =
    'constr_expr list *      (* for constr subterms *)
    'constr_expr list list * (* for recursive notations *)
    'cases_pattern_expr list *   (* for binders *)
    'a local_binder_expr list list (* for binder lists (recursive notations) *)
    constraint 'a = <
      constr_expr:'constr_expr;
      cases_pattern_expr:'cases_pattern_expr;
      genarg:'genarg
    >

type 'a constr_expr_r =
  | CRef     of qualid * O.instance_expr option
  | CFix     of lident * 'a fix_expr list
  | CCoFix   of lident * 'a cofix_expr list
  | CProdN   of 'a local_binder_expr list * 'constr_expr
  | CLambdaN of 'a local_binder_expr list * 'constr_expr
  | CLetIn   of lname * 'constr_expr * 'constr_expr option * 'constr_expr
  | CAppExpl of (O.proj_flag * qualid * O.instance_expr option) * 'constr_expr list
  | CApp     of (O.proj_flag * 'constr_expr) *
                ('constr_expr * O.explicitation CAst.t option) list
  | CRecord  of (qualid * 'constr_expr) list

  (* representation of the "let" and "match" constructs *)
  | CCases of Constr.case_style   (* determines whether this value represents "let" or "match" construct *)
            * 'constr_expr option  (* return-clause *)
            * 'a case_expr list
            * 'a branch_expr list    (* branches *)

  | CLetTuple of lname list * (lname option * 'constr_expr option) *
                 'constr_expr * 'constr_expr
  | CIf of 'constr_expr * (lname option * 'constr_expr option)
         * 'constr_expr * 'constr_expr
  | CHole   of Evar_kinds.t option * Namegen.intro_pattern_naming_expr * 'genarg option
  | CPatVar of Pattern.patvar
  | CEvar   of Glob_term.existential_name * (Id.t * 'constr_expr) list
  | CSort   of Glob_term.glob_sort
  | CCast   of 'constr_expr * 'constr_expr Glob_term.cast_type
  | CNotation of O.notation * 'a constr_notation_substitution
  | CGeneralization of Glob_term.binding_kind * O.abstraction_kind option * 'constr_expr
  | CPrim of O.prim_token
  | CDelimiters of string * 'constr_expr
  constraint 'a = <
    constr_expr:'constr_expr;
    cases_pattern_expr:'cases_pattern_expr;
    genarg:'genarg
  >

type constr_dispatch = <
  constr_expr:constr_expr;
  cases_pattern_expr:cases_pattern_expr;
  genarg:Genarg.raw_generic_argument
>
and constr_expr = constr_dispatch constr_expr_r CAst.t
and cases_pattern_expr = constr_dispatch cases_pattern_expr_r CAst.t
