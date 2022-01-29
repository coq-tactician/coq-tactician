open Names

module O = Glob_term

(**  The kind of patterns that occurs in "match ... with ... end"

     locs here refers to the ident's location, not whole pat *)
type 'a cases_pattern_r =
  | PatVar  of Name.t
  | PatCstr of constructor * 'cases_pattern_g list * Name.t
  (** [PatCstr(p,C,l,x)] = "|'C' 'l' as 'x'" *)
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

(** Representation of an internalized (or in other words globalized) term. *)
type 'a glob_constr_r =
  | GRef of GlobRef.t * O.glob_level list option
      (* An identifier that represents a reference to an object defined
          either in the (global) environment or in the (local) context. *)
  | GVar of Id.t
      (* An identifier that cannot be regarded as "GRef".
          Bound variables are typically represented this way. *)
  | GEvar   of O.existential_name * (Id.t * 'glob_constr_g) list
  | GPatVar of Evar_kinds.matching_var_kind (** Used for patterns only *)
  | GApp    of 'glob_constr_g * 'glob_constr_g list
  | GLambda of Name.t * O.binding_kind *  'glob_constr_g * 'glob_constr_g
  | GProd   of Name.t * O.binding_kind * 'glob_constr_g * 'glob_constr_g
  | GLetIn  of Name.t * 'glob_constr_g * 'glob_constr_g option * 'glob_constr_g
  | GCases  of Constr.case_style * 'glob_constr_g option * 'a tomatch_tuples_g * 'a cases_clauses_g
      (** [GCases(style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in [MatchStyle]) *)
  | GLetTuple of Name.t list * (Name.t * 'glob_constr_g option) * 'glob_constr_g * 'glob_constr_g
  | GIf   of 'glob_constr_g * (Name.t * 'glob_constr_g option) * 'glob_constr_g * 'glob_constr_g
  | GRec  of O.glob_fix_kind * Id.t array * 'a glob_decl_g list array *
             'glob_constr_g array * 'glob_constr_g array
  | GSort of O.glob_sort
  | GHole of Evar_kinds.t * Namegen.intro_pattern_naming_expr * 'genarg option
  | GCast of 'glob_constr_g * 'glob_constr_g O.cast_type
  | GInt of Uint63.t
  | GFloat of Float64.t

  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

and 'a glob_decl_g = Name.t * O.binding_kind * 'glob_constr_g option * 'glob_constr_g
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

and 'a predicate_pattern_g =
    Name.t * (inductive * Name.t list) CAst.t option
      (* [(na,id)] = "as 'na' in 'id'" where if [id] is [Some(l,I,k,args)]. *)
    constraint 'a = <
      glob_constr_g:'glob_constr_g;
      cases_pattern_g:'cases_pattern_g;
      genarg:'genarg
    >

and 'a tomatch_tuple_g = ('glob_constr_g * 'a predicate_pattern_g)
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

and 'a tomatch_tuples_g = 'a tomatch_tuple_g list
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

and 'a cases_clause_g = (Id.t list * 'cases_pattern_g list * 'glob_constr_g) CAst.t
(* [(p,il,cl,t)] = "|'cl' => 't'". Precondition: the free variables
    of [t] are members of [il]. *)
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

and 'a cases_clauses_g = 'a cases_clause_g list
  constraint 'a = <
    glob_constr_g:'glob_constr_g;
    cases_pattern_g:'cases_pattern_g;
    genarg:'genarg
  >

type constr_dispatch = <
  glob_constr_g:glob_constr;
  cases_pattern_g:cases_pattern;
  genarg:Genarg.glob_generic_argument
>
and glob_constr = (constr_dispatch glob_constr_r, [ `any ]) DAst.t
and cases_pattern = (constr_dispatch cases_pattern_r, [ `any ]) DAst.t

