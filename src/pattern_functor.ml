open Names

(** {5 Patterns} *)

type 'a constr_pattern_r =
  | PRef of GlobRef.t
  | PVar of Id.t
  | PEvar of Evar.t * 'a array
  | PRel of int
  | PApp of 'a * 'a array
  | PSoApp of Pattern.patvar * 'a list
  | PProj of Projection.t * 'a
  | PLambda of Name.t * 'a * 'a
  | PProd of Name.t * 'a * 'a
  | PLetIn of Name.t * 'a * 'a option * 'a
  | PSort of Sorts.family
  | PMeta of Pattern.patvar option
  | PIf of 'a * 'a * 'a
  | PCase of Pattern.case_info_pattern * 'a * 'a *
      (int * bool list * 'a) list (** index of constructor, nb of args *)
  | PFix of (int array * int) * (Name.t array * 'a array * 'a array)
  | PCoFix of int * (Name.t array * 'a array * 'a array)
  | PInt of Uint63.t
  | PFloat of Float64.t

type constr_pattern = constr_pattern constr_pattern_r

(** Nota : in a [PCase], the array of branches might be shorter than
    expected, denoting the use of a final "_ => _" branch *)
