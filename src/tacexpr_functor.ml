open Ltac_plugin
open Names
open Genredexpr
open Loc
open Genarg
open Locus
open Tacexpr
open Tactypes
open Libnames

type 'a intro_pattern_expr_r =
  | IntroForthcoming of bool
  | IntroNaming of Namegen.intro_pattern_naming_expr
  | IntroAction of 'intro_pattern_action_expr
  constraint 'a = <
    constr:'constr;
    intro_pattern_expr:'intro_pattern_expr;
    intro_pattern_action_expr:'intro_pattern_action_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr
  >
type 'a intro_pattern_action_expr_r =
  | IntroWildcard
  | IntroOrAndPattern of 'or_and_intro_pattern_expr
  | IntroInjection of ('intro_pattern_expr) CAst.t list
  | IntroApplyOn of 'constr CAst.t * 'intro_pattern_expr CAst.t
  | IntroRewrite of bool
  constraint 'a = <
    constr:'constr;
    intro_pattern_expr:'intro_pattern_expr;
    intro_pattern_action_expr:'intro_pattern_action_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr
  >
type 'a or_and_intro_pattern_expr_r =
  | IntroOrPattern of ('intro_pattern_expr) CAst.t list list
  | IntroAndPattern of ('intro_pattern_expr) CAst.t list
  constraint 'a = <
    constr:'constr;
    intro_pattern_expr:'intro_pattern_expr;
    intro_pattern_action_expr:'intro_pattern_action_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr
  >

type 'constr intro_pattern_dispatch = <
  constr:'constr;
  intro_pattern_expr:'constr intro_pattern_expr;
  intro_pattern_action_expr:'constr intro_pattern_action_expr;
  or_and_intro_pattern_expr:'constr or_and_intro_pattern_expr
>
and 'constr intro_pattern_expr = 'constr intro_pattern_dispatch intro_pattern_expr_r
and 'constr intro_pattern_action_expr = 'constr intro_pattern_dispatch intro_pattern_action_expr_r
and 'constr or_and_intro_pattern_expr = 'constr intro_pattern_dispatch or_and_intro_pattern_expr_r

type 'a inversion_strength =
  | NonDepInversion of
      Inv.inversion_kind * 'name list * 'or_and_intro_pattern_expr CAst.t or_var option
  | DepInversion of
      Inv.inversion_kind * 'term option * 'or_and_intro_pattern_expr CAst.t or_var option
  | InversionUsing of 'term * 'name list
  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

type 'a induction_clause =
  'dterm with_bindings Tactics.destruction_arg *
  (Namegen.intro_pattern_naming_expr CAst.t option (* eqn:... *)
   * 'or_and_intro_pattern_expr CAst.t or_var option) (* as ... *)
  * 'name clause_expr option (* in ... *)
  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

type 'a induction_clause_list =
  'a induction_clause list
  * 'term with_bindings option (* using ... *)
  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

type 'a gen_atomic_tactic_expr =
  (* Basic tactics *)
  | TacIntroPattern of evars_flag * 'intro_pattern_expr CAst.t list
  | TacApply of advanced_flag * evars_flag * 'term with_bindings_arg list *
      ('name * 'intro_pattern_expr CAst.t option) option
  | TacElim of evars_flag * 'term with_bindings_arg * 'term with_bindings option
  | TacCase of evars_flag * 'term with_bindings_arg
  | TacMutualFix of Id.t * int * (Id.t * int * 'term) list
  | TacMutualCofix of Id.t * (Id.t * 'term) list
  | TacAssert of
      evars_flag * bool * 'tacexpr option option *
      'intro_pattern_expr CAst.t option * 'term
  | TacGeneralize of ('term with_occurrences * Name.t) list
  | TacLetTac of evars_flag * Name.t * 'term * 'name clause_expr * letin_flag *
      Namegen.intro_pattern_naming_expr CAst.t option

  (* Derived basic tactics *)
  | TacInductionDestruct of
      rec_flag * evars_flag * 'a induction_clause_list

  (* Conversion *)
  | TacReduce of ('term,'constant,'pattern) red_expr_gen * 'name clause_expr
  | TacChange of check_flag * 'pattern option * 'dterm * 'name clause_expr

  (* Equality and inversion *)
  | TacRewrite of evars_flag *
      (bool * Equality.multi * 'dterm with_bindings_arg) list * 'name clause_expr *
      (* spiwack: using ['dtrm] here is a small hack, may not be
         stable by a change in the representation of delayed
         terms. Because, in fact, it is the whole "with_bindings"
         which is delayed. But because the "t" level for ['dtrm] is
         uninterpreted, it works fine here too, and avoid more
         disruption of this file. *)
      'tacexpr option
  | TacInversion of 'a inversion_strength * quantified_hypothesis

  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

type 'a gen_tactic_arg =
  | TacGeneric     of 'genarg
  | ConstrMayEval  of ('term,'constant,'pattern) may_eval
  | Reference      of 'reference
  | TacCall    of ('reference * 'tacarg list) CAst.t
  | TacFreshId of string or_var list
  | Tacexp of 'tacexpr
  | TacPretype of 'term
  | TacNumgoals

  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

type 'a gen_tactic_fun_ast =
  Name.t list * 'tacexpr

  constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
  >

(** Generic ltac expressions.
    't : terms, 'p : patterns, 'c : constants, 'i : inductive,
    'r : ltac refs, 'n : idents, 'l : levels *)

type 'a gen_tactic_expr =
  | TacAtom of 'a gen_atomic_tactic_expr CAst.t
  | TacThen of
      'tacexpr *
      'tacexpr
  | TacDispatch of
      'tacexpr list
  | TacExtendTac of
      'tacexpr array *
      'tacexpr *
      'tacexpr array
  | TacThens of
      'tacexpr *
      'tacexpr list
  | TacThens3parts of
      'tacexpr *
      'tacexpr array *
      'tacexpr *
      'tacexpr array
  | TacFirst of 'tacexpr list
  | TacComplete of 'tacexpr
  | TacSolve of 'tacexpr list
  | TacTry of 'tacexpr
  | TacOr of
      'tacexpr *
      'tacexpr
  | TacOnce of
      'tacexpr
  | TacExactlyOnce of
      'tacexpr
  | TacIfThenCatch of
      'tacexpr *
      'tacexpr *
      'tacexpr
  | TacOrelse of
      'tacexpr *
      'tacexpr
  | TacDo of int or_var * 'tacexpr
  | TacTimeout of int or_var * 'tacexpr
  | TacTime of string option * 'tacexpr
  | TacRepeat of 'tacexpr
  | TacProgress of 'tacexpr
  | TacShowHyps of 'tacexpr
  | TacAbstract of
      'tacexpr * Id.t option
  | TacId of 'name message_token list
  | TacFail of global_flag * int or_var * 'name message_token list
  | TacInfo of 'tacexpr
  | TacLetIn of rec_flag *
      (lname * 'tacarg) list *
      'tacexpr
  | TacMatch of lazy_flag *
      'tacexpr *
      ('pattern,'tacexpr) match_rule list
  | TacMatchGoal of lazy_flag * direction_flag *
      ('pattern,'tacexpr) match_rule list
  | TacFun of 'a gen_tactic_fun_ast
  | TacArg of 'tacarg CAst.t
  | TacSelect of Goal_select.t * 'tacexpr
  (* For ML extensions *)
  | TacML of (ml_tactic_entry * 'tacarg list) CAst.t
  (* For syntax extensions *)
  | TacAlias of (KerName.t * 'tacarg list) CAst.t

constraint 'a = <
    term:'term;
    dterm: 'dterm;
    pattern:'pattern;
    constant:'constant;
    reference:'reference;
    name:'name;
    tacexpr:'tacexpr;
    tacarg:'tacarg;
    genarg:'genarg;
    intro_pattern_expr:'intro_pattern_expr;
    or_and_intro_pattern_expr:'or_and_intro_pattern_expr;
>

(** Globalized tactics *)

type g_trm = Glob_term_functor.glob_constr * Constrexpr_functor.constr_expr option
type g_pat = Id.Set.t * g_trm * Pattern_functor.constr_pattern
type g_cst = evaluable_global_reference Genredexpr.and_short_name or_var
type g_ref = ltac_constant located or_var
type g_nam = lident

type g_dispatch =  <
  term:g_trm;
  dterm:g_trm;
  pattern:g_pat;
  constant:g_cst;
  reference:g_ref;
  name:g_nam;
  tacexpr:glob_tactic_expr;
  tacarg:glob_tactic_arg;
  genarg:glevel generic_argument;
  intro_pattern_expr:g_trm intro_pattern_expr;
  or_and_intro_pattern_expr:g_trm or_and_intro_pattern_expr;
>

and glob_tactic_expr =
  g_dispatch gen_tactic_expr

and glob_tactic_arg =
  g_dispatch gen_tactic_arg

type glob_atomic_tactic_expr =
  g_dispatch gen_atomic_tactic_expr


(** Raw tactics *)

type r_trm = Constrexpr_functor.constr_expr
type r_pat = r_trm
type r_ref = qualid
type r_nam = lident
type r_lev = rlevel

type r_dispatch =  <
  term:r_trm;
  dterm:r_trm;
  pattern:r_pat;
  constant:r_cst;
  reference:r_ref;
  name:r_nam;
  tacexpr:raw_tactic_expr;
  tacarg:raw_tactic_arg;
  genarg:rlevel generic_argument;
  intro_pattern_expr:r_trm intro_pattern_expr;
  or_and_intro_pattern_expr:r_trm or_and_intro_pattern_expr;
>

and raw_tactic_expr =
  r_dispatch gen_tactic_expr

and raw_tactic_arg =
  r_dispatch gen_tactic_arg

type raw_atomic_tactic_expr =
  r_dispatch gen_atomic_tactic_expr

