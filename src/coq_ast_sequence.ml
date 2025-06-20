open Monad_util
open Coq_ast_monadic_map
open Tacexpr_functor
open Glob_term_functor
open Constrexpr_functor
open Pattern_functor
open Genarg

module Sequence (M : Monad.Def) = struct
  include WithMonadNotations(M)

  type g_dispatch_t =  <
    term:g_trm t;
    dterm:g_trm t;
    pattern:g_pat t;
    constant:g_cst t;
    reference:g_ref t;
    name:g_nam t;
    tacexpr:glob_tactic_expr t;
    tacarg:glob_tactic_arg t;
    genarg:glevel generic_argument t;
    intro_pattern_expr:g_trm intro_pattern_expr t;
    or_and_intro_pattern_expr:g_trm or_and_intro_pattern_expr t;
  >
  and glob_tactic_expr_t =
    g_dispatch_t gen_tactic_expr
  and glob_tactic_arg_t =
    g_dispatch_t gen_tactic_arg
  type glob_atomic_tactic_expr_t =
    g_dispatch_t gen_atomic_tactic_expr

  type r_dispatch_t =  <
    term:r_trm t;
    dterm:r_trm t;
    pattern:r_pat t;
    constant:Genredexpr.r_cst t;
    reference:r_ref t;
    name:r_nam t;
    tacexpr:raw_tactic_expr t;
    tacarg:raw_tactic_arg t;
    genarg:rlevel generic_argument t;
    intro_pattern_expr:r_trm intro_pattern_expr t;
    or_and_intro_pattern_expr:r_trm or_and_intro_pattern_expr t;
  >
  type raw_tactic_expr_t =
    r_dispatch_t gen_tactic_expr
  type raw_tactic_arg_t =
    r_dispatch_t gen_tactic_arg
  type raw_atomic_tactic_expr_t =
    r_dispatch_t gen_atomic_tactic_expr

  type constr_g_dispatch_t = <
    glob_constr_g:glob_constr t;
    cases_pattern_g:cases_pattern t;
    genarg:Genarg.glob_generic_argument t
  >
 type glob_constr_t = (constr_g_dispatch_t glob_constr_r, [ `any ]) DAst.t
 type cases_pattern_t = (constr_g_dispatch_t cases_pattern_r, [ `any ]) DAst.t

  type constr_r_dispatch_t = <
    constr_expr:constr_expr t;
    cases_pattern_expr:cases_pattern_expr t;
    genarg:Genarg.raw_generic_argument t
  >
  type constr_expr_t = constr_r_dispatch_t constr_expr_r CAst.t
  type cases_pattern_expr_t = constr_r_dispatch_t cases_pattern_expr_r CAst.t

  type constr_pattern_t = constr_pattern t constr_pattern_r

  type 'constr intro_pattern_dispatch_t = <
    constr:'constr t;
    intro_pattern_expr:'constr intro_pattern_expr t;
    intro_pattern_action_expr:'constr intro_pattern_action_expr t;
    or_and_intro_pattern_expr:'constr or_and_intro_pattern_expr t
  >
  type 'constr intro_pattern_expr_t = 'constr intro_pattern_dispatch_t intro_pattern_expr_r
  type 'constr intro_pattern_action_expr_t = 'constr intro_pattern_dispatch_t intro_pattern_action_expr_r
  type 'constr or_and_intro_pattern_expr_t = 'constr intro_pattern_dispatch_t or_and_intro_pattern_expr_r

  let id x = x
  let idobj = object
    method cases_pattern_g = id
    method cases_pattern_expr = id
    method constr_expr = id
    method genarg = id
    method glob_constr_g = id
    method constant = id
    method pattern = id
    method reference = id
    method tacarg = id
    method tacexpr = id
    method term = id
    method dterm = id
    method name = id
    method intro_pattern_expr = id
    method intro_pattern_action_expr = id
    method or_and_intro_pattern_expr = id
    method constr = id
  end

  module MM = Mapper(M)

  let cases_pattern_g_sequence : cases_pattern_t -> cases_pattern t =
    MM.dast_map @@ MM.cases_pattern_r_map idobj
  let cases_pattern_r_sequence : cases_pattern_expr_t -> cases_pattern_expr t =
    MM.cast_map @@ MM.cases_pattern_expr_r_map idobj
  let constr_expr_sequence : constr_expr_t -> constr_expr t =
    MM.cast_map @@ MM.constr_expr_r_map idobj
  let constr_pattern_sequence : constr_pattern_t -> constr_pattern t =
    MM.constr_pattern_r_map id
  let glob_constr_sequence : glob_constr_t -> glob_constr t =
    MM.dast_map @@ MM.glob_constr_r_map idobj
  let glob_tacarg_sequence : glob_tactic_arg_t -> glob_tactic_arg t =
    MM.gen_tactic_arg_map idobj
  let glob_tacexpr_sequence : glob_tactic_expr_t -> glob_tactic_expr t =
    MM.gen_tactic_expr_map idobj
  let raw_tacarg_sequence : raw_tactic_arg_t -> raw_tactic_arg t =
    MM.gen_tactic_arg_map idobj
  let raw_tacexpr_sequence : raw_tactic_expr_t -> raw_tactic_expr t =
    MM.gen_tactic_expr_map idobj
  let intro_pattern_expr_sequence (t : 'a intro_pattern_expr_t) : 'a intro_pattern_expr t =
    MM.intro_pattern_expr_map idobj t
  let intro_pattern_action_expr_sequence (t : 'a intro_pattern_action_expr_t) : 'a intro_pattern_action_expr t =
    MM.intro_pattern_action_expr_map idobj t
  let or_and_intro_pattern_expr_sequence (t : 'a or_and_intro_pattern_expr_t) : 'a or_and_intro_pattern_expr t =
    MM.or_and_intro_pattern_expr_map idobj t

end
