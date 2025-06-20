open Ltac_plugin
open Coq_ast_sequence
open Monad_util

module Cata (M : Monad.Def) : sig
  open Sequence(M)

  open Glob_term_functor
  open Constrexpr_functor
  open Pattern_functor
  open Tacexpr_functor

  type sequence_record =
    { cases_pattern_g : cases_pattern_t      -> cases_pattern t
    ; cases_pattern_r : cases_pattern_expr_t -> cases_pattern_expr t
    ; constr_expr     : constr_expr_t        -> constr_expr t
    ; constr_pattern  : constr_pattern_t     -> constr_pattern t
    ; glob_constr     : glob_constr_t        -> glob_constr t
    ; glob_tacarg     : glob_tactic_arg_t    -> glob_tactic_arg t
    ; glob_tacexpr    : glob_tactic_expr_t   -> glob_tactic_expr t
    ; raw_tacarg      : raw_tactic_arg_t     -> raw_tactic_arg t
    ; raw_tacexpr     : raw_tactic_expr_t    -> raw_tactic_expr t
    ; glob_intro_pattern_expr : g_trm intro_pattern_expr_t -> g_trm intro_pattern_expr t
    ; glob_intro_pattern_action_expr : g_trm intro_pattern_action_expr_t -> g_trm intro_pattern_action_expr t
    ; glob_or_and_intro_pattern_expr : g_trm or_and_intro_pattern_expr_t -> g_trm or_and_intro_pattern_expr t
    ; raw_intro_pattern_expr : r_trm intro_pattern_expr_t -> r_trm intro_pattern_expr t
    ; raw_intro_pattern_action_expr : r_trm intro_pattern_action_expr_t -> r_trm intro_pattern_action_expr t
    ; raw_or_and_intro_pattern_expr : r_trm or_and_intro_pattern_expr_t -> r_trm or_and_intro_pattern_expr t }

  val default_sequence_record : sequence_record

  open Tacexpr
  open Glob_term
  open Constrexpr
  open Pattern
  open Tactypes
  open Genredexpr

  val glob_tactic_expr_cata : sequence_record -> glob_tactic_expr map
  val glob_tactic_arg_cata  : sequence_record -> glob_tactic_arg map
  val raw_tactic_expr_cata  : sequence_record -> raw_tactic_expr map
  val raw_tactic_arg_cata   : sequence_record -> raw_tactic_arg map
  val glob_constr_cata      : sequence_record -> glob_constr map
  val cases_pattern_g_cata  : sequence_record -> cases_pattern map
  val constr_expr_cata      : sequence_record -> constr_expr map
  val cases_pattern_r_cata  : sequence_record -> cases_pattern_expr map
  val g_trm_cata            : sequence_record -> g_trm map
  val constr_pattern_cata   : sequence_record -> constr_pattern map
  val g_pat_cata            : sequence_record -> g_pat map
  val glob_intro_pattern_expr_cata        : sequence_record -> g_trm intro_pattern_expr map
  val glob_intro_pattern_action_expr_cata : sequence_record -> g_trm intro_pattern_action_expr map
  val glob_or_and_intro_pattern_expr_cata : sequence_record -> g_trm or_and_intro_pattern_expr map
  val raw_intro_pattern_expr_cata         : sequence_record -> r_trm intro_pattern_expr map
  val raw_intro_pattern_action_expr_cata  : sequence_record -> r_trm intro_pattern_action_expr map
  val raw_or_and_intro_pattern_expr_cata  : sequence_record -> r_trm or_and_intro_pattern_expr map
end

(** Used for extending the recursive structure with generic arguments defined in plugins *)

module MapDef (M : Monad.Def) : sig
  open WithMonadNotations(M)

  open Tacexpr
  open Glob_term
  open Constrexpr
  open Tactypes
  open Genredexpr

  type generic_obj =
    < cases_pattern_g    : cases_pattern map
    ; cases_pattern_expr : cases_pattern_expr map
    ; glob_constr_g      : glob_constr map
    ; pattern            : g_pat map
    ; glob_tacarg        : glob_tactic_arg map
    ; glob_tacexpr       : glob_tactic_expr map
    ; raw_tacarg         : raw_tactic_arg map
    ; raw_tacexpr        : raw_tactic_expr map
    ; g_term             : g_trm map
    ; constr_expr        : constr_expr map
    ; raw_intro_pattern_expr : r_trm intro_pattern_expr map
    ; glob_intro_pattern_expr : g_trm intro_pattern_expr map
    ; raw_intro_pattern_action_expr : r_trm intro_pattern_action_expr map
    ; glob_intro_pattern_action_expr : g_trm intro_pattern_action_expr map
    ; raw_or_and_intro_pattern_expr : r_trm or_and_intro_pattern_expr map
    ; glob_or_and_intro_pattern_expr : g_trm or_and_intro_pattern_expr map
    >
end

module type GenMap = sig
  type raw
  type glob
  module M (M : Monad.Def) : sig
    open MapDef(M)
    val raw_map : generic_obj -> raw -> raw M.t
    val glob_map : generic_obj -> glob -> glob M.t
  end
end

val register_generic_cata :
  ('a, 'b, 'c) Genarg.genarg_type -> (module GenMap with type glob = 'b and type raw = 'a) -> unit
val register_generic_cata_identity : ('a, 'b, 'c) Genarg.genarg_type -> unit
