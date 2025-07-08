open Ltac_plugin
open Tacexpr
open Glob_term
open Constrexpr
open Pattern
open Genarg
open Monad_util
open Loc
open Genintern
open Tactypes
open Locus
open Tactics
open Names
open Genredexpr

module type MapDef = sig
  include MonadNotations

  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t

  val with_binders : Id.t list -> 'a -> ('a -> 'a t) -> ((Id.t -> Id.t) * 'a) t

  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t t -> 'a CAst.t t
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : 'a. (Loc.t option * 'a) t -> (Loc.t option * 'a) t
    ; variable : Id.t map
    ; qualid : (DirPath.t * Id.t) map
    (* Guaranteed not be at least partially qualified (otherwise variable is called) *)
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer
    ; glob_constr_and_expr : Genintern.glob_constr_and_expr transformer
    ; glob_constr_pattern_and_expr : Genintern.glob_constr_pattern_and_expr transformer
    }

  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; variable_map : Id.t map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; glob_constr_pattern_and_expr_map : glob_constr_pattern_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    ; qualid_map : Libnames.qualid map
    ; globref_map : GlobRef.t map
    ; quantified_hypothesis_map : quantified_hypothesis map
    ; red_expr_gen_map : 'a 'b 'c. 'a map -> 'b map -> 'c map -> ('a, 'b, 'c) red_expr_gen map
    }

  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }

  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) gen_map

end

module MapDefTemplate (M: Monad.Def) : sig
  include MonadNotations
  type 'a transformer = 'a -> ('a -> 'a t) -> 'a t
  val with_binders : Id.t list -> 'a -> ('a -> 'a t) -> ((Id.t -> Id.t) * 'a) t
  type mapper =
    { glob_tactic : glob_tactic_expr transformer
    ; raw_tactic : raw_tactic_expr transformer
    ; glob_atomic_tactic : glob_atomic_tactic_expr transformer
    ; raw_atomic_tactic : raw_atomic_tactic_expr transformer
    ; glob_tactic_arg : glob_tactic_arg transformer
    ; raw_tactic_arg : raw_tactic_arg transformer
    ; cast : 'a. 'a CAst.t t -> 'a CAst.t t
    ; constant : Constant.t map
    ; mutind : MutInd.t map
    ; short_name : Id.t CAst.t option map
    ; located : 'a. (Loc.t option * 'a) t -> (Loc.t option * 'a) t
    ; variable : Id.t map
    ; qualid : (DirPath.t * Id.t) map
    (* Guaranteed not be at least partially qualified (otherwise variable is called) *)
    ; constr_pattern : constr_pattern transformer
    ; constr_expr : constr_expr_r transformer
    ; glob_constr : ([ `any ] glob_constr_r) transformer
    ; glob_constr_and_expr : Genintern.glob_constr_and_expr transformer
    ; glob_constr_pattern_and_expr : Genintern.glob_constr_pattern_and_expr transformer
    }
  type recursor =
    { option_map : 'a. 'a map -> 'a option map
    ; or_var_map : 'a. 'a map -> 'a or_var map
    ; cast_map : 'a. 'a map -> 'a CAst.t map
    ; constant_map : Constant.t map
    ; mutind_map : MutInd.t map
    ; short_name_map : Id.t CAst.t option map
    ; located_map : 'a. 'a map -> 'a located map
    ; variable_map : Id.t map
    ; constr_expr_map : constr_expr map
    ; glob_constr_and_expr_map : glob_constr_and_expr map
    ; glob_constr_pattern_and_expr_map : glob_constr_pattern_and_expr map
    ; intro_pattern_expr_map : 'a. 'a map -> 'a intro_pattern_expr map
    ; bindings_map : 'a. 'a map -> 'a bindings map
    ; with_bindings_map : 'a. 'a map -> 'a with_bindings map
    ; clause_expr_map : 'a. 'a map -> 'a clause_expr map
    ; destruction_arg_map : 'a. 'a map -> 'a destruction_arg map
    ; raw_tactic_expr_map : raw_tactic_expr map
    ; glob_tactic_expr_map : glob_tactic_expr map
    ; qualid_map : Libnames.qualid map
    ; globref_map : GlobRef.t map
    ; quantified_hypothesis_map : quantified_hypothesis map
    ; red_expr_gen_map : 'a 'b 'c. 'a map -> 'b map -> 'c map -> ('a, 'b, 'c) red_expr_gen map
    }
  val default_mapper : mapper
  type ('raw, 'glb) gen_map =
    { raw : recursor -> 'raw map
    ; glb : recursor -> 'glb map }
  val default : ('raw, 'glb, 'top) genarg_type -> ('raw, 'glb) gen_map
end with type 'a t = 'a M.t

module type GenMap = sig
  type raw
  type glob
  module M : functor (M : MapDef) -> sig
    open M
    val raw_map : recursor -> raw map
    val glob_map : recursor -> glob map
  end
end

val register_generic_map : ('raw, 'glb, 'top) genarg_type ->
  (module GenMap with type raw = 'raw and type glob = 'glb) -> unit

val register_generic_map_identity : ('raw, 'glb, 'top) genarg_type -> unit

module MakeMapper : functor (M : MapDef) -> sig
  open M
  val glob_constr_map : mapper -> glob_constr map
  val constr_expr_map : mapper -> constr_expr map
  val constr_pattern_map : mapper -> constr_pattern map
  val raw_tactic_expr_map : mapper -> raw_tactic_expr map
  val raw_tactic_arg_map : mapper -> raw_tactic_arg map
  val raw_atomic_tactic_map : mapper -> raw_atomic_tactic_expr map
  val glob_tactic_expr_map : mapper -> glob_tactic_expr map
  val glob_tactic_arg_map : mapper -> glob_tactic_arg map
  val glob_atomic_tactic_map : mapper -> glob_atomic_tactic_expr map
end
