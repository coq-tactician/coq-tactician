open Ltac_plugin
open Tacexpr
open Constr
open Names

type id = Id.t
type id_map = id Id.Map.t

type sexpr = Sexpr.sexpr = Node of sexpr list | Leaf of string

module type TacticianStructures = sig
  type term
  type relevance
  type named_context = (term, term, relevance) Context.Named.pt
  val term_sexpr : term -> sexpr
  val term_repr  : term -> constr

  type proof_state
  val proof_state_hypotheses  : proof_state -> named_context
  val proof_state_goal        : proof_state -> term
  val proof_state_equal       : proof_state -> proof_state -> bool
  val proof_state_independent : proof_state -> bool

  type tactic
  val tactic_sexpr           : tactic -> sexpr
  val tactic_repr            : tactic -> glob_tactic_expr
  val tactic_make            : glob_tactic_expr -> tactic
  val tactic_hash            : tactic -> int
  val tactic_local_variables : tactic -> id list (* TODO: Add global variables *)
  val tactic_substitute      : tactic -> id_map -> tactic
  val tactic_globally_equal  : tactic -> tactic -> bool

  (* Proof tree with sharing. Behaves as a Directed Acyclic Tree. *)
  type proof_dag =
    | End
    | Step of proof_step
  and proof_step =
    { executions : (proof_state * proof_dag) list
    ; tactic     : tactic }

  type situation =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; state    : proof_state }
  type outcome =
    { parents  : (proof_state * proof_step) list
    ; siblings : proof_dag
    ; before   : proof_state
    ; after    : proof_state list }

  type prediction =
    { confidence : float
    ; focus      : int
    ; tactic     : tactic }
end

type data_status =
  | Original
  | QedTime
  | Substituted of Libnames.full_path (* path of the substituted constant (does not exist) *)
  | Discharged of Libnames.full_path (* path of the substituted constant (does not exist) *)

type origin = KerName.t * Libnames.full_path * data_status

module type TacticianOnlineLearnerType =
  functor (S : TacticianStructures) -> sig
    open S
    type model
    val empty    : unit -> model
    val learn    : model -> origin -> outcome list -> tactic -> model (* TODO: Add lemma dependencies *)
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float * model
  end

module type TacticianOfflineLearnerType =
  functor (S : TacticianStructures) -> sig
    open S
    type model
    val add      : origin -> outcome list -> tactic -> unit (* TODO: Add lemma dependencies *)
    val train    : unit -> model
    val predict  : model -> situation list -> prediction IStream.t (* TODO: Add global environment *)
    val evaluate : model -> outcome -> tactic -> float
  end

val register_online_learner  : string -> (module TacticianOnlineLearnerType)  -> unit
val register_offline_learner : string -> (module TacticianOfflineLearnerType) -> unit
