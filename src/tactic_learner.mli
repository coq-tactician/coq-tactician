type sentence = Node of string * sentence list

module Id : sig
  type t
  val equal : t -> t -> bool
end

type proof_state =
{ hypotheses : (Id.t * sentence) list
; goal       : sentence }

type tactic
val tactic_sentence : tactic -> sentence
val local_variables : tactic -> Id.t list

module IdMap : Map.S with type key = Id.t
type substitution = Id.t IdMap.t
val substitute      : tactic -> substitution -> tactic

module type TacticianLearnerType = sig
  type t
  val create  : unit -> t
  val add     : t -> memory:tactic list ->
                     before:proof_state -> tactic ->
                      after:proof_state -> t
  val predict : t -> proof_state -> (float * tactic) list
end

val register_learner : string -> (module TacticianLearnerType) -> unit
