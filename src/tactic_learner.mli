module Id : sig
  type t
  val equal     : t -> t -> bool
  val to_string : t -> string
end

type id = Id.t

module IdMap : Map.S with type key = Id.t
type id_map = Id.t IdMap.t

type sentence = Node of sentence list | Leaf of string

type proof_state =
{ hypotheses : (id * sentence) list
; goal       : sentence }

type tactic
val tactic_sentence : tactic -> sentence
val local_variables : tactic -> id list
val substitute      : tactic -> id_map -> tactic

type execution = tactic list * proof_state * proof_state list
module type TacticianLearnerType = sig
  type t
  val create  : unit -> t
  val add     : t -> execution list -> tactic -> t
  val predict : t -> (tactic list * proof_state) list -> (float * bool list * tactic) list
end

val register_learner : string -> (module TacticianLearnerType) -> unit
