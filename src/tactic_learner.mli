module Id : sig
  type t
  val equal : t -> t -> bool
end
type id = Id.t

val mk_id : Names.Id.t -> id
val id_mk : id -> Names.Id.t

module IdMap : Map.S with type key = Id.t
type id_map = Id.t IdMap.t

type sentence = Node of string * sentence list

type proof_state =
{ hypotheses : (id * sentence) list
; goal       : sentence }

type tactic
val tactic_sentence : tactic -> sentence
val local_variables : tactic -> id list
val substitute      : tactic -> id_map -> tactic

module type TacticianLearnerType = sig
  type t
  val create  : unit -> t
  val add     : t -> before:proof_state ->
                            tactic ->
                      after:proof_state list -> t
  val predict : t -> proof_state -> (float * tactic) list
end

val register_learner : string -> (module TacticianLearnerType) -> unit
