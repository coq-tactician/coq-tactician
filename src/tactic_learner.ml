module Id = struct
  type t = Names.Id.t
  let equal = Names.Id.equal
end
type id = Id.t

let mk_id x = x
let id_mk x = x

module IdMap = Map.Make(struct
    type t = Id.t
    let compare = Names.Id.compare
  end)
type id_map = Id.t IdMap.t

type sentence = Node of string * sentence list

type proof_state =
{ hypotheses : (id * sentence) list
; goal       : sentence }

type tactic = string
let tactic_sentence t =  Node (t, [])
let local_variables t = []
let substitute t map = t

module type TacticianLearnerType = sig
  type t
  val create  : unit -> t
  val add     : t -> before:proof_state ->
                            tactic ->
                      after:proof_state list -> t
  val predict : t -> proof_state -> (float * tactic) list
end

let register_learner (name : string) (learner : (module TacticianLearnerType)) : unit = ()
