module Id = Tactic_learner_internal.Id
type id = Tactic_learner_internal.id

module IdMap = Tactic_learner_internal.IdMap
type id_map = Tactic_learner_internal.id_map

type sentence = Tactic_learner_internal.sentence = Node of sentence list | Leaf of string

type proof_state = Tactic_learner_internal.proof_state =
{ hypotheses : (id * sentence) list
; goal       : sentence }

type tactic = Tactic_learner_internal.tactic
let tactic_sentence = Tactic_learner_internal.tactic_sentence
let local_variables = Tactic_learner_internal.local_variables
let substitute = Tactic_learner_internal.substitute

module type TacticianLearnerType = Tactic_learner_internal.TacticianLearnerType
let register_learner = Tactic_learner_internal.register_learner
