type id = Tactic_learner_internal.id

module IdMap = Tactic_learner_internal.IdMap
type id_map = Tactic_learner_internal.id_map

type sexpr = Sexpr.sexpr = Node of sexpr list | Leaf of string

module type TacticianStructures = Tactic_learner_internal.TacticianStructures

type data_status = Tactic_learner_internal.data_status = Original | Substituted | Discharged

module type TacticianOnlineLearnerType = Tactic_learner_internal.TacticianOnlineLearnerType
module type TacticianOfflineLearnerType = Tactic_learner_internal.TacticianOfflineLearnerType

let register_online_learner = Tactic_learner_internal.register_online_learner
let register_offline_learner = Tactic_learner_internal.register_offline_learner
