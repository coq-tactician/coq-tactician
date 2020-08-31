open Tactic_learner
open Learner_helper

module NullLearner : TacticianLearnerType = struct
  type t = unit
  let create () = ()
  let add db ~memory:_ ~before:_ tac ~after:_ = ()
  let predict db ls = []
end

module ReverseAddedOrder : TacticianLearnerType = struct
  type t = tactic list
  let create () = []
  let add db ~memory:_ ~before:_ tac ~after:_ = tac::db
  let predict db ls = List.map (fun tac -> (1., focus_first ls, tac)) db
end

module AddedOrder : TacticianLearnerType = struct
  type t = tactic list
  let create () = []
  let add db ~memory:_ ~before:_ tac ~after:_ = tac::db
  let predict db ls = List.map (fun tac -> (1., focus_first ls, tac)) (List.rev db)
end

module Random : TacticianLearnerType = struct
  type t = tactic list

  let create () = []
  let add db ~memory:_ ~before:_ tac ~after:_ = tac::db

  let shuffle d =
    let nd = List.map (fun c -> (Random.bits (), c)) d in
    let sond = List.sort compare nd in
    List.map snd sond

  let predict db ls =
    List.map (fun tac -> (1., focus_first ls, tac)) (shuffle db)
end

(* let () = register_learner "ReverseAddedOrder" (module ReverseAddedOrder) *)
