open Tactic_learner
open Learner_helper

module OnlineForest : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
    module LH = L(TS)
    open TS
    open LH
    module Tree = Tree_online.Make(Data)
    module Forest = Forest_online.Make(Data)

    type model = (TS.tactic Tree.tree) list

    let empty () = []

    let add forest b obj =
      let feats = proof_state_to_ints b in
      Forest.add forest (Data.labeled (feats, obj))

    let learn db _loc outcomes tac =
      List.fold_left (fun db out -> add db out.before tac) db outcomes

    let predict forest f =
      if f = [] then IStream.empty else
      let feats = proof_state_to_ints (List.hd f).state in
      let example = Data.unlabeled feats in
      let out = Forest.score forest example in
      let out = remove_dups_and_sort out in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "online-forest" (module OnlineForest)
