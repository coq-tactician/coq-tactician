open Tactic_learner
open Learner_helper

module OnlineForest : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
    module LH = L(TS)
    open TS
    open LH
    module Data = Data.Make(Sparse)
    module Tree = Tree_online.Make(Data)
    module Forest = Forest_online.Make(Data)
    open Data


    type model = (TS.tactic Tree.tree) list

    let empty () = []

    let add (db : model) b obj =
      let feats = proof_state_to_ints b in
      let feats = Sparse.ISet.of_list feats in
(*       let label = tactic_hash obj in *)
      let label = obj in
      let example = {features = feats; label = Some label} in
      Forest.add db example

    let learn db _loc outcomes tac =
      List.fold_left (fun db out -> add db out.before tac) db outcomes

    let predict db f =
      if f = [] then IStream.empty else
      let feats = proof_state_to_ints (List.hd f).state in
      let feats = Sparse.ISet.of_list feats in
      let example = {features = feats; label = None} in
      let out = Forest.classify_1 db example in
      let out = remove_dups_and_sort out in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "online-forest" (module OnlineForest)
