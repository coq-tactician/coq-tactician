open Tactic_learner
open Learner_helper

module OnlineForest : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
    module LH = L(TS)
    open TS
    open LH
    module Data = Data.Make(Sparse)
    module Tree = Tree_online.Make(Data)
    module Forest = Forest_online.Make(Data)

    type model = {
        forest : (TS.tactic Tree.tree) list;
        examples : TS.tactic Data.examples
    }

(*     let empty () = {forest = []; examples = Data.empty} *)

    let empty_examples =
    let universe : (int, TS.tactic Data.example) Hashtbl.t = Hashtbl.create 10000 in
    {Data.indices=[]; Data.universe=universe}
    let empty () = {forest = []; examples = empty_examples }

    let add model b obj =
      let feats = proof_state_to_ints b in
      let feats = Sparse.ISet.of_list feats in
      let label = obj in
      let example = Data.add model.examples (feats, label) in
      let updated_forest = Forest.add model.forest example in
      {forest=updated_forest; examples=model.examples}

    let learn db _loc outcomes tac =
      List.fold_left (fun db out -> add db out.before tac) db outcomes

    let predict model f =
      if f = [] then IStream.empty else
      let feats = proof_state_to_ints (List.hd f).state in
      let feats = Sparse.ISet.of_list feats in
      let example = Data.add_unlabeled model.examples feats in
      let out = Forest.classify_1 model.forest example in
      let out = remove_dups_and_sort out in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "online-forest" (module OnlineForest)
