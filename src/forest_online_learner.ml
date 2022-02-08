open Tactic_learner
open Learner_helper
open Features

module OnlineForest : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
    module LH = L(TS)
    module FH = F(TS)
    open FH
    open TS
    open LH
    module Tree = Tree_online.Make(Data)
    module Forest = Forest_online.Make(Data)

    type model = (TS.tactic Tree.tree) list
(*         {trees : (TS.tactic Tree.tree) list; perf : float list; n : float} *)

(*     let empty () = {Forest.trees=[]; Forest.perf=[]; Forest.n=0.} *)
    let empty () = Forest.empty

    let add forest b obj =
      let feats = proof_state_to_complex_ints_no_kind b in
      Forest.add
      ~min_impur:0.5
      ~n_trees:100
      ~part:0.3
      forest (Data.labeled (feats, obj))

    let learn db _loc outcomes tac =
      List.fold_left (fun db out -> add db out.before tac) db outcomes

    let predict forest f =
      if f = [] then IStream.empty else
      let feats = proof_state_to_complex_ints_no_kind (List.hd f).state in
      let example = Data.unlabeled feats in
      let out = Forest.score forest example in
      let out = List.map (fun (x, y) -> (y, x)) out in
      let out = remove_dups_and_sort out in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "online-forest" (module OnlineForest)
