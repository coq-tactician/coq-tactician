open Tactic_learner
open Learner_helper

(*
let proof_state_feats_to_feats {hypotheses = hyps; goal = goal} =
  let s2is = List.map (function
      | Leaf s -> int_of_string s
      | _ -> assert false) in
  let hf = List.map (fun (id, hyp) -> match hyp with
      | Node [Leaf "LocalAssum"; Node fs] -> s2is fs
      | Node [Leaf "LocalDef"; Node fs1; Node fs2] -> s2is (fs1 @ fs2)
      | _ -> assert false
    ) hyps in
  let gf = match goal with
    | Node gf -> s2is gf
    | _ -> assert false in
  gf @ List.flatten hf
*)

module NaiveKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

  module IntMap = Stdlib.Map.Make(struct type t = int
      let compare = Int.compare end)

  let remove_dups_and_sort ranking =
    let ranking_map = List.fold_left
        (fun map (score, tac) ->
           IntMap.update
             (tactic_hash tac)
             (function
               | None -> Some (score, tac)
               | Some (lscore, ltac) ->
                 if score > lscore then Some (score, tac) else Some (lscore, ltac)
             )
             map
        )
        IntMap.empty
        ranking
    in
    let new_ranking = List.map (fun (hash, (score, tac)) -> (score, tac)) (IntMap.bindings ranking_map) in
    List.sort (fun (x, _) (y, _) -> Float.compare y x) new_ranking

  let proof_state_to_ints ps =
    let feats = proof_state_to_features 2 ps in
    (* print_endline (String.concat ", " feats); *)

    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev (List.rev_map Hashtbl.hash feats) in
    List.sort_uniq Int.compare feats

    type feature = int
    module FeatureOrd = struct
        type t = feature
        let compare = Int.compare
    end
    module Frequencies = Map.Make(FeatureOrd)
    type db_entry =
        { features : feature list;
          obj      : tactic
        }
    type database =
        { entries     : db_entry list
        ; length      : int
        ; frequencies : int Frequencies.t}

    type model = database

    let default d opt = match opt with | None -> d | Some x -> x

    let empty () = {entries = []; length = 0; frequencies = Frequencies.empty}

    let rec deletelast = function
      | [] -> assert false
      | [x] -> (x.features, [])
      | x::ls' -> let (last, lsn) = deletelast ls' in (last, x::lsn)

    let add db b obj =
      let feats = proof_state_to_ints b in
      let comb = {features = feats; obj = obj} in
      let newfreq = List.fold_left
          (fun freq f ->
             Frequencies.update f (fun y -> Some ((default 0 y) + 1)) freq)
          db.frequencies
          feats in
      let max = 1000 in
      let last, purgedentries = if db.length >= max then deletelast db.entries else ([], db.entries) in
      let newfreq = List.fold_left
          (fun freq f ->
             Frequencies.update f (fun y -> Some ((default 1 y) - 1)) freq)
          newfreq
          last in
      (* TODO: Length needs to be adjusted if we want to use multisets  *)
      let l = if db.length >= max then db.length else db.length + 1 in
      {entries = comb::purgedentries; length = l; frequencies = newfreq}

    let learn db outcomes tac =
      List.fold_left (fun a out -> add db out.before tac) db outcomes

    (* TODO: This doesn't work on multisets *)
    let rec intersect l1 l2 =
      match l1 with
      | [] -> []
      | h1::t1 -> (
          match l2 with
          | [] -> []
          | h2::t2 when compare h1 h2 < 0 -> intersect t1 l2
          | h2::t2 when compare h1 h2 > 0 -> intersect l1 t2
          | h2::t2 -> (
              match intersect t1 t2 with
              | [] -> [h1]
              | h3::t3 as l when h3 = h1 -> l
              | h3::t3 as l -> h1::l
            )
        )

    let tfidf db ls1 ls2 =
        let inter = intersect ls1 ls2 in
        let size = db.length in
        List.fold_left (+.) 0.
            (List.map
                (fun f -> Float.log ((Float.of_int (1 + size)) /.
                                     (Float.of_int (1 + (default 0 (Frequencies.find_opt f db.frequencies))))))
                inter)

    let predict db f =
      if f = [] then Stream.of_list [] else
      let feats = proof_state_to_ints (List.hd (List.rev f)).state in
      let tdidfs = List.map
          (fun ent -> let x = tfidf db feats ent.features in (x, ent.obj))
          db.entries in
      let out = remove_dups_and_sort tdidfs in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      Stream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "naive-knn" (module NaiveKnn)
