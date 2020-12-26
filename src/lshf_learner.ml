open Tactic_learner
open Learner_helper
open Util

module LSHF : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

  let depth = 15
  let trie_count = 10

  let proof_state_to_ints ps =
    let feats = proof_state_to_features 2 ps in
    (* print_endline (String.concat ", " feats); *)

    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev (List.rev_map Hashtbl.hash feats) in
    List.sort_uniq Int.compare feats


  type features = int list
  type 'a trie =
    | Leaf of ('a * features) list
    | Node of 'a trie * 'a trie

  type hash = int -> int

  type 'a lsh_trie =
    { hashes : hash list
    ; trie   : 'a trie }

  type 'a forest = 'a lsh_trie list

  (* TODO: Would it be beneficial to initialize this better? *)
  let random = Random.State.make [||]

  let init_trie depth =
    let mk_hash _ =
      let seed = Random.State.bits random in
      Hashtbl.seeded_hash seed in
    { hashes = List.init depth mk_hash
    ; trie   = Leaf [] }

  let min_hash h feats =
    (* Empty `feats` hashing to the same `max_int` value is okay, because then
       all empty objects collide. Note that the hash functions never produce `max_int`. *)
    let min = List.fold_left (fun m x -> min m (h x)) max_int feats in
    min mod 2 = 0

  let insert f feats elem =
    let extend hashes feats2 elem2 =
      let rec extend hashes = match hashes with
        | []        -> Leaf [elem, feats; elem2, feats2]
        | h::hashes -> match min_hash h feats, min_hash h feats2 with
          | true , true  -> Node (Leaf []      , extend hashes)
          | false, false -> Node (extend hashes, Leaf [])
          | true , false -> Node (Leaf [elem , feats] , Leaf [elem2, feats2])
          | false, true  -> Node (Leaf [elem2, feats2], Leaf [elem , feats]) in
      extend hashes in
    let insert { hashes; trie } =
      let rec insert hashes trie = match hashes, trie with
        | _        , Leaf []              -> Leaf [elem, feats]
        | _::_     , Leaf [elem2, feats2] -> extend hashes feats2 elem2
        | _::_     , Leaf _               -> CErrors.anomaly (Pp.str "LSHF invariant violated")
        | []       , Leaf ls              -> Leaf ((elem, feats) :: ls)
        | []       , Node _               -> CErrors.anomaly (Pp.str "LSHF invariant violated")
        | h::hashes, Node (l, r)          ->
          if min_hash h feats then Node (l, insert hashes r) else Node (insert hashes l, r)
      in
      {hashes; trie = insert hashes trie} in
    List.map insert f

  let rec collect = function
    | Leaf ls -> ls
    | Node (l, r) -> collect l @ collect r

  let query f feats max =
    let select_relevant { hashes; trie } = match hashes, trie with
      | _, Leaf _ -> None
      | [], Node _ -> CErrors.anomaly (Pp.str "LSHF invariant violated")
      | h::hashes, Node (l, r) ->
        Some { hashes; trie = if min_hash h feats then r else l } in
    let select_irrelevant { hashes; trie } = match hashes, trie with
      | _, Leaf _ -> trie
      | [], Node _ -> CErrors.anomaly (Pp.str "LSHF invariant violated")
      | h::_, Node (l, r) -> if min_hash h feats then l else r in
    let rec query f =
      let filtered = List.filter_map select_relevant f in
      let res, c = if List.is_empty filtered then [], 0 else query filtered in
      if c >= max then res, c else
        let res' = List.concat @@ List.map collect @@ List.map select_irrelevant f in
        res @ res', List.length res' + c in
    query f

  type model = tactic forest

  let empty () = List.init trie_count @@ fun _ -> init_trie depth

  let learn db outcomes tac =
    List.fold_left (fun db out -> insert db (proof_state_to_ints out.before) tac) db outcomes

  let predict db f =
    if f = [] then Stream.of_list [] else
      let feats = proof_state_to_ints (List.hd f).state in
      let tacs, _ = query db feats 100 in
      Stream.of_list @@ List.map (fun (tac, _) -> { confidence = 1.; focus = 0; tactic = tac }) tacs

  let evaluate db _ _ = 1., db

end

let () = register_online_learner "LSHF" (module LSHF)
