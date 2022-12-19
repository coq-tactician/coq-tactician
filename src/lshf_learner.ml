open Tactic_learner
open Learner_helper
open Features
open Util

type features =  int list
type 'a trie =
  | Leaf of ('a * features) list
  | Node of 'a trie * 'a trie

type hash = int -> int

type 'a lsh_trie =
  { hashes : int list
  ; trie   : 'a trie }

type 'a forest = 'a lsh_trie list

let init_trie random depth =
  let mk_hash _ =
    let seed = Random.State.bits random in
    seed in
  { hashes = List.init depth mk_hash
  ; trie   = Leaf [] }

let min_hash h feats =
  let h = Hashtbl.seeded_hash h in
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

let depth = Goptions.declare_int_option_and_ref
    ~stage:Summary.Stage.Interp ~depr:false ~key:["Tactician"; "LSHF"; "Depth"] ~value:9
let trie_count = Goptions.declare_int_option_and_ref
    ~stage:Summary.Stage.Interp ~depr:false ~key:["Tactician"; "LSHF"; "Trie"; "Count"] ~value:11
let sort_window = Goptions.declare_int_option_and_ref
    ~stage:Summary.Stage.Interp ~depr:false ~key:["Tactician"; "LSHF"; "Sort"; "Window"] ~value:1000

module LSHF =
  functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

  (* TODO: Would it be beneficial to initialize this better? *)
  let random = Random.State.make [||]

  type model =
    { forest : tactic forest
    ; length : int
    ; frequencies : int Frequencies.t }

  let empty () =
    { forest = List.init (trie_count ()) (fun _ -> init_trie random (depth ()))
    ; length = 0
    ; frequencies = Frequencies.empty }

  let add db b obj to_feats =
    let feats = to_feats b in
    let frequencies = List.fold_left
        (fun freq f ->
           Frequencies.update f (fun y -> Some ((Option.default 0 y) + 1)) freq)
        db.frequencies
        feats in
    (* TODO: Length needs to be adjusted if we want to use multisets  *)
    let length = db.length + 1 in
    let forest = insert db.forest feats obj in
    { forest; length; frequencies }

  let learn db (_kn, _path, _status) outcomes tac to_feats =
    List.fold_left (fun db out -> add db out.before tac to_feats) db outcomes

  let predict db f to_feats remove_kind tfidf =
    if f = [] then IStream.of_list [] else
      let feats = to_feats (List.hd f).state in
      let candidates, _ = query db.forest (remove_kind feats) (sort_window ()) in
      let tdidfs = List.map
          (fun (o, f) -> let x = tfidf db.length db.frequencies feats f in (x, o))
          candidates in
      let out = remove_dups_and_sort tdidfs in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

  let evaluate db _ _ = 1., db

end

module SimpleLSHF : TacticianOnlineLearnerType =
  functor (TS : TacticianStructures) -> struct
    module LSHF = LSHF(TS)
    include LSHF
    module FH = F(TS)
    open FH
  let learn db _status outcomes tac = learn db _status outcomes tac proof_state_to_simple_ints
  let predict db f = predict db f proof_state_to_simple_ints (fun x -> x) tfidf
end

module ComplexLSHF : TacticianOnlineLearnerType =
  functor (TS : TacticianStructures) -> struct
    module LSHF = LSHF(TS)
    include LSHF
    module FH = F(TS)
    open FH
    let learn db _status outcomes tac = learn db _status outcomes tac
        proof_state_to_complex_ints_no_kind
    let predict db f = predict db f proof_state_to_complex_ints (List.map snd) manually_weighed_tfidf
  end

(* let () = register_online_learner "SimpleLSHF" (module SimpleLSHF) *)
let () = register_online_learner "ComplexLSHF" (module ComplexLSHF)
