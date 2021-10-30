open Tactic_learner
open Learner_helper
open Features

module NaiveKnn = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

  type db_entry =
    { features : feature list;
      obj      : tactic
    }
  type database =
    { entries     : db_entry list
    ; length      : int
    ; frequencies : int Frequencies.t}

  type model = database

  let empty () = {entries = []; length = 0; frequencies = Frequencies.empty}

  let rec deletelast = function
    | [] -> assert false
    | [x] -> (x.features, [])
    | x::ls' -> let (last, lsn) = deletelast ls' in (last, x::lsn)

  let add db b obj to_feat =
    let feats = to_feat b in
    let comb = {features = feats; obj = obj} in
    let newfreq = List.fold_left
        (fun freq f ->
           Frequencies.update f (fun y -> Some ((default 0 y) + 1)) freq)
        db.frequencies
        feats in
    let max = 2000 in
    let last, purgedentries = if db.length >= max then deletelast db.entries else ([], db.entries) in
    let newfreq = List.fold_left
        (fun freq f ->
           Frequencies.update f (fun y -> Some ((default 1 y) - 1)) freq)
        newfreq
        last in
    (* TODO: Length needs to be adjusted if we want to use multisets  *)
    let l = if db.length >= max then db.length else db.length + 1 in
    {entries = comb::purgedentries; length = l; frequencies = newfreq}

  let learn db _status _loc outcomes tac to_feat =
    List.fold_left (fun db out -> add db out.before tac to_feat) db outcomes

  let predict db f to_feat tfidf =
    if f = [] then IStream.empty else
      let feats = to_feat (List.hd f).state in
      let tdidfs = List.map
          (fun ent -> let x = tfidf db.length db.frequencies feats ent.features in (x, ent.obj))
          db.entries in
      let out = remove_dups_and_sort tdidfs in
      let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) out in
      IStream.of_list out

  let evaluate db _ _ = 1., db

end

module SimpleNaiveKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module NaiveKnn = NaiveKnn(TS)
  include NaiveKnn
  module FH = F(TS)
  open FH
  let learn db _status _loc outcomes tac = learn db _status _loc outcomes tac proof_state_to_simple_ints
  let predict db _ f = predict db f proof_state_to_simple_ints tfidf
end

module ComplexNaiveKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module NaiveKnn = NaiveKnn(TS)
  include NaiveKnn
  module FH = F(TS)
  open FH
  let learn db _status _loc outcomes tac = learn db _status _loc outcomes tac
      (fun x -> remove_feat_kind @@ proof_state_to_complex_ints x)
  let predict db _ f = predict db f proof_state_to_complex_ints manually_weighed_tfidf

end

(* let () = register_online_learner "simple-naive-knn" (module SimpleNaiveKnn) *)
(* let () = register_online_learner "complex-naive-knn" (module ComplexNaiveKnn) *)
