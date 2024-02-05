open Tactic_learner
open Learner_helper
open Features

module CircularQueue : sig
  type 'a t
  val empty : int -> 'a t
  val add : 'a -> 'a t -> 'a option * 'a t
  val to_list_map : ('a -> 'b) -> 'a t -> 'b list
  val size : 'a t -> int
  val max : 'a t -> int
end = struct
  type 'a t =
    { max      : int
    ; size     : int
    ; incoming : 'a list
    ; outgoing : 'a list }

  let empty max = { size = 0; max; incoming = []; outgoing = [] }

  let head_tail ls = List.hd ls, List.tl ls

  let add x { max; size; incoming; outgoing } =
    if size < max then begin
      assert (outgoing = []);
      None, { max; size = size + 1; incoming = x::incoming; outgoing }
      end
    else begin
      assert (size = max);
      match outgoing with
      | [] ->
        let out, outgoing = head_tail @@ List.rev (x::incoming) in
        Some out, { max; size; incoming = []; outgoing }
      | out::outgoing ->
        Some out, { max; size; incoming = x::incoming; outgoing }
    end

  let to_list_map f { incoming; outgoing; _ } =
    let tail = List.fold_right (fun x -> List.cons (f x)) outgoing [] in
    List.fold_left (fun ls x -> List.cons (f x) ls) tail incoming

  let size { size; _ } = size
  let max { max; _ } = max

end

module NaiveKnn = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

  type db_entry =
    { features : feature list;
      obj      : tactic
    }
  type database =
    { entries     : db_entry CircularQueue.t
    ; frequencies : int Frequencies.t}

  type model = database

  let max = 1000
  let empty () = {entries = CircularQueue.empty max; frequencies = Frequencies.empty}

  let add { entries; frequencies } b obj to_feat =
    let features = to_feat b in
    let comb = { features; obj } in
    let frequencies = List.fold_left
        (fun freq f ->
           Frequencies.update f (fun y -> Some ((Option.default 0 y) + 1)) freq)
        frequencies
        features in
    let out, entries = CircularQueue.add comb entries in
    let frequencies = Option.cata (fun out ->
        List.fold_left
          (fun freq f ->
             Frequencies.update f (fun y -> Some ((Option.default 1 y) - 1)) freq)
          frequencies out.features)
        frequencies out in
    { entries; frequencies }

  let learn db _status outcomes tac to_feat =
    List.fold_left (fun db out -> add db out.before tac to_feat) db outcomes

  let predict { entries; frequencies } f to_feat tfidf =
    if f = [] then IStream.empty else
      let feats = to_feat (List.hd f).state in
      let length = CircularQueue.size entries in
      let tdidfs = CircularQueue.to_list_map
          (fun ent -> let x = tfidf length frequencies feats ent.features in (x, ent.obj))
          entries in
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
  let learn db _status outcomes tac = learn db _status outcomes tac proof_state_to_simple_ints
  let predict db f = predict db f proof_state_to_simple_ints tfidf
end

module ComplexNaiveKnn : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module NaiveKnn = NaiveKnn(TS)
  include NaiveKnn
  module FH = F(TS)
  open FH
  let learn db _status outcomes tac = learn db _status outcomes tac
      proof_state_to_complex_ints_no_kind
  let predict db f = predict db f proof_state_to_complex_ints manually_weighed_tfidf

end

(* let () = register_online_learner "simple-naive-knn" (module SimpleNaiveKnn) *)
let () = register_online_learner "complex-naive-knn" (module ComplexNaiveKnn)
