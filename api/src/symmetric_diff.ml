open CMap

module Make(M : Map.OrderedType)
    (Map : ExtS with
      type key = M.t
    ) : sig
  val symmetric_diff :
    eq:('a -> 'a -> bool) ->
    (Map.key -> [ `Left of 'a | `Right of 'a | `Unequal of 'a * 'a ] -> 'b -> 'b) ->
    'a Map.t -> 'a Map.t -> 'b -> 'b
end = struct

  [@@@warning "-37"]
  type 'a map =
    | MEmpty
    | MNode of {l:'a Map.t; v:Map.key; d:'a; r:'a Map.t; h:int}
  [@@@warning "+37"]

  let map_prj : 'a Map.t -> 'a map = Obj.magic

  type 'a sequenced =
    | End
    | More of Map.key * 'a * 'a Map.t * 'a sequenced

  let rec seq_cons m rest =
    match map_prj m with
    | MEmpty -> rest
    | MNode {l; v; d; r; _ } -> seq_cons l (More (v, d, r, rest))

  let rec fold_seq f acc = function
    | End -> acc
    | More (k, v, m, r) -> f k v @@ fold_seq f (Map.fold f m acc) r

  let move_to_acc (m, acc) = match map_prj m with
    | MEmpty -> assert false
    | MNode {l; v; d; r; _ } -> l, More (v, d, r, acc)

  let rec symmetric_cons ((lm, la) as l) ((rm, ra) as r) =
    if lm == rm then la, ra
    else
      let lh = Map.height lm in
      let rh = Map.height rm in
      if lh == rh then
        symmetric_cons (move_to_acc l) (move_to_acc r)
      else if lh < rh then
        symmetric_cons l (move_to_acc r)
      else
        symmetric_cons (move_to_acc l) r

  let symmetric_diff ~eq f lm rm acc =
    let rec aux s acc =
      match s with
      | End, rs -> fold_seq (fun k v -> f k (`Right v)) acc rs
      | ls, End -> fold_seq (fun k v -> f k (`Left v)) acc ls
      | (More (kl, vl, tl, rl) as ls), (More (kr, vr, tr, rr) as rs) ->
        let cmp = M.compare kl kr in
        if cmp == 0 then
          let rem = aux (symmetric_cons (tl, rl) (tr, rr)) acc in
          if eq vl vr then rem
          else f kl (`Unequal (vl, vr)) rem
        else if cmp < 0 then
          f kl (`Left vl) @@ aux (seq_cons tl rl, rs) acc
        else
          f kr (`Right vr) @@ aux (ls, seq_cons tr rr) acc
    in aux (symmetric_cons (lm, End) (rm, End)) acc
  end

module HMapMake(M : Map.OrderedType)
    (Map : ExtS with
      type key = M.t
    ) : sig
  val symmetric_diff :
    eq:('a -> 'a -> bool) ->
    (Map.key -> [ `Left of 'a | `Right of 'a | `Unequal of 'a * 'a ] -> 'b -> 'b) ->
    'a Map.t -> 'a Map.t -> 'b -> 'b
end = struct
  module InternalSym = Make(Int)(
      struct
        include Int.Map
        module Set = Int.Set
      end)
  module InternalMap = CMap.Make(M)
  module InternalSym2 = Make(M)(
    struct
      include InternalMap
      module Set = Set.Make(M)
    end)
  let map_prj : 'a Map.t -> 'a InternalMap.t Int.Map.t = Obj.magic
  let symmetric_diff ~eq f lm rm acc =
    InternalSym.symmetric_diff ~eq:(InternalMap.equal eq)
      (fun _ s acc -> match s with
         | `Left v -> InternalMap.fold (fun k v acc -> f k (`Left v) acc) v acc
         | `Right v -> InternalMap.fold (fun k v acc -> f k (`Right v) acc) v acc
         | `Unequal (lm, rm) -> InternalSym2.symmetric_diff ~eq f lm rm acc)
      (map_prj lm) (map_prj rm) acc
end
