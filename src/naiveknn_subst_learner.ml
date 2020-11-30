open Tactic_learner
open Learner_helper
open Context
open Names

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

  let proof_state_to_ints ps =
    let feats = proof_state_to_features 2 ps in
    (* print_endline (String.concat ", " feats); *)

    (* Tail recursive version of map, because these lists can get very large. *)
    let feats = List.rev (List.rev_map Hashtbl.hash feats) in
    List.sort_uniq Int.compare feats

  let context_to_ints ctx =
    let ctx = context_features 2 ctx in
    let to_ints feats = List.sort_uniq Int.compare (List.rev_map Hashtbl.hash feats) in
    context_map to_ints to_ints ctx

    type feature = int
    module FeatureOrd = struct
        type t = feature
        let compare = Int.compare
    end
    module Frequencies = Map.Make(FeatureOrd)
    type db_entry =
      { features : feature list;
        context  : (feature list, feature list) Context.Named.pt;
        obj      : tactic;
        substituted_hash : int
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

    let decl2id = function
      | Named.Declaration.LocalAssum (id, _) -> id.binder_name
      | Named.Declaration.LocalDef (id, _, _) -> id.binder_name

    let find_decl ctx id =
      List.find_opt (function
          | Named.Declaration.LocalAssum (id', _) -> Id.equal id id'.binder_name
          | Named.Declaration.LocalDef (id', _, _) -> Id.equal id id'.binder_name
        ) ctx

    let decl2feats = function
      | Named.Declaration.LocalAssum (_, typ) -> typ
      | Named.Declaration.LocalDef (_, _, typ) -> typ

    let tactic_simplified_hash ctx tac =
      let tac = Tactic_substitute.tactic_substitute (fun id ->
          match find_decl ctx id with
          | None -> Id.of_string "__knnpl"
          | Some _ -> id)
          (tactic_repr tac) in
      tactic_hash (tactic_make tac)


    let add db b obj =
      let feats = proof_state_to_ints b in
      let ctx = context_to_ints (proof_state_hypotheses b) in
      let sh = tactic_simplified_hash ctx obj in
      let comb = {features = feats; context = ctx; obj = obj; substituted_hash = sh} in
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
      List.fold_left (fun db out -> add db out.before tac) db outcomes

    (* TODO: This doesn't work on multisets *)
    let rec intersect l1 l2 =
      match l1 with
      | [] -> []
      | h1::t1 -> (
          match l2 with
          | [] -> []
          | h2::_ when compare h1 h2 < 0 -> intersect t1 l2
          | h2::t2 when compare h1 h2 > 0 -> intersect l1 t2
          | _::t2 -> (
              match intersect t1 t2 with
              | [] -> [h1]
              | h3::_ as l when h3 = h1 -> l
              | _::_ as l -> h1::l
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

    let remove_dups ranking =
      let ranking_map = List.fold_left
          (fun map (score, ({obj; substituted_hash; _} as entry)) ->
             (* TODO: this is a total hack *)
             IntMap.update
               (tactic_hash obj (* (tactic_make tac') *))
               (function
                 | None -> Some (score, entry)
                 | Some (lscore, ltac) ->
                   if score > lscore then Some (score, entry) else Some (lscore, ltac)
               )
               map
          )
          IntMap.empty
          ranking
      in
      List.map (fun (_hash, (score, tac)) -> (score, tac)) (IntMap.bindings ranking_map)

    let predict db f =
      if f = [] then Stream.of_list [] else
        let ps = (List.hd f).state in
        let ctx = context_to_ints (proof_state_hypotheses ps) in
        let feats = proof_state_to_ints ps in
        let tdidfs = List.map
            (fun ent -> let x = tfidf db feats ent.features in (x, ent))
            db.entries in
        (* let subst = List.map (fun (f, ({context; obj; _} as entry)) ->
         *     let subst id =
         *       match find_decl context id with
         *       | None -> id
         *       | Some decl ->
         *         let feats = decl2feats decl in
         *         let ids_scored = List.map
         *             (fun decl -> let x = tfidf db feats (decl2feats decl) in (x, decl2id decl))
         *             ctx in
         *         let ids_sorted = List.sort (fun (x, _) (y, _) -> Float.compare y x) ids_scored in
         *         match ids_sorted with
         *         | [] -> id
         *         | (_, id)::_ -> id
         *     in
         *     let tactic = tactic_make (Tactic_substitute.tactic_substitute subst (tactic_repr obj)) in
         *     f, {entry with obj = tactic}) tdidfs in *)
        (* TODO: This is a totally random decision *)
        let combined = tdidfs (* @ List.map (fun (s, o) -> s /. 100., o) subst *) in
        let deduped = remove_dups combined in
        let sorted = List.stable_sort (fun (x, _) (y, _) -> Float.compare y x) deduped in
        let out = List.map (fun (a, entry) -> { confidence = a; focus = 0; tactic = entry.obj }) sorted in
        Stream.of_list out

    let evaluate db _ _ = 1., db

end

let () = register_online_learner "naive-knn" (module NaiveKnn)
