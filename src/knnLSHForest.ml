open Tactic_learner
open Learner_helper

module OrigLSHF : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = L(TS)
  open TS
  open LH

    type obj = tactic

    type 'a trie =
        | Leaf of ('a * int list) option
        | BottomLeaf of 'a list
        | Node of 'a trie * 'a trie

    type db_entry =
        { signature : int list;
          trie_prefixes : int list list;
          features : int list;
          obj      : obj;
          hashed : int
        }

    module DbEntrySet = Set.Make(
                        struct
                            let compare = (fun a b -> compare  a.hashed b.hashed)
                            type t = db_entry
                        end )


    type database =
        { entries : db_entry list;
        length  : int;
        minhashFunctions : (int -> int) list;
        signatureLength : int;
        forest : db_entry trie list;
        tree_count : int;
        max_depth : int }

    type t = database
    type model = t

    exception TrieError of string

    let rec insert tree el prefix = match prefix with
        | [] -> (match tree with
            | Leaf None -> BottomLeaf [el]
            | Leaf _ -> raise (TrieError "Encountered non empty Leaf at max level")
            | BottomLeaf lst -> BottomLeaf (el::lst)
            | Node _ -> raise (TrieError "Encountered Node at maximum depth while inserting"))
        | bit::bits -> (match tree with
            | Leaf None -> Leaf (Some (el, prefix))
            | Leaf Some (x, remainingPrefix) -> insert (insert (Node (Leaf None, Leaf None)) x remainingPrefix) el prefix
            | BottomLeaf _ -> raise (TrieError "Encountered BottomLeaf while not at maximum depth during insertion")
            | Node (x, y) when bit = 0 -> Node ((insert x el bits), y)
            | Node (x, y) when bit = 1 -> Node (x, (insert y el bits))
            | Node _ -> raise (TrieError ("Invalid bit value " ^ (string_of_int bit))))

    [@@@ocaml.warning "-32"]
    let rec delete tree prefix = match prefix with
        | [] -> (match tree with
            | Leaf _ -> raise (TrieError "Encountered Leaf at maximum depth while deleting")
            | Node _ -> raise (TrieError "Encountered Node at maximum depth while deleting")
            | BottomLeaf [] | BottomLeaf (_::[]) -> Leaf None
            | BottomLeaf (_::xs) -> BottomLeaf xs)
        | bit::bits -> (match tree with
            | Leaf _ -> Leaf None
            | BottomLeaf _ -> raise (TrieError "Encountered BottomLeaf while not at maximum depth during deletion")
            | Node (x, y) when bit = 0 ->
                let new_x = delete x bits in
                (match (new_x, y) with
                    | (Leaf None, Leaf None) -> Leaf None
                    | (Leaf (Some (el, lst)), Leaf None) -> Leaf (Some (el, 0::lst))
                    | (Leaf None, Leaf (Some (el, lst))) -> Leaf (Some (el, 1::lst))
                    | (BottomLeaf (el::[]), Leaf None) -> Leaf (Some (el, [0]))
                    | (Leaf None, BottomLeaf (el::[])) -> Leaf (Some (el, [1]))
                    | _ -> Node (new_x, y))
            | Node (x, y) when bit = 1 ->
                let new_y = delete y bits in
                (match (x, new_y) with
                    | (Leaf None, Leaf None) -> Leaf None
                    | (Leaf (Some (el, lst)), Leaf None) -> Leaf (Some (el, 0::lst))
                    | (Leaf None, Leaf (Some (el, lst))) -> Leaf (Some (el, 1::lst))
                    | (BottomLeaf (el::[]), Leaf None) -> Leaf (Some (el, [0]))
                    | (Leaf None, BottomLeaf (el::[])) -> Leaf (Some (el, [1]))
                    | _ -> Node (x, new_y))
            | Node _ -> raise (TrieError ("Invalid bit value " ^ (string_of_int bit))))

    let get_generic_trie_child tree bit = match tree with
        | Leaf _ | BottomLeaf _ -> tree
        | Node (x, y) -> if bit == 0 then x else y

    let get_generic_trie_other_child tree bit = match tree with
        | Leaf _ | BottomLeaf _ -> tree
        | Node (x, y) -> if bit == 1 then x else y

    let is_leaf_or_bottom_leaf tree = match tree with
        | Leaf _ | BottomLeaf _ -> true
        | _ -> false

    let rec collect tree = match tree with
        | Leaf None -> []
        | Leaf (Some (el, _)) -> [el]
        | BottomLeaf lst -> lst
        | Node (x, y) -> List.rev_append (collect x) (collect y)

    let take n lst =
        let rec takehelper cur acc lst =
            match (cur, lst)
            with (num, _) when num == n -> ((List.rev acc), lst)
                | (_, []) -> ((List.rev acc), lst)
                | (num, hd::tl) -> (takehelper (cur+1) (hd::acc) tl)
        in
        takehelper 0 [] lst

    let splitIntoSublistsOfLengthN n lst =
        let rec splitHelper acc lst =
            match (take n lst)
                with (nTup, []) -> List.rev (nTup::acc)
                    | (nTup, rest) -> splitHelper (nTup::acc) rest
        in
        splitHelper [] lst

    let modulo x y =
        let remainder = x mod y in
        if remainder >= 0 then remainder else remainder + y

    let get_hash_maker =
        let bigPrime = 4611686018427387847 in
        (fun a b -> (fun x -> modulo (a*x + b) bigPrime))

    let get_random_62bit_int ()  =
        let a = Random.bits () in
        let b = Random.bits () in
        let c = (Random.bits ()) land 3 in
        ((a lsl 32) lor (b lsl 2) lor c)

    (*
    let create_n_hash_functions n =
        let hashMaker = get_hash_maker in
        let rec creator_rec n =
            if n == 0 then [] else (hashMaker (get_random_62bit_int ()) (get_random_62bit_int ()))  :: (creator_rec (n-1)) in
        creator_rec n
    *)

    let create_n_hash_functions n =
        let rec creator_rec n =
            if n == 0 then [] else (get_hash_maker (get_random_62bit_int ()) (get_random_62bit_int ()))  :: (creator_rec (n-1)) in
        creator_rec n

    let generateSignature db fl =
        let initialHashedList = (List.map Hashtbl.hash fl) in
        List.map (fun hash ->
            (*let hashedList = (List.map hash initialHashedList) in*)
            List.fold_left (fun min cur ->
                let currentHashed = hash cur in
                if min <= currentHashed then min else currentHashed)
            max_int initialHashedList) db.minhashFunctions

    let generate_lsh_signature db signature =
        (*Array.of_list (List.map (fun element -> (Hashtbl.hash element) mod 2) signature)*)
        (*Array.of_list (List.map (fun element -> (get_hash_maker 1575529902561734492 385728199332520566 element) land 1) signature)*)
        splitIntoSublistsOfLengthN db.max_depth (List.map (fun element -> (Hashtbl.hash element) land 1) signature)

    let get_minhash_similarity db sig1 sig2 =
        let count = (List.fold_left2 (fun count x y -> if x == y then count+1 else count) 0 sig1 sig2) in
        (float_of_int count) /. (float_of_int db.signatureLength)

    let add_to_forest db entry =
        List.map2
            (fun tree prefix -> insert tree entry prefix)
            db.forest entry.trie_prefixes

    let add db fl obj =
        let signatur = (generateSignature db fl) in
        let combined =
            {
                signature = signatur;
                trie_prefixes = generate_lsh_signature db signatur;
                features = fl;
                obj = obj;
                hashed = (Hashtbl.hash_param (db.signatureLength + 1) 100 (obj, signatur))
              } in
        { db with forest = add_to_forest db combined
        ; entries = combined :: db.entries
        ; length = db.length + 1 }

    (* rewinds the database to n-th state,
     * 0 being empty db
     * NOT IMPLEMENTED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
     *)
    (* let rec backto db n = if n < db.length then
     *     db.entries <- List.tl db.entries;
     *     db.length <- db.length - 1;
     *     backto db n *)

    let create () =
        let tree_count = 11 in
        let tree_max_depth = 9 in
        let minhash_count = tree_count*tree_max_depth in
        let () = Random.init 43 in
        {
            entries = [];
            length = 0;
            minhashFunctions = (create_n_hash_functions minhash_count);
            signatureLength = minhash_count;
            forest = (List.init tree_count (fun _ -> Leaf None));
            tree_count = tree_count;
            max_depth = tree_max_depth
        }

    let empty () = create ()

    [@@@ocaml.warning "-8"]
    let collect_neighbors db prefixes m =
        let rec collect_from_all tries =
            if List.for_all (fun (tree, _) -> is_leaf_or_bottom_leaf tree) tries
            then
                let collected = List.flatten (List.map (fun (tree, _) -> collect tree) tries) in
                (false, collected)
            else
                let new_tries_inter = List.filter (fun (tree, _) -> not (is_leaf_or_bottom_leaf tree) ) tries in
                let new_tries = List.map
                    (fun (tree, bits) -> match bits with
                       | bit::bits -> (get_generic_trie_child tree bit, bits)
                       | [] -> assert false)
                    new_tries_inter
                in
                let (short_circuit, collected) = collect_from_all new_tries in
                if short_circuit || (((List.length collected) >= (2*m)) (*&& (DbEntrySet.(of_list collected |> cardinal) >= m)*))
                then
                    (true, collected)
                else
                    let more_collected = List.flatten
                        (List.map
                            (fun (tree, bit::bits) ->
                                collect (get_generic_trie_other_child tree bit))
                            tries)
                    in
                    (false, List.rev_append collected more_collected)

        in
        let (_ ,neighbors) = collect_from_all (List.map2 (fun tree prefix -> (tree, prefix)) db.forest prefixes) in
        DbEntrySet.(of_list neighbors |> elements)

    let knn db fl =
        let featureSig = generateSignature db fl in
        let prefixes = generate_lsh_signature db featureSig in
        let neighbors = collect_neighbors db prefixes 100 in
        let jaccards = List.map
                         (fun ent -> let x = get_minhash_similarity db featureSig ent.signature in (x, ent.obj))
                         neighbors
        in
        (*let (jaccards, _) = take 100 jaccards in*)
        let jaccards = List.map (fun (float, obj) -> (float, obj)) jaccards in
        List.sort (fun (x, _) (y, _) -> Float.compare y x) jaccards

    let predict db f =
      if f = [] then IStream.empty else
        let feats = proof_state_to_ints (List.hd f).state in
        let preds = knn db feats in
        let out = List.map (fun (a, c) -> { confidence = a; focus = 0; tactic = c }) preds in
        IStream.of_list out

    let tolist db = List.map (fun ent -> (ent.features, ent.obj)) db.entries

    let count db = db.length

    let learn db _loc outcomes tac =
      List.fold_left (fun db out -> add db (remove_feat_kind (proof_state_to_ints out.before)) tac) db outcomes

    let evaluate db _ _ = 1., db
end

(* let () = register_online_learner "orig-lshf" (module OrigLSHF) *)