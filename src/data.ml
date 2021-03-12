module type DATA_CONCRETE = sig
    type features
    type indices = int list
    type 'a example = (features * ('a option))
    type 'a examples = {
        indices : int list;
        universe : (int, 'a example) Hashtbl.t}
    type rule = features -> bool
    type 'a split_rule = 'a examples -> 'a examples * 'a examples
    val labels : 'a examples -> 'a list
    val features : 'a example -> features
    val label : 'a example -> 'a
    val random_rule : 'a examples -> rule
    val gini_rule : ?m:int -> 'a examples -> rule
end;;

module Make = functor (D : DATA_CONCRETE) -> struct
    include D


    let indices {D.indices; D.universe} =
        indices

(*
    let empty =
        let universe : (int, 'a example) Hashtbl.t = Hashtbl.create 10000 in
        {D.indices=[]; D.universe=universe}
*)

    let is_empty {indices; universe} =
        indices = []

    let first_label {D.indices; D.universe} =
        let i = match indices with
        | i :: _ -> i
        | [] -> failwith "empty examples" in
        label (Hashtbl.find universe i)

    let random_label {D.indices; D.universe} =
        let i = Utils.choose_random indices in
        label (Hashtbl.find universe i)

    let random_subset {D.indices; D.universe} =
        let random_indices =
            Utils.sample_with_replace indices (List.length indices) in
        {D.indices=random_indices; D.universe}

    let uniform_labels examples =
        let labels = labels examples in
        let rec uniform labels =
            match labels with
            | [] | [_] -> true
            | h1 :: h2 :: t ->
                if h1 = h2 then uniform (h2 :: t) else false in
        uniform labels

    let split rule {D.indices; D.universe} =
        let rec loop inds_l inds_r = function
            | [] -> (inds_l, inds_r)
            | h :: t ->
                match rule (features (Hashtbl.find universe h)) with
                | true -> loop (h :: inds_l) inds_r t
                | false -> loop inds_l (h :: inds_r) t in
        let inds_l, inds_r = loop [] [] indices in
        ({D.indices = inds_l; D.universe},
         {D.indices = inds_r; D.universe})

    let length {D.indices; D.universe} =
        List.length indices

    let random_example {D.indices; D.universe} =
        let i = Utils.choose_random indices in
        {D.indices=[i]; D.universe=universe}

    let add {D.indices; D.universe} (features, label) =
        let example = (features, Some label) in
        let i = Hashtbl.hash example in
        Hashtbl.add universe i example;
        {D.indices = [i]; D.universe = universe}

    let add_unlabeled {D.indices; D.universe} features =
        let example = (features, None) in
        let i = Hashtbl.hash example in
        Hashtbl.add universe i example;
        {D.indices = [i]; D.universe = universe}

    let append {D.indices=indices1; D.universe=universe1}
               {D.indices=indices2; D.universe=universe2} =
    assert (universe1 == universe2);
    let new_indices = List.append indices1 indices2 in
    {D.indices=new_indices; D.universe=universe1}

    let get {D.indices; D.universe} i =
        {D.indices=[i]; D.universe}

    let fold_left f s examples =
        let f' acc i = f acc (get examples i) in
        List.fold_left f' s examples.indices

end
