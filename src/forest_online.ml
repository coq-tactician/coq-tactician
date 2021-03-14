module Make = functor (Data : Tree_online.DATA) -> struct
    module Tree = Tree_online.Make(Data)

    let empty = []

    let add forest example =
        let n_trees = List.length forest in
        let add_new_tree = (n_trees = 0) || (Random.int n_trees = 0) in
        let remove_old_tree = (n_trees > 0) && (Random.int n_trees) > 300 in
        let forest =
            if remove_old_tree then Utils.remove_last forest else forest in
        let updated_trees =
            List.map (fun tree -> Tree.add tree example) forest in
        if add_new_tree then Tree.leaf example :: updated_trees else updated_trees

    let forest examples =
        Data.fold_left add empty examples

    let vote votes =
        let sorted = List.sort compare votes in
        let rec loop occ sorted =
            match sorted, occ with
            | [], _ -> occ
            | h :: t, [] -> loop [(h, 1)] t
            | h :: t, (e, c) :: t2 ->
                if h = e
                then loop ((e, c + 1) :: t2) t
                else loop ((h, 1) :: (e, c) :: t2) t
        in
        let occurs = loop [] sorted in
        let sum = float_of_int (List.length votes) in
        let freqs =
            List.map (fun (e, c) -> (e, (float_of_int c) /. sum)) occurs in
        List.sort (fun (_, c1) (_, c2) -> compare c2 c1) freqs

    let classify forest example =
        let votes = List.map (Tree.classify example) forest in
        match vote votes with
        | (e, _) :: _ -> e
        | [] -> failwith "empty list of voting scores"

    let score forest unlabeled_example =
        let votes = List.map (Tree.classify unlabeled_example) forest in
        List.map (fun (a, b) -> (b, a) ) (vote votes)

end
