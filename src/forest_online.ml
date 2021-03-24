module Make = functor (Data : Tree_online.DATA) -> struct
    module Tree = Tree_online.Make(Data)

    let empty = []

    let add ?(n_feas=1) ?(min_impur=0.5) ?(max_depth=100) ?(n_trees=1000)
        forest example =
        let n = List.length forest in
        let must_add_tree = (n = 0) || (Random.int n = 0) in
        let must_remove_tree = (n > 0) && (Random.int n) > n_trees in
        let forest =
            if must_remove_tree then Utils.remove_last forest else forest in
        let updated_trees =
            List.map
            (fun tree -> Tree.add ~n_feas ~min_impur ~max_depth tree example)
            forest in
        if must_add_tree then Tree.leaf example :: updated_trees else updated_trees

    let forest examples =
        Data.fold_left add empty examples

    let vote votes =
        let freqs = Utils.freqs votes in
        List.sort (fun (_, c1) (_, c2) -> compare c2 c1) freqs

    let classify forest example =
        let votes = List.map (Tree.classify example) forest in
        match vote votes with
        | (e, _) :: _ -> e
        | [] -> failwith "empty list of voting scores"

    let score forest unlabeled_example =
        let votes = List.map (Tree.classify unlabeled_example) forest in
        vote votes

    let stats forest =
        let l = List.length forest in
        let ds_sum = List.fold_left (fun s t -> s + Tree.depth t) 0 forest in
        let ds_avg = (float_of_int ds_sum) /. (float_of_int l) in
        let ns_sum = List.fold_left (fun s t -> s + Tree.max_node t) 0 forest in
        let ns_sum_lab =
            List.fold_left (fun s t -> s + Tree.max_labels_node t) 0 forest in
        let ns_avg = (float_of_int ns_sum) /. (float_of_int l) in
        let ns_avg_lab = (float_of_int ns_sum_lab) /. (float_of_int l) in
        let () = Printf.printf "\nNumber of trees: %n\n" l in
        let () = Printf.printf "Avg depth of trees: %f\n" ds_avg in
        let () = Printf.printf "Avg largest node of trees: %f\n" ns_avg in
        let () = Printf.printf
            "Avg largest n. of labels in node of trees: %f\n" ns_avg_lab in
        ()

end
