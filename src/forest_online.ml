module Make = functor (Data : Tree_online.DATA) -> struct
    module Tree = Tree_online.Make(Data)

    type 'a forest = {trees : ('a Tree.tree) list; perf : float list; n : float}

    let empty = {trees = []; perf = []; n = 0.}

    let add forest example =
        let trees = forest.trees in
        let n_trees = List.length trees in
        let add_new_tree = (n_trees = 0) || (Random.int n_trees = 0) in
        let preds = List.map (Tree.classify example) trees in
        let corr = List.map (( = ) (Data.label example)) preds in
        let n = forest.n in
        let update_perf (p, c) = match c with
            | true -> p +. (1. /. (n +. 1.)) *. (1. -. p)
            | false -> p *. (n /. (n +. 1.)) in
        let perf_corr = List.combine forest.perf corr in
        let updated_perf = List.map update_perf perf_corr in
        let updated_trees = List.map (fun tree -> Tree.add tree example) trees in
        let updated_trees, updated_perf = if add_new_tree
            then ((Tree.leaf example :: updated_trees), 1. :: updated_perf)
            else updated_trees, updated_perf in
        {trees=updated_trees; perf=updated_perf; n=n +. 1.}


    let forest examples =
        Data.fold_left add empty examples

    let vote votes =
        let freqs = Utils.freqs votes in
        List.sort (fun (_, c1) (_, c2) -> compare c2 c1) freqs

    let score forest example =
        let votes = List.map (Tree.classify example) forest.trees in
        let votes_weights = List.combine votes forest.perf in
        Utils.sum_scores votes_weights

    let classify forest example =
        let scores = score forest example in
        let scores = List.sort (fun (_, c1) (_, c2) -> compare c2 c1) scores in
        match scores with
        | (e, _) :: _ -> e
        | [] -> failwith "empty list of voting scores"

    let stats forest =
        let forest = forest.trees in
        let l = List.length forest in
        let ds_sum = List.fold_left (fun s t -> s + Tree.depth t) 0 forest in
        let ds_avg = (float_of_int ds_sum) /. (float_of_int l) in
        let ns_sum = List.fold_left (fun s t -> s + Tree.max_node t) 0 forest in
        let ns_avg = (float_of_int ns_sum) /. (float_of_int l) in
        let () = Printf.printf "\nNumber of trees: %n\n" l in
        let () = Printf.printf "Avg depth of trees: %f\n" ds_avg in
        let () = Printf.printf "Avg largest node of trees: %f\n" ns_avg in ()

end
