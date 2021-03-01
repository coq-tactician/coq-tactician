module Make = functor (Data : Tree_online.DATA) -> struct
    module Tree = Tree_online.Make(Data)

    let empty () = []

    let add forest example =
        let new_tree = Tree.leaf example in
        let updated_trees =
            List.map (fun tree -> Tree.add tree example) forest
        in
        new_tree :: updated_trees

    let forest examples =
        let forest = empty () in
        Data.fold_left add forest examples

    let vote votes =
        let tbl = Hashtbl.create 100 in
        let update cl =
            if Hashtbl.mem tbl cl then
                Hashtbl.replace tbl cl ((Hashtbl.find tbl cl) + 1)
            else
                Hashtbl.add tbl cl 1
        in
        List.iter update votes;
        let update_max_cl cl v (max_cls, max_v) =
            match compare v max_v with
            | 1  -> ([cl], v)
            | 0  -> (cl :: max_cls, v)
            | -1 -> (max_cls, max_v)
            | _  -> failwith "Illegal value of compare." in
        let max_freq_cls = Hashtbl.fold update_max_cl tbl ([], 1) in
        match max_freq_cls with
        | ([], _) -> failwith "At least one class needs to have maximal frequency."
        | ([x], _) -> x
        | (l, _) -> Utils.choose_random l

    let freqs votes =
        let tbl = Hashtbl.create 10 in
        let update cl =
            if Hashtbl.mem tbl cl then
                Hashtbl.replace tbl cl ((Hashtbl.find tbl cl) + 1)
            else
                Hashtbl.add tbl cl 1
        in
        List.iter update votes;
        let sum = Hashtbl.fold (fun c n s -> n + s) tbl 0 in
        let sum = float_of_int sum in
        let keys = List.of_seq (Hashtbl.to_seq_keys tbl) in
        List.map
            (fun cl -> ((float_of_int (Hashtbl.find tbl cl)) /. sum, cl)) keys

    let classify forest examples =
        let votes = List.map (Tree.classify examples) forest in
        let inds = Data.indices examples in
        List.map (fun i -> vote (List.map (fun x -> List.nth x i) votes)) inds

    let classify_1 forest example =
        let example = Data.examples_of_1 example in
        let votes = List.map (Tree.classify example) forest in
        let votes = List.map List.hd votes in
        freqs votes

end
