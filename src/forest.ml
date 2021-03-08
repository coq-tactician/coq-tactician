module Make = functor (Data : Tree.DATA) -> struct
    module Tree = Tree.Make(Data)

    let forest tree n examples =
        let initseg = Parmap.L (List.init n (fun i -> i)) in
        Parmap.parmap (fun _ -> tree (Data.random_subset examples)) initseg

(*
    let forest tree n examples =
        let initseg = List.init n (fun i -> i) in
        List.map (fun _ -> tree (Data.random_subset examples)) initseg
*)

    let vote votes =
        let tbl = Hashtbl.create 10 in (* about 10 classes assumed *)
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

    let classify forest examples =
(*      let votes = List.map (Tree.classify examples) forest in *)
        let votes = Parmap.parmap (Tree.classify examples) (Parmap.L forest) in
        let inds = Data.indices examples in
        List.map (fun i -> vote (List.map (fun x -> List.nth x i) votes)) inds
end
