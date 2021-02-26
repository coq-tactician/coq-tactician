
module type DATA_CONCRETE = sig
    type example_features
    type label
    type indices = int list
    type features = example_features array
    type labels = label array
    type example = {features : example_features; label : label option}
    type examples = {
        indices : indices;
        features : features;
        labels : labels option}
    type rule = example -> bool
    type split_rule = examples -> examples * examples
    val labels : examples -> label list
    val load_labels : string -> labels
    val load_features : string -> features
    val print_example : examples -> int -> unit
(*     val print_example_2 : example -> unit *)
    val print_label : label -> unit
    val random_rule : examples -> rule
    val gini_rule : ?m:int -> examples -> rule
end;;

module Make = functor (D : DATA_CONCRETE) -> struct
    include D

    let load ?labels features =
        let features = D.load_features features
        and labels = match labels with
        | None -> None
        | Some labels -> Some (D.load_labels labels) in
        let n = Array.length features in
        let indices = List.init n (fun x -> x) in
        {D.indices; D.features; D.labels}

    let indices {D.indices; D.features; _} =
        indices

    let labels {D.indices; D.features; D.labels} =
        match labels with
        | None -> failwith "no labels"
        | Some (l) -> Array.to_list l

    let get examples i =
        let label = match examples.labels with
        | None -> None
        | Some ls -> Some ls.(i) in
        {D.features = examples.features.(i); D.label = label}

    let print examples =
        let inds = indices examples in
        List.iter (D.print_example examples) inds

    let is_empty {D.indices; D.features; D.labels} =
        indices = []

    let first_label {D.indices; D.features; D.labels} =
        match indices, labels with
        | _, None -> failwith "unlabeled examples"
        | [], _ -> failwith "empty examples"
        | h :: t, Some labels -> labels.(h)

    let random_label {D.indices; D.features; D.labels} =
        match labels with
        | None -> failwith "unlabeled examples"
        | Some labels -> let i = Utils.choose_random indices in labels.(i)

    let random_subset {D.indices; D.features; D.labels} =
        let random_indices =
            Utils.sample_with_replace indices (List.length indices) in
        {D.indices=random_indices; D.features; D.labels}

    let uniform_labels {D.indices; D.features; D.labels} =
        match labels with
        | None -> failwith "unlabeled examples"
        | Some labels ->
            let rec uniform inds =
                match inds with
                | [] | [_] -> true
                | h1 :: h2 :: t ->
                    if labels.(h1) = labels.(h2) then uniform (h2 :: t) else false in
            uniform indices

    let split rule examples =
        let {D.indices; D.features; D.labels} = examples in
        let rec loop inds_l inds_r = function
            | [] -> (inds_l, inds_r)
            | h :: t ->
                let example = get examples h in
                match rule example with
                | true -> loop (h :: inds_l) inds_r t
                | false -> loop inds_l (h :: inds_r) t in
        let inds_l, inds_r = loop [] [] indices in
        ({D.indices = inds_l; D.features; D.labels},
         {D.indices = inds_r; D.features; D.labels})

    let examples_of_1 (example : example) =
        let label = match example.label with
        | None -> None
        | Some l -> Some [|l|] in
        {
            D.indices=[0];
            D.features=[|example.features|];
            D.labels=label
        }

    let split_rev (split_rule : split_rule) =
        function example ->
            let example = examples_of_1 example in
            let l, r = split_rule example in
            match is_empty l, is_empty r with
            | false, true -> true
            | true, false -> false
            | _, _ -> failwith "one example goes either left or right"

    let length {D.indices; D.features; D.labels} =
        List.length indices


    let random_example {D.indices; D.features; D.labels} =
        let i = Utils.choose_random indices in
        let f = features.(i) in
        let l = match labels with
            | None -> None
            | Some l -> Some l.(i) in
        {D.features = f; D.label = l}

    let label {D.features; D.label} =
        label

    let unlabel {D.features; D.label} =
        features


    let add examples example =
        let max_i = Utils.max_list examples.indices in
        let new_labels = match examples.labels, example.label with
        | None, _ -> None
        | Some ls, None -> failwith "cannot add unlabeled example"
        | Some ls, Some l -> Some (Array.append [|l|] ls) in
            {
                D.indices = (max_i + 1) :: examples.indices;
                D.features = Array.append [|example.features|] examples.features;
                D.labels = new_labels
            }

    let fold_left f s examples =
        let f' acc i =
            f acc (get examples i)
        in
        List.fold_left f' s examples.indices


end
