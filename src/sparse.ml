module ISet = Set.Make(Int)

type indices = int list
type example_features = ISet.t
type features = example_features array
type 'a example = {features : example_features; label : 'a option}
type 'a examples = {
    indices : indices;
    features : features;
    labels : 'a array option}

let labels {indices; features; labels} =
    match labels with
    | None -> failwith "unlabeled examples"
    | Some labels -> List.map (fun i -> labels.(i)) indices

let is_empty {indices; features; _} =
    indices = []

let all_features {indices; features; _} =
    let all = List.fold_left
        (fun s n -> ISet.union s features.(n)) ISet.empty indices in
    ISet.elements all

let n_features examples =
    List.length (all_features examples)

let random_feature {indices; features; _} =
    let random_example_1 = features.(Utils.choose_random indices) in
    let random_example_2 = features.(Utils.choose_random indices) in
    let ex_1_minus_ex_2 = ISet.diff random_example_1 random_example_2 in
    if ISet.is_empty ex_1_minus_ex_2 then
        Utils.choose_random (ISet.elements random_example_1)
    else
        Utils.choose_random (ISet.elements ex_1_minus_ex_2)

let random_features examples n =
    let rec loop acc = function
        | 0 -> acc
        | n -> loop ((random_feature examples) :: acc) (n - 1) in
    loop [] n

let random_rule examples =
    fun {features; label} -> ISet.mem (random_feature examples) features

let split_impur impur rule {indices; features; labels} =
    let labels =
        match labels with
        | None -> failwith "labels required"
        | Some labels -> labels in
    let append (left, right) i =
        if rule features.(i) then (labels.(i) :: left, right)
        else (left, labels.(i) :: right) in
    let left, right = List.fold_left append ([], []) indices in
    ((impur left) +. (impur right)) /. 2.

exception Empty_list

(* m -- numbers of features to choose from *)
let gini_rule ?m:(m=0) examples =
    let {indices; features; _} = examples in
    let n = List.length indices in
    let m = match m with
    | 0 -> n |> float_of_int |> sqrt |> int_of_float
    | m -> m in
    let random_feas = random_features examples m in
    let rec loop features impurs =
        match features with
        | [] -> List.rev impurs
        | h :: t ->
            let rule = fun e -> ISet.mem h e in
            let impur = split_impur Impurity.gini_impur rule examples in
            loop t (impur :: impurs) in
    let impurs = loop random_feas [] in
    let feas_impurs = List.combine random_feas impurs in
    let im (_, i) = i in
    let feas_impurs_sorted =
        List.sort (fun a b -> compare (im a) (im b)) feas_impurs in
    let best_fea =
        match feas_impurs_sorted with
        | [] -> raise Empty_list
        | (f, _) :: _ -> f in
    fun {features; label} -> ISet.mem best_fea features
