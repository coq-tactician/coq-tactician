open Printf
open Hashtbl

module ISet = Set.Make(Int)

type features = ISet.t
type indices = int list
type 'a example = (features * ('a option))
type 'a examples = {
    indices : int list;
    universe : (int, 'a example) Hashtbl.t}
type rule = features -> bool
type 'a split_rule = 'a examples -> 'a examples * 'a examples

let label (features, label) =
    match label with
    | None -> failwith "unlabeled example"
    | Some l -> l

let labels {indices; universe} =
    List.map (fun i -> label (find universe i)) indices

let features (features, label) =
    features

let length {indices; universe} =
    List.length indices

let all_features {indices; universe} =
    let all = List.fold_left
        (fun s i -> ISet.union s (features (find universe i)))
        ISet.empty indices in
    ISet.elements all

let n_features examples =
    List.length (all_features examples)

(*
let print_example {_; universe} i =
    ISet.iter (fun f -> printf "%n %!" f) features.(n);
    match labels with
        | None -> ()
        | Some labels -> printf "# %n\n%!" labels.(n)
*)

(*
let random_feature {indices; features; _} =
    let random_example = features.(Utils.choose_random indices) in
    Utils.choose_random (ISet.elements random_example)
*)

let random_feature {indices; universe} =
    let random_example_1 =
        features (find universe (Utils.choose_random indices)) in
    let random_example_2 =
        features (find universe (Utils.choose_random indices)) in
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
    ISet.mem (random_feature examples)

let split_impur impur rule {indices; universe} =
    let append (left, right) i =
        if rule (features (find universe i)) then
            (label (find universe i) :: left, right)
        else (left, label (find universe i) :: right) in
    let left, right = List.fold_left append ([], []) indices in
    ((impur left) +. (impur right)) /. 2.

exception Empty_list

(* m -- numbers of features to choose from *)
let gini_rule ?m:(m=0) examples =
    let n = length examples in
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
    fun example -> ISet.mem best_fea example

let print_label l = l |> printf "%n\n"
