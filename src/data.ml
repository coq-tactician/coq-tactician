open Printf
module ISet = Set.Make(Int)

type feature = int
type features = ISet.t
type 'a example = (features * ('a option))
type 'a examples = 'a example list
type direction = Left | Right
type rule = features -> direction

let label (features, label) =
    match label with
    | None -> failwith "unlabeled example"
    | Some l -> l

let labels examples =
    List.map label examples

let unlabeled features =
    (ISet.of_list features, None)

let labeled (features, label) =
    (ISet.of_list features, Some label)

let features (features, label) =
    features

let length = List.length

let random_feature examples =
    let random_example_1 = features (Utils.choose_random examples) in
    let random_example_2 = features (Utils.choose_random examples) in
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
let is_splitting examples f =
    let is_mem e = ISet.mem f (features e) in
    let in_some = List.fold_left (fun b e -> b || is_mem e) false examples in
    let in_all = List.fold_left (fun b e -> b && is_mem e) true examples in
    in_some && (not in_all)

let is_empty examples =
    examples = []

let indices examples =
    List.init (List.length examples) (fun i -> i)

let random_label examples =
    let (f, l) = Utils.choose_random examples in
    match l with
    | None -> failwith "unlabeled example"
    | Some l -> l

let uniform_labels examples =
    let labels = labels examples in
    let rec uniform labels =
        match labels with
        | [] | [_] -> true
        | h1 :: h2 :: t ->
            if h1 = h2 then uniform (h2 :: t) else false in
    uniform labels

let rule_of_fea f =
    fun e -> match ISet.mem f e with true -> Left | false -> Right

let split fea examples =
    let rule = rule_of_fea fea in
    let rec loop examples_l examples_r = function
        | [] -> (examples_l, examples_r)
        | e :: t ->
            match rule (features e) with
            | Left -> loop (e :: examples_l) examples_r t
            | Right -> loop examples_l (e :: examples_r) t in
    loop [] [] examples

let length examples =
    List.length examples

let add examples example =
    example :: examples

let fold_left f s examples =
    List.fold_left f s examples

let random_example examples =
    Utils.choose_random examples

let split_impur impur fea examples =
    let rule = rule_of_fea fea in
    let append (left, right) e =
    match rule (features e) with
    | Left -> (label e :: left, right)
    | Right -> (left, label e :: right) in
    let left, right = List.fold_left append ([], []) examples in
    let el = float_of_int (List.length left) in
    let er = float_of_int (List.length right) in
    let e = float_of_int (List.length examples) in
    let fl = sqrt (el /. e) in
    let fr = sqrt (er /. e) in
    ((impur left) *. fl +. (impur right) *. fr)

(* m -- numbers of features to choose from *)
let gini_rule examples =
    let n = length examples in
    let m =  n |> float_of_int |> sqrt |> int_of_float in
    let random_feas = random_features examples m in
    let impur_from_fea f =
        split_impur Impurity.gini_impur f examples in
    let impurs = List.map impur_from_fea random_feas in
    let impurs_feas = List.combine impurs random_feas in
    let best_impur, best_fea = Utils.min_list impurs_feas in
    best_fea
