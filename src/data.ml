open Printf
module ISet = Set.Make(Int)

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

let all_features examples =
    let all = List.fold_left
        (fun s e -> ISet.union s (features e)) ISet.empty examples in
    ISet.elements all

let n_features examples =
    List.length (all_features examples)

(*
let random_feature {indices; features; _} =
    let random_example = features.(Utils.choose_random indices) in
    Utils.choose_random (ISet.elements random_example)
*)

exception Empty_examples

let random_feature examples =
    let ex1 = Utils.choose_random examples in
    let ex2 =
        let rec loop l =
            match l with
            | [] -> ex1
            | ex :: t -> if (label ex) = (label ex1) then loop t else
                if ISet.equal (features ex) (features ex1)
                then loop t else ex in
        loop examples in
    let feas = if ex1 = ex2 then features ex1 else
        let diff = ISet.diff (features ex1) (features ex2) in
            if ISet.is_empty diff then ISet.diff (features ex2) (features ex1)
            else diff
    in Utils.choose_random (ISet.elements feas) ;;


(*
let random_feature examples =
    let random_example_1 = features (Utils.choose_random examples) in
    let random_example_2 = features (Utils.choose_random examples) in
    let random_example_3 = features (Utils.choose_random examples) in
    let union = ISet.union random_example_1 random_example_2 in
    let diff = ISet.diff union random_example_3 in
    if ISet.is_empty diff then
(*         let () = Printf.printf "%i empty\n" (List.length examples) in *)
        Utils.choose_random (ISet.elements random_example_1)
    else
(*         let () = Printf.printf "good\n" in *)
        Utils.choose_random (ISet.elements diff)
*)

let random_features examples n =
    let rec loop acc = function
        | 0 -> acc
        | n -> loop ((random_feature examples) :: acc) (n - 1) in
    loop [] n

let is_empty examples =
    examples = []

let indices examples =
    List.init (List.length examples) (fun i -> i)

let first_label examples =
    let l = match examples with
    | (f, l) :: _ -> l
    | [] -> failwith "empty examples" in
    match l with
    | None -> failwith "unlabeled example"
    | Some l -> l

let random_label examples =
    let (f, l) = Utils.choose_random examples in
    match l with
    | None -> failwith "unlabeled example"
    | Some l -> l

let random_subset examples =
    Utils.sample_with_replace examples (length examples)

let uniform_labels examples =
    let labels = labels examples in
    let rec uniform labels =
        match labels with
        | [] | [_] -> true
        | h1 :: h2 :: t ->
            if h1 = h2 then uniform (h2 :: t) else false in
    uniform labels

let split rule examples =
    let rec loop examples_l examples_r = function
        | [] -> (examples_l, examples_r)
        | e :: t ->
            match rule (features e) with
            | Left -> loop (e :: examples_l) examples_r t
            | Right -> loop examples_l (e :: examples_r) t in
    loop [] [] examples

let length examples =
    List.length examples

let random_example examples =
    Utils.choose_random examples

let add examples example =
    example :: examples

let fold_left f s examples =
    List.fold_left f s examples

let random_rule examples =
    fun example ->
        match ISet.mem (random_feature examples) example with
        | true -> Left
        | false -> Right

let split_impur impur rule examples =
    let append (left, right) e =
        if rule (features e) then
            (label e :: left, right) else (left, label e :: right) in
    let left, right = List.fold_left append ([], []) examples in
    ((impur left) +. (impur right)) /. 2.

exception Empty_list

(* m -- numbers of features to choose from *)
let gini_rule examples =
    let n = length examples in (* more examples = more features to consider *)
    let m1 = n |> float_of_int |> sqrt |> int_of_float  in
    let m2 = List.length (Utils.uniq (labels examples))
            |> float_of_int |> sqrt |> int_of_float in
    let m = m1 + m2 in
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
    let f_start, i_start =
        match feas_impurs with
        | [] -> raise Empty_list
        | (f, i) :: _ -> (f, i) in
    let best_fea, best_impur = List.fold_left
        (fun (f_b, i_b) (f, i) -> if i_b > i then (f, i) else (f_b, i_b))
        (f_start, i_start) feas_impurs in
    fun example ->
        match ISet.mem best_fea example with
        | true -> Left
        | false -> Right

