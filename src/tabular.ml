open Printf

type indices = int list
type example_features = float array
type features = example_features array
type label = string
type labels = label array
type examples = {
    indices : indices;
    features : features;
    labels : labels option}
type rule = example_features -> bool
type split_rule = examples -> examples * examples

let load_features file =
    let x = Csv.to_array (Csv.load file) in
    Array.map (fun x -> Array.map float_of_string x) x

let load_labels file =
    Array.of_list (Utils.read_lines file)

let print_example {indices; features; labels} n =
    Array.iter (fun f -> printf "%f " f) features.(n);
    match labels with
        | None -> ()
        | Some labels -> printf "# %s" labels.(n); print_newline ()

let n_features {indices; features; labels} =
    Array.length features.(0)

let col_to_list n {indices; features; labels} =
    List.map (fun i -> features.(i).(n)) indices

let labels {indices; features; labels} =
    match labels with
    | None -> failwith "unlabeled examples"
    | Some labels -> List.map (fun i -> labels.(i)) indices

exception Empty_list

let random_thr x =
    let min = Utils.min_list x in
    let x_no_min = List.filter (fun i -> i > min) x in
    (* check if uniform x *)
    if (List.length x_no_min) = 0 then
        match x with
        | [] -> raise Empty_list
        | h :: _ -> h
    else List.nth x_no_min (Random.int (List.length x_no_min))

let random_rule examples =
    let n = Random.int (n_features examples) in
    let col = col_to_list n examples in
    (fun example -> example.(n) < random_thr col)

let best_gini_thr = Impurity.best_split Impurity.gini_impur

(* m -- numbers of columns to choose from *)
let gini_rule ?m examples =
    let n = n_features examples in
    let m = match m with
    | None -> n |> float_of_int |> sqrt |> int_of_float
    | Some m -> m in
    let random_cols = Utils.sample (List.init n (fun i -> i)) m in
    let labels  = labels examples in
    let rec loop rc thrs_impurs =
        match rc with
        | [] -> List.rev thrs_impurs
        | h :: t ->
            let col = col_to_list h examples in
            let thr_impur = best_gini_thr col labels in
            loop t (thr_impur :: thrs_impurs) in
    let thrs_impurs = loop random_cols [] in
    let cols_impurs = List.combine random_cols thrs_impurs in
    let im (_, (_, i)) = i in
    let cols_impurs_sorted =
        List.sort (fun a b -> compare (im a) (im b)) cols_impurs in
    let best_col, best_thr =
        match cols_impurs_sorted with
        | [] -> raise Empty_list
        | (c, (t, _)) :: _ -> c, t in
    (fun example -> example.(best_col) < best_thr)

let print_label l = l |> printf "%s\n"

