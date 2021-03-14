module IntMap = Map.Make(Int)

let min_list = function
    | [] -> failwith "Empty list"
    | h :: t -> List.fold_left min h t

let max_list = function
    | [] -> failwith "Empty list"
    | h :: t -> List.fold_left max h t

let accuracy l1 l2 =
    assert (List.length l1 = List.length l2);
    let pairs = List.combine l1 l2 in
    let correct = List.filter (fun (x, y) -> x = y) pairs in
    float_of_int (List.length correct) /. float_of_int (List.length pairs)

let array_subset x inds =
    Array.of_list (List.map (fun i -> x.(i)) inds)

let sample_with_replace l n =
    let a = Array.of_list l in
    let rec loop i r =
        match i with
        | 0 -> r
        | i -> loop (i - 1) (a.(Random.int (Array.length a)) :: r)
    in loop n []

let sample l n =
    if List.length l < n then failwith "list shorter than n" else
    let a = Array.of_list l in
    (* i -- number of already chosen elements *)
    let rec loop i = if i = n then () else
        let j = (Random.int (Array.length a - i)) in
        let e = a.(i + j) in
        Array.set a (i + j) a.(i);
        Array.set a i e;
        loop (i + 1) in
    loop 0; Array.sub a 0 n |> Array.to_list

let choose_random l =
    List.nth l (Random.int (List.length l))

let read_lines file : string list =
  let ic = open_in file in
  let try_read () =
    try Some (input_line ic) with End_of_file -> None in
  let rec loop acc = match try_read () with
    | Some s -> loop (s :: acc)
    | None -> close_in ic; List.rev acc in
  loop []

let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time: %f s\n%!" (Sys.time() -. t);
    fx

let load_features file =
    let lines = read_lines file in
    let split = Str.split_delim (Str.regexp " ") in
    let rec loop split_lines = function
        | [] -> List.rev split_lines
        | h :: t ->
            let features_list = List.map int_of_string (split h) in
            features_list :: (loop split_lines t) in
    loop [] lines

let load_labels file =
    List.map int_of_string (read_lines file)

