module ISet = Set.Make(Int)


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

let shuffle l =
    let l = List.map (fun c -> (Random.bits (), c)) l in
    let sl = List.sort compare l in
    List.map snd sl

let rec init_seg l n =
    match l with
    | [] -> failwith "init_seg"
    | h :: t -> if n = 1 then [h] else h :: init_seg t (n-1)

let init_seg_and_tail l n =
    let rec aux acc n = function
        | [] -> (List.rev acc, [])
        | h :: t ->
            if n = 0 then (List.rev acc, h :: t) else aux (h :: acc) (n-1) t
    in aux [] n l

let random_split l n =
    let sl = shuffle l in
    init_seg_and_tail sl n

let choose_randoms l n =
    init_seg (shuffle l) n

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
    List.map (fun l -> List.map int_of_string (split l)) lines

let load_labels file =
    List.map int_of_string (read_lines file)

let print_label label =
    Printf.printf "%n\n" label

let rec remove_last l =
    match l with
    | [] -> []
    | [h] -> []
    | h :: t -> h :: (remove_last t)

let freqs l =
    let sorted = List.sort compare l in
    let rec loop occ sorted =
        match sorted, occ with
        | [], _ -> occ
        | h :: t, [] -> loop [(h, 1)] t
        | h :: t, (e, c) :: t2 ->
            if h = e then loop ((e, c + 1) :: t2) t
            else loop ((h, 1) :: (e, c) :: t2) t in
    let occurs = loop [] sorted in
    let len = float_of_int (List.length l) in
    List.map (fun (e, c) -> (e, (float_of_int c) /. len)) occurs

let uniq l =
    let rec aux u l =
        match l with
        | [] -> u
        | h :: t -> if List.mem h u then aux u t else aux (h :: u) t
    in aux [] l

let rec min_list = function
    | [] -> invalid_arg "empty list"
    | h :: t -> List.fold_left min h t

let rec max_list = function
    | [] -> invalid_arg "empty list"
    | h :: t -> List.fold_left max h t
