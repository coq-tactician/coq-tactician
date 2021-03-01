let gini_impur x =
    let len = Float.of_int (List.length x) in
    let tbl = Hashtbl.create 10 in (* about 10 classes assumed *)
    let update cl =
        if Hashtbl.mem tbl cl then
            Hashtbl.replace tbl cl ((Hashtbl.find tbl cl) + 1)
        else
            Hashtbl.add tbl cl 1
    in
    List.iter update x;
    1. -. Hashtbl.fold (fun _ x s -> s +. (Float.of_int x /. len) ** 2.) tbl 0.;;

(* compute impurity given an impurity function, *sorted* pairs (value, label)
 * and a threshold *)
(* TODO assert sorted *)
(*
let split_impur impur x_labels thr =
    let append (left, right) (x, l) =
        if x < thr then (l :: left, right) else (left, l :: right) in
    let left, right = List.fold_left append ([], []) x_labels in
    ((impur left) +. (impur right)) /. 2.

let best_split impur x labels =
    let x_l = List.combine x labels in
    let x_l = List.sort (fun a b -> compare (fst a) (fst b)) x_l in
    let rec loop remaining_x_l best_thr best_impur =
        match remaining_x_l with
        | [] | [_]  -> best_thr, best_impur
        | (x1, l1) :: (x2, l2) :: t ->
            let new_thr = (x1 +. x2) /. 2. in
            let new_impur = split_impur impur x_l new_thr in
            if new_impur < best_impur then
                loop ((x2, l2) :: t) new_thr new_impur
            else
                loop ((x2, l2) :: t) best_thr best_impur
    in loop x_l 0. 1.
*)
