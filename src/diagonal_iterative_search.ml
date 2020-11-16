open Tactician_util
open Search_strategy
open Proofview
open Notations

let tclFoldPredictions max_reached tacs =
  let rec aux depth i =
      let open Proofview in
      match Stream.peek tacs with
      | None -> tclZERO (if depth then DepthEnd else PredictionsEnd)
      | Some tac -> Stream.junk tacs;
        tclOR tac
          (fun e ->
             if max_reached () then tclZERO PredictionsEnd else
               let depth = depth || (match e with
                   | (DepthEnd, _) -> true
                   | _ -> false) in
               aux depth (i+1)) in
  aux false 0

(* TODO: max_reached is a hack, remove *)
let tclSearchDiagonalDFS max_reached predict depth =
  let rec aux (depth : int) : int tactic =
    if max_reached () then tclZERO PredictionsEnd else
      Goal.goals >>= function
      | [] -> tclUNIT depth
      | _ ->
        predict >>= fun predictions ->
        tclFoldPredictions max_reached
          (stream_mapi
             (fun i {focus; tactic; _} ->
                let ndepth = depth - i in
                if ndepth <= 0 then tclZERO DepthEnd else
                  (tactic >>= fun _ -> aux (ndepth - 1)))
             predictions) >>= aux in
  aux depth >>= fun _ -> tclUNIT ()

let rec tclSearchDiagonalIterative d max_reached predict : unit tactic =
  (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
  if max_reached () then Tacticals.New.tclZEROMSG (Pp.str "No more executions") else
  tclOR
    (tclSearchDiagonalDFS max_reached predict d)
    (function
      | (PredictionsEnd, _) ->
        Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
      | _ -> tclSearchDiagonalIterative (d + 1) max_reached predict)

let () = register_search_strategy "diagonal iterative search" (tclSearchDiagonalIterative 10)
