open Tactician_util
open Search_strategy
open Proofview
open Notations

let tclFoldPredictions tacs =
  let rec aux depth =
    let open Proofview in
    match Stream.peek tacs with
    | None -> tclZERO (if depth then DepthEnd else PredictionsEnd)
    | Some tac -> Stream.junk tacs;
      tclOR tac
        (fun e ->
           let depth = depth || (match e with
               | (DepthEnd, _) -> true
               | _ -> false) in
           aux depth) in
  aux false

let tclSearchDiagonalDFS predict depth =
  let rec aux (depth : int)
    : int tactic =
    tclENV >>= fun env -> Goal.goals >>= function
    | [] -> tclUNIT depth
    | _ ->
      predict >>= fun predictions ->
      tclFoldPredictions
        (stream_mapi
           (fun i {focus; tactic} ->
              let ndepth = depth - i in
              if ndepth <= 0 then tclZERO DepthEnd else
                (tactic >>= fun _ -> aux (ndepth - 1)))
           predictions) >>= aux in
  aux depth >>= fun _ -> tclUNIT ()

let rec tclSearchDiagonalIterative d predict : unit tactic =
  (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
  tclOR
    (tclSearchDiagonalDFS predict d)
    (function
      | (PredictionsEnd, _) ->
        Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
      | _ -> tclSearchDiagonalIterative (d + 1) predict)

let () = register_search_strategy "diagonal iterative search" (tclSearchDiagonalIterative 1)
