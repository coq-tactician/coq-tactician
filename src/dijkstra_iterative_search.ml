open Tactician_util
open Search_strategy
open Proofview
open Notations
open Diagonal_iterative_search

exception DepthEnd of float

let tclFoldPredictions max_reached tacs cont max_dfs =
  let rec aux tacs depth =
      let open Proofview in
      match IStream.peek tacs with
      | IStream.Nil -> tclZERO (
          match depth with
          | None -> PredictionsEnd
          | Some depth -> DepthEnd depth)
      | IStream.Cons ({ focus=_; tactic; confidence }, tacs) ->
        (* TODO: At some point we should start using the focus *)
        let max_dfs = max_dfs +. confidence in
        if max_dfs <= 0. then tclZERO (DepthEnd max_dfs) else
        let tac = tactic >>= fun _ -> cont max_dfs in
        tclOR tac
          (fun e ->
             if max_reached () then tclZERO PredictionsEnd else
               let depth = Option.append depth (match e with
                   | (DepthEnd depth', _) -> Some depth'
                   | _ -> None) in
               aux tacs depth) in
  aux tacs None

(* TODO: max_reached is a hack, remove *)
let tclSearchDijkstraDFS max_reached predict max_dfs =
  let rec aux (max_dfs : float) : float tactic =
    if max_reached () then tclZERO PredictionsEnd else
      Goal.goals >>= function
      | [] -> tclUNIT max_dfs
      | _ ->
        let independent =
          (predict >>= fun predictions ->
           tclFoldPredictions max_reached predictions aux max_dfs
          ) in
        tclFOCUS 1 1 @@ tclUntilIndependent independent >>= aux in
  let rec cont max_dfs =
    aux max_dfs >>= fun max_dfs -> tclUNIT (Cont (cont max_dfs)) in
  cont max_dfs

let tclSearchDijkstraIterative d max_reached predict : cont_tactic =
  let rec aux d =
    (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_float d)))) <*> *)
    if max_reached () then Tacticals.New.tclZEROMSG (Pp.str "No more executions") else
      tclOR
        (tclSearchDijkstraDFS max_reached predict d)
        (function
          | (PredictionsEnd, _) ->
            Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
          | (DepthEnd delta, _) ->
            let d = d -. delta +. 1. in
            (* Feedback.msg_notice Pp.(str "----------- new iteration : " ++ real d ++ str " previous reached " ++ real delta); *)
            aux d
          | (e, info) -> tclZERO ~info e )
  in Cont (aux d)

(* let () = register_search_strategy "dijkstra iterative search" (tclSearchDijkstraIterative 0.) *)
