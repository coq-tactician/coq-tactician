open Tactician_util
open Search_strategy
open Proofview
open Notations

exception DepthEnd of float

let tclFoldPredictions max_reached tacs =
  let rec aux tacs depth =
      let open Proofview in
      match IStream.peek tacs with
      | IStream.Nil -> tclZERO (
          match depth with
          | None -> PredictionsEnd
          | Some depth -> DepthEnd depth)
      | IStream.Cons (tac, tacs) ->
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
          tclFOCUS 1 1
            (predict >>= fun predictions ->
             tclFoldPredictions max_reached
               (mapi
                  (fun _i {focus=_; tactic; confidence} -> (* TODO: At some point we should start using the focus *)
                     if confidence <= 0. then tclZERO PredictionsEnd else
                       let lconfidence = Float.log confidence /. Float.log 2. in
                       let max_dfs = max_dfs +. lconfidence in
                       if max_dfs <= 0. then tclZERO (DepthEnd max_dfs) else
                         (tactic >>= fun _ -> aux max_dfs))
                  predictions) >>= aux) in
        tclONCE independent >>= aux in
  aux max_dfs >>= fun _ -> tclUNIT ()

let rec tclSearchDijkstraIterative d max_reached predict : unit tactic =
  (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_float d)))) <*> *)
  if max_reached () then Tacticals.tclZEROMSG (Pp.str "No more executions") else
  tclOR
    (tclSearchDijkstraDFS max_reached predict d)
    (function
      | (PredictionsEnd, _) ->
        Tacticals.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
      | (DepthEnd delta, _) ->
        let d = d -. delta +. 1. in
        (* Feedback.msg_notice Pp.(str "----------- new iteration : " ++ real d ++ str " previous reached " ++ real delta); *)
        tclSearchDijkstraIterative d max_reached predict
      | (e, info) -> tclZERO ~info e )

(* let () = register_search_strategy "dijkstra iterative search" (tclSearchDijkstraIterative 0.) *)
