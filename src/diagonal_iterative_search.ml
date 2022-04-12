open Tactician_util
open Search_strategy
open Proofview
open Notations

let tclFoldPredictions max_reached tacs =
  let rec aux tacs depth =
      let open Proofview in
      match IStream.peek tacs with
      | IStream.Nil -> tclZERO (if depth then DepthEnd else PredictionsEnd)
      | IStream.Cons (tac, tacs) ->
        tclOR tac
          (fun e ->
             if max_reached () then tclZERO PredictionsEnd else
               let depth = depth || (match e with
                   | (DepthEnd, _) -> true
                   | _ -> false) in
               aux tacs depth) in
  aux tacs false

(* TODO: max_reached is a hack, remove *)
let tclSearchDiagonalDFS max_reached predict max_dfs =
  let rec aux (max_dfs : int) : int tactic =
    if max_reached () then tclZERO PredictionsEnd else
      Goal.goals >>= function
      | [] -> tclUNIT max_dfs
      | _ ->
        let independent =
          tclFOCUS 1 1
            (predict >>= fun predictions ->
             tclFoldPredictions max_reached
               (mapi
                  (fun i {focus=_; tactic; confidence} -> (* TODO: At some point we should start using the focus *)
                     let n_max_dfs = Stdlib.Int.shift_right max_dfs i in
                     if n_max_dfs <= 0 then tclZERO DepthEnd else
                     if confidence = Float.neg_infinity then tclZERO PredictionsEnd else (* TODO: Hack *)
                       (tactic >>= fun _ -> aux (n_max_dfs - 1)))
                  predictions) >>= aux) in
        tclONCE independent >>= aux in
  aux max_dfs >>= fun _ -> tclUNIT ()

let rec tclSearchDiagonalIterative d max_reached predict : unit tactic =
  (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
  if max_reached () then Tacticals.tclZEROMSG (Pp.str "No more executions") else
  tclOR
    (tclSearchDiagonalDFS max_reached predict d)
    (function
      | (PredictionsEnd, _) ->
        Tacticals.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
      | _ ->
        (* Feedback.msg_notice Pp.(str "----------- new iteration : " ++ int ( d * 2)); *)
        tclSearchDiagonalIterative (d * 2) max_reached predict)

let () = register_search_strategy "diagonal iterative search" (tclSearchDiagonalIterative 8)
