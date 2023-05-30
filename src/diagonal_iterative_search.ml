open Tactician_util
open Search_strategy
open Proofview
open Notations

let withIsIndependent t =
  tclEVARMAP >>= fun sigma1 ->
  Goal.enter_one @@ fun gl ->
  let goal = Goal.goal gl in
  with_shelf t >>= fun (shelf, res) ->
  if not @@ CList.is_empty shelf
  then
    shelve_goals shelf <*> tclUNIT (false, res)
  else
    tclEVARMAP >>= fun sigma2 ->
    (* TODO: One might also consider the tactic independent if it completely solves
       another evar and that evar is not a dependency of any other goal *)
    let independent = Evd.fold_undefined (fun e _ d ->
        (Evar.equal goal e || Evd.is_undefined sigma2 e) && d) sigma1 true in
    tclUNIT (independent, res)

let tclUntilIndependent t =
  let rec aux t =
    tclCASE t >>= function
    | Fail (e, info) -> tclZERO ~info e
    | Next ((true, res), _) -> tclUNIT res
    | Next ((false, res), cont) -> tclOR (tclUNIT res) (fun e -> aux @@ cont e)
  in
  aux @@ withIsIndependent t

let tclFoldPredictions max_reached tacs cont max_dfs =
  let rec aux i tacs depth =
      let open Proofview in
      match IStream.peek tacs with
      | IStream.Nil -> tclZERO (if depth then DepthEnd else PredictionsEnd)
      | IStream.Cons ({ focus=_; tactic; confidence }, tacs) ->
        (* TODO: At some point we should start using the focus *)
        let n_max_dfs = Stdlib.Int.shift_right max_dfs i in
        if n_max_dfs <= 0 then tclZERO DepthEnd else
        if confidence = Float.neg_infinity then tclZERO PredictionsEnd else (* TODO: Hack *)
        let tac = tactic >>= fun _ -> cont (n_max_dfs - 1) in
        tclOR tac
          (fun e ->
             if max_reached () then tclZERO PredictionsEnd else
               let depth = depth || (match e with
                   | (DepthEnd, _) -> true
                   | _ -> false) in
               aux (i+1) tacs depth) in
  aux 0 tacs false

(* TODO: max_reached is a hack, remove *)
let tclSearchDiagonalDFS max_reached predict max_dfs =
  let rec aux (max_dfs : int) : int tactic =
    if max_reached () then tclZERO PredictionsEnd else
      Goal.goals >>= function
      | [] -> tclUNIT max_dfs
      | _ ->
        let independent =
          predict >>= fun predictions ->
          tclFoldPredictions max_reached predictions aux max_dfs in
        tclFOCUS 1 1 @@ tclUntilIndependent independent >>= aux in
  let rec cont max_dfs =
    aux max_dfs >>= fun max_dfs -> tclUNIT (Cont (cont max_dfs)) in
  cont max_dfs

let tclSearchDiagonalIterative d max_reached predict : cont_tactic =
  let rec aux d =
    (* (tclLIFT (NonLogical.print_info (Pp.str ("Iterative depth: " ^ string_of_int d)))) <*> *)
    if max_reached () then Tacticals.New.tclZEROMSG (Pp.str "No more executions") else
      tclOR
        (tclSearchDiagonalDFS max_reached predict d)
        (function
          | (PredictionsEnd, _) ->
            Tacticals.New.tclZEROMSG (Pp.str "Tactician failed: there are no more tactics left")
          | _ ->
            (* Feedback.msg_notice Pp.(str "----------- new iteration : " ++ int ( d * 2)); *)
            aux (d * 2)) in
  Cont (aux d)

let () = register_search_strategy "diagonal iterative search" (tclSearchDiagonalIterative 8)
