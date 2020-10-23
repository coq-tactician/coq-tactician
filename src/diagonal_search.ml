open Tactician_util

let rec tclFairJoin (tacs : 'a Proofview.tactic Proofview.tactic) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1, resttacs) ->
      tclCASE tac1 >>= function
      | Fail e -> (tclFairJoin (resttacs e))
      | Next (a, tac1') ->
        tclOR (tclUNIT a)
              (fun e -> (tclFairJoin (tclOR (resttacs e)
                                            (fun e -> tclUNIT (tac1' e)))))

let tclInterleave tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclFairJoin ((tclUNIT tac1) <+> (tclUNIT tac2))

let tclInterleaveList (tacs : 'a Proofview.tactic list) : 'a Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFairJoin
      (List.fold_right (fun tac acc -> (tclUNIT tac) <+> acc) tacs (tclZERO PredictionsEnd))

let rec tclInterleaveCaseTacsSpecial start (tacs : bool Proofview.case Proofview.tactic) =
    let open Proofview in
    let open Notations in
    tclCASE tacs >>= function
    | Fail (iexn, info) -> tclZERO ~info:info iexn
    | Next (tac1case, resttacs) ->
      match tac1case with
      | Fail e -> (tclInterleaveCaseTacsSpecial start (resttacs e))
      | Next (b, tac1') ->
        if (start && b) then Tacticals.New.tclZEROMSG (Pp.str "Ran out of tactics") else
        tclOR (if b then tclUNIT () else Tacticals.New.tclCOMPLETE (tclUNIT ()))
              (fun e -> (tclInterleaveCaseTacsSpecial b (tclOR (resttacs e)
                                                               (fun e -> (tclCASE (tac1' e))))))

let rec tclInfiniteTrue () =
    let open Proofview in
    tclOR (tclUNIT true) (fun _ -> tclInfiniteTrue ())

let tclInterleaveListSpecial (tacs : unit Proofview.tactic list) : unit Proofview.tactic =
    let open Proofview in
    let open Notations in
    let tacs = List.map (fun t -> t <*> tclUNIT false) tacs in
    tclInterleaveCaseTacsSpecial true
      (List.fold_right (fun tac acc -> (tclCASE tac) <+> acc) tacs (tclCASE (tclInfiniteTrue ())))

let tclInterleaveSpecial tac1 tac2 =
    tclInterleaveListSpecial [tac1; tac2]

let rec tclInterleaveWrong tac1 tac2 =
    let open Proofview in
    let open Notations in
    tclCASE tac1 >>= function
    | Fail iexn -> tac2
    | Next ((), tac1') -> tclOR (tclUNIT ()) (fun e -> (tclInterleaveWrong tac2 (tac1' e)))

type blaat = | Intermediate | Complete | No_goal

(* TODO: This does not use the focus, and is generally entirely wrong. Probably delete or rewrite *)
let rec tclFold tac : blaat Proofview.tactic =
    let open Proofview in
    let open Notations in
    tclFOCUS ~nosuchgoal:(tclUNIT No_goal) 1 1 tac >>=
    (function
     | No_goal -> tclUNIT Complete
     | Complete -> tclFold tac
     | Intermediate -> tclUNIT Intermediate)

let rec tclSearchBFS () mark : blaat Proofview.tactic =
  let open Proofview in
  let open Notations in
  tclENV >>= fun env -> Goal.goals >>= record_map (fun x -> x) >>= function
  | [] -> tclUNIT No_goal
  | gls -> let predictions = predict gls in
    (tclSearchGoalBFS predictions mark)
and tclSearchGoalBFS ps mark =
    let open Proofview in
    let open Notations in
      tclUNIT Intermediate <+> tclInterleaveList
        (List.mapi (fun i {focus; tactic=(tac, _)} ->
          let tac2 = parse_tac tac in
          tclFold (
           (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
           (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int i)))) <*>
           (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pp.str "")))) <*>
           print_goal_short <*>
           tclPROGRESS tac2 <*>
           (*print_goal_short <*>*)
           tclSearchBFS () (mark ^ "." ^ string_of_int i))
       ) (Stream.npeek 100 ps))

(* TODO: Doesn't compile anymore and is probably wrong
let rec tclSearch () mark curr : blaat Proofview.tactic =
    let open Proofview in
    tclFold (Goal.enter_one (fun gl ->
        let predictions = List.map fst (predict gl) in
        (tclSearchGoal predictions mark curr)))
and tclSearchGoal ps mark curr =
    let open Proofview in
    let open Notations in
    match ps with
    | [] -> Tacticals.New.tclZEROMSG (Pp.str "No more predicted tactics")
    | tac::ps' ->
      let tac2 = parse_tac tac in
      tclUNIT Intermediate <+> tclInterleave
        (tclSearchGoal ps' mark (curr + 1))
        (
         (tclLIFT (NonLogical.print_info (Pp.str "------------------------------"))) <*>
         (tclLIFT (NonLogical.print_info (Pp.str (mark ^ "." ^ string_of_int curr)))) <*>
         (tclLIFT (NonLogical.print_info (Pp.app (Pp.str "Exec: ") (Pptactic.pr_raw_tactic Environ.empty_env Evd.empty tac)))) <*>
         print_goal_short <*>
         tclPROGRESS tac2 <*>
         print_goal_short <*>
         tclSearch () (mark ^ "." ^ string_of_int curr) 0)
*)

let rec tclInfiniteUnit () =
  let open Proofview in
  tclOR (tclUNIT ()) (fun _ -> tclInfiniteUnit ())
