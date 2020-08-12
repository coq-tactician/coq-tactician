open Tactic_learner
open Learner_helper

module NullLearner : TacticianLearnerType = struct
  type t = unit
  let create () = ()
  let add db execs tac = ()
  let predict db states = []
end

module PrintLearner : TacticianLearnerType = struct
  type t = unit
  let create () = ()
  let add db execs tac =
    let print_tac t = sentence_to_sexpr (tactic_sentence t) in
    print_endline "Tactic:";
    print_endline (print_tac tac);
    List.iteri (fun i (mem, before, after) ->
        print_endline "";
        print_endline ("Executed on proof state " ^ string_of_int i ^ ":");
        print_endline "Tactic trace:";
        print_endline (String.concat " - " (List.map print_tac mem));
        print_endline "Proof state:";
        print_endline (proof_state_to_sexpr before);
        print_endline ("Generated " ^ string_of_int (List.length after) ^ " states:");
        List.iteri (fun j pf ->
            print_endline (string_of_int j ^ ": " ^ proof_state_to_sexpr pf)
          ) after;
      ) execs;
    print_endline "\n";
    ()
  let predict db states = []
end

module ReverseAddedOrder : TacticianLearnerType = struct
  type t = tactic list
  let create () = []
  let add db execs tac = tac::db
  let predict db states = List.map (fun tac -> (1., focus_first states, tac)) db
end

module AddedOrder : TacticianLearnerType = struct
  type t = tactic list
  let create () = []
  let add db execs tac = tac::db
  let predict db states = List.map (fun tac -> (1., focus_first states, tac)) (List.rev db)
end

module Random : TacticianLearnerType = struct
  type t = tactic list

  let create () = []
  let add db execs tac = tac::db

  let shuffle d =
    let nd = List.map (fun c -> (Random.bits (), c)) d in
    let sond = List.sort compare nd in
    List.map snd sond

  let predict db states =
    List.map (fun tac -> (1., focus_first states, tac)) (shuffle db)
end

(*
let () = Feedback.msg_warning (Pp.str ("You have installed and enabled the coq-tactician-plugin-example " ^
                                       "package.\n This is only meant for demonstration purposes, and does " ^
                                       "not actually provide good predictions."))
let () = register_learner "ReverseAddedOrder" (module PrintLearner)
*)
