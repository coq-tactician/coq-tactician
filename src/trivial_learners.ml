open Tactic_learner

module NullLearner : TacticianOnlineLearnerType = functor (_ : TacticianStructures) -> struct
  type model = unit
  let empty () = ()
  let learn () _ _ = ()
  let predict () _ = Stream.sempty
let evaluate () _ _ = 0., ()
end

module PrintLearner : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  module LH = Learner_helper.L(TS)
  open TS
  open LH
  type model = unit
  let empty () = ()
  let learn () outcomes tac =
    let tactic_to_string t = sexpr_to_string (tactic_sexpr t) in
    let proof_state_to_string pf = sexpr_to_string (proof_state_to_sexpr pf) in
    print_endline "Tactic:";
    print_endline (tactic_to_string tac);
    List.iteri (fun i outcome ->
        print_endline "";
        print_endline ("Executed on proof state " ^ string_of_int i ^ ":");
        print_endline "Tactic trace:";
        print_endline (String.concat " - " (List.map (fun (_, (ps : proof_step)) ->
            tactic_to_string ps.tactic) outcome.parents));
        print_endline "Proof state:";
        print_endline (proof_state_to_string outcome.before);
        print_endline ("Generated " ^ string_of_int (List.length outcome.after) ^ " states:");
        List.iteri (fun j pf ->
            print_endline (string_of_int j ^ ": " ^ proof_state_to_string pf)
          ) outcome.after;
      ) outcomes;
    print_endline "\n"; ()
  let predict () _ = Stream.sempty
  let evaluate () _ _ = 0., ()
end

module ReverseAddedOrder : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  open TS
  type model = tactic list
  let empty () = []
  let learn db _ tac = tac::db
  let predict db _ = Stream.of_list (List.map (fun tac -> {confidence = 1.; focus = 0; tactic = tac}) db)
  let evaluate db _ _ = 1., db
end

module AddedOrder : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  open TS
  type model = tactic list
  let empty () = []
  let learn db _ tac = tac::db
  let predict db _ = Stream.of_list (List.map (fun tac -> {confidence = 1.; focus = 0; tactic = tac}) (List.rev db))
  let evaluate db _ _ = 1., db
end

module Random : TacticianOnlineLearnerType = functor (TS : TacticianStructures) -> struct
  open TS
  type model = tactic list
  let empty () = []
  let learn db _ tac = tac::db

  let shuffle d =
    let nd = List.map (fun c -> (Random.bits (), c)) d in
    let sond = List.sort compare nd in
    List.map snd sond

  let predict db _ =
    Stream.of_list (List.map (fun tac -> {confidence = 1.; focus = 0; tactic = tac}) (shuffle db))

  let evaluate db _ _ = 1., db
end

(*
let () = Feedback.msg_warning (Pp.str ("You have installed and enabled the coq-tactician-plugin-example " ^
                                       "package.\n This is only meant for demonstration purposes, and does " ^
                                       "not actually provide good predictions.")) *)
(* let () = register_online_learner "ReverseAddedOrder" (module PrintLearner) *)
