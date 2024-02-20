open Tactic_learner
open Ltac_plugin

module SubstitutionChecker = functor (TS : TacticianStructures) -> struct
  open TS

  type model = unit

  let empty () = ()

  let add () b tac = ()

  let learn () _status outcomes tac =
    let orig = tac in
    let strict = Tactic_normalize.tactic_strict (Global.env ()) @@
      Tactic_normalize.tactic_normalize @@ tactic_repr tac in
    let (args, exact), interm = Tactic_one_variable.tactic_one_variable (Global.env ()) strict in
    let stripped = Tactic_one_variable.tactic_strip strict in
    let reconstructed = Tactic_one_variable.tactic_substitute args stripped in
    match reconstructed with
    | None ->
      let stricth = tactic_hash @@ tactic_make strict in
      let intermh = tactic_hash @@ tactic_make interm in
      let strippedh = tactic_hash @@ tactic_make stripped in
      let expr = Pp.(
          str "--------------------------" ++ fnl () ++
          str "Tactic reconstruction failure" ++ fnl () ++
          str "original: " ++ (int (tactic_hash orig)) ++ ws 1 ++
          Pptactic.pr_glob_tactic (Global.env ()) (tactic_repr orig) ++ fnl () ++
          str "strict  : " ++ (int stricth) ++ ws 1 ++
          Pptactic.pr_glob_tactic (Global.env ()) strict ++ ws 1 ++
          str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr strict)) ++ fnl () ++
          str "intermed: " ++ (int intermh) ++ ws 1 ++
          (if exact then str "(exact)" else str "(not exact)") ++ ws 1 ++
          Pptactic.pr_glob_tactic (Global.env ()) interm ++ ws 1 ++
          str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr interm)) ++ fnl () ++
          str "stripped: " ++ (int strippedh) ++ ws 1 ++
          Pptactic.pr_glob_tactic (Global.env ()) stripped ++ ws 1 ++
          str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr stripped)) ++ fnl ()
        ) in
      CErrors.anomaly expr
    | Some reconstructed ->
      let stricth = tactic_hash @@ tactic_make strict in
      let intermh = tactic_hash @@ tactic_make interm in
      let reconstructedh = tactic_hash @@ tactic_make reconstructed in
      let strippedh = tactic_hash @@ tactic_make stripped in
      let fail, msg =
        if (exact && stricth != intermh) then true, "Tactic exactness report incorrect"
        else if (reconstructedh != intermh) then true, "Tactic reconstruction incorrect"
        else false, "" in
      if fail then
        let expr = Pp.(
            str "--------------------------" ++ fnl () ++
            str msg ++ fnl () ++
            str "original: " ++ (int (tactic_hash orig)) ++ ws 1 ++
            Pptactic.pr_glob_tactic (Global.env ()) (tactic_repr orig) ++ fnl () ++
            str "strict  : " ++ (int stricth) ++ ws 1 ++
            Pptactic.pr_glob_tactic (Global.env ()) strict ++ ws 1 ++
            str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr strict)) ++ fnl () ++
            str "intermed: " ++ (int intermh) ++ ws 1 ++
            (if exact then str "(exact)" else str "(not exact)") ++ ws 1 ++
            Pptactic.pr_glob_tactic (Global.env ()) interm ++ ws 1 ++
            str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr interm)) ++ fnl () ++
            str "reconstr: " ++ (int reconstructedh) ++ ws 1 ++
            Pptactic.pr_glob_tactic (Global.env ()) reconstructed ++ ws 1 ++
            str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr reconstructed)) ++ fnl () ++
            str "stripped: " ++ (int strippedh) ++ ws 1 ++
            Pptactic.pr_glob_tactic (Global.env ()) stripped ++ ws 1 ++
            str (Sexpr.sexpr_to_string (Tactic_sexpr.tactic_sexpr stripped)) ++ fnl ()
          ) in
        CErrors.anomaly expr

  let predict () f = IStream.empty

  let evaluate () _ _ = 1., ()

end

(* let () = register_online_learner "substitution-check" (module SubstitutionChecker) *)
(* let () = Tactic_learner_internal.disable_queue () *)
