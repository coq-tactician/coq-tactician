From Tactician Require Export Ltac1.Record.

Declare ML Module "tactician_ltac1_tactics_plugin".

(* These notations are on a higher level so that we can override the dummy module.
   Note that tactic redefinition does not work, because the dummy module might be loaded
   again after this module. *)
Tactic Notation (at level 5) "search" "with" "cache" tactic3(t) := solve [t] || (idtac
    "A previously synthesized proof script by Tactician has failed."
    "An attempt is being made to synthesize a new script.";
    ml_search).

Tactic Notation (at level 5) "search" := ml_search.

Tactic Notation (at level 5) "tactician" "ignore" tactic3(t) := ml_tactician_ignore t.
