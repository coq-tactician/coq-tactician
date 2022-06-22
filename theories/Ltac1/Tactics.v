From Tactician Require Export Ltac1.Record.

Declare ML Module "tactician_ltac1_tactics_plugin:coq-tactician.tactics-plugin".

Tactic Notation (at level 5) "search" "with" "cache" tactic3(t) := fail
  "'search with cache' has been renamed to 'synth with cache'".

Tactic Notation (at level 5) "search" := fail
  "'search' has been renamed to 'synth'".

(* These notations are on a higher level so that we can override the dummy module.
   Note that tactic redefinition does not work, because the dummy module might be loaded
   again after this module. *)
Tactic Notation (at level 5) "synth" "with" "cache" tactic3(t) := solve [t] || (idtac
    "A previously synthesized proof script by Tactician has failed."
    "An attempt is being made to synthesize a new script.";
    ml_synth).

Tactic Notation (at level 5) "synth" := ml_synth.

Tactic Notation (at level 5) "debug" "synth" := ml_debug_synth.

Tactic Notation (at level 5) "tactician" "ignore" tactic3(t) := ml_tactician_ignore t.
