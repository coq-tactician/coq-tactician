Declare ML Module "ltac_plugin".
Declare ML Module "tactician_ltac1_record_plugin".
Declare ML Module "tactician_ltac1_tactics_plugin".

From Ltac2 Require Import Control Notations.
From Tactician Require Import Ltac1Dummy.

Ltac searcher := idtac
    "A previously synthesized proof script by Tactician has failed."
    "An attempt is being made to synthesize a new script.";
    ml_search.

(* A hack to work around https://github.com/coq/coq/issues/11866 *)
Ltac2 Notation "-" tacs(list0(thunk(self), "-")) "--|" := prove_with tacs.

Tactic Notation (at level 5) "search" "failing" tactic(t) := t searcher.

Tactic Notation (at level 5) "search" := ml_search.

Tactic Notation (at level 5) "suggest" := ml_suggest.
