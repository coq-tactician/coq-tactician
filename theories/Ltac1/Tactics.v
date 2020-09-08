Declare ML Module "ltac_plugin".
Declare ML Module "tactician_ltac1_record_plugin".
Declare ML Module "tactician_ltac1_tactics_plugin".

Ltac searcher := idtac
    "A previously synthesized proof script by Tactician has failed."
    "An attempt is being made to synthesize a new script.";
    ml_search.
Tactic Notation (at level 5) "search" "failing" tactic(t) := solve [t] || searcher.
Tactic Notation (at level 5) "search" := ml_search.
Tactic Notation (at level 5) "suggest" := ml_suggest.
