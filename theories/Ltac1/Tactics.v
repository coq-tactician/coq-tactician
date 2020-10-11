From Tactician Require Export Ltac1Dummy.

Declare ML Module "ltac_plugin".
Declare ML Module "ssrmatching_plugin".
Declare ML Module "ssreflect_plugin".
Declare ML Module "tactician_ltac1_record_plugin".
Declare ML Module "tactician_ltac1_tactics_plugin".

Ltac searcher ::= idtac
    "A previously synthesized proof script by Tactician has failed."
    "An attempt is being made to synthesize a new script.";
    ml_search.
Ltac search ::= ml_search.
