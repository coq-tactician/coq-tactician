From Tactician Require Export Ltac1Dummy.

Goal True. tactician ignore auto. Qed.
Goal True. auto. Qed.
Goal True.
Fail synth.
synth with cache auto.
Qed.

From Tactician Require Import Ltac1.

Goal True. synth with cache auto. Qed.
Goal True. synth. Qed.
