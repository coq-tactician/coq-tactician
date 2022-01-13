From Tactician Require Import Ltac1.
From Tactician Require Export Ltac1Dummy.

Goal True. tactician ignore auto. Qed.
Goal True. Fail synth. auto. Qed.
Goal True. synth. Qed.
