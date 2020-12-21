From Tactician Require Import Ltac1.
Section test.
Tactic Notation "ptrue" := exact I.
Ltac prefl := reflexivity.
Goal True. ptrue. Qed.
Goal True. Suggest. search. Qed.
Goal 1 = 1. prefl. Qed.
Goal 1 = 1. Suggest. search. Qed.
End test.
Goal True. Suggest. search. Qed.
Goal 1 = 1. Suggest. search. Qed.