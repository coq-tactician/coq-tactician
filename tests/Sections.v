From Tactician Require Import Ltac1.
Section test.
Tactic Notation "ptrue" := exact I.
Ltac prefl := reflexivity.
Goal True. ptrue. Qed.
Goal True. Suggest. synth. Qed.
Goal 1 = 1. prefl. Qed.
Goal 1 = 1. Suggest. synth. Qed.
End test.
Goal True. Suggest. synth. Qed.
Goal 1 = 1. Suggest. synth. Qed.
