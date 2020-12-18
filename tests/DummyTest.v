From Tactician Require Export Ltac1Dummy.

Goal True. tactician ignore auto. Qed.
Goal True. auto. Qed.
Goal True.
Fail search.
search with cache auto.
Qed.

From Tactician Require Import Ltac1.

Goal True. search with cache auto. Qed.
Goal True. search. Qed.
