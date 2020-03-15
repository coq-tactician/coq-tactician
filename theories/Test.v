Require Import Loader.

Lemma t : True.
auto.
Qed.

Set Tactician Benchmark 10.

Lemma k : True.
apply I.
Qed.

Lemma u : True.
suggest.
search.
Qed.

Module K.

Lemma v : True.
auto.
Qed.

End K.

Set Default Proof Mode "Classic".

Lemma r : True.
reflexivity.
Qed.

Lemma p : True.
suggest.
search.
Qed.