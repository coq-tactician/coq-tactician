From Tactician Require Import Ltac1.

Goal exists x, True /\ x = 0.
eexists ?[x].
split.
- Fail Third If Not Equal
    (instantiate (x := 0))
    (instantiate (x := 1))
    (gfail).
  Fail third if not equal
    (instantiate (y := 1))
    (instantiate (y := 0))
    (gfail).
  (* Known shortcoming that this does not fail *)
  third if not equal
    (instantiate (x := 1))
    (instantiate (x := 0))
    (gfail).
  auto.
- auto.
Qed.

Goal nat.
Third If Not Equal
  (assert ((forall x:Prop, Prop) -> nat))
  (assert ((forall y:Prop, Prop) -> nat))
  (gfail "Not equal").
intro. exact 4.
apply X. intro. apply y.
(* Fail third if not equal
  (assert ((forall x:Prop, Prop) -> nat))
  (assert ((forall y:Prop, Prop) -> nat))
  (gfail "Not equal").
third if not equal
  (assert ((forall x:Prop, Prop) -> nat))
  (assert ((forall x:Prop, Prop) -> nat))
  (gfail "Not equal").

intro. exact 4.
apply X. intro. apply x. *)
Qed.

Goal nat.
(* Test universes *)
third if not equal
  (assert (forall x, x -> x))
  (assert (forall x, x -> x))
  (gfail "Not equal").
third if not equal (auto) (auto) (gfail).
third if not equal (exact 1) (exact 2) (gfail).
Qed.