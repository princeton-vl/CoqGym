Require Import mathcomp.ssreflect.ssreflect.

Structure stuff :=
  Stuff { one : bool; two : nat }.

Lemma stuff_one s b n : s = Stuff b n -> one s = b.
Proof.
by case: s => [b' n']; case =>->.
Qed.
