Require Import Coq.omega.Omega.

Lemma strong_induction {P: nat -> Prop}:
  (forall n, (forall m, m < n -> P m) -> P n) ->
  (forall n, P n).
Proof.
  intros ?.
  assert (forall n, (forall m, m < n -> P m)).
  + intro n; induction n.
    - intros; omega.
    - intros.
      destruct (lt_dec m n).
      * apply IHn; auto.
      * assert (m = n) by omega; subst m.
        apply H; auto.
  + intros.
    apply (H0 (S n)).
    constructor.
Qed.

Ltac strong_induction n :=
  revert dependent n;
  intro n;
  pattern n;
  revert n;
  apply strong_induction;
  intros ?n ?IH.
