(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Require Import Arith.
Require Import Zbase.

Definition succZ (x : Z) :=
  match x return Z with
  | OZ => IZ
  | pos n => pos (S n)
  | neg n => match n return Z with
             | O => OZ
             | S m => neg m
             end
  end.

Definition predZ (x : Z) :=
  match x return Z with
  | OZ => neg 0
  | pos n => match n return Z with
             | O => OZ
             | S m => pos m
             end
  | neg n => neg (S n)
  end.

Lemma pred_succZ : forall x : Z, predZ (succZ x) = x.
intro x; elim x; auto with arith.
intro n; elim n; auto with arith.
Qed.

Lemma succ_predZ : forall x : Z, succZ (predZ x) = x.
intro x; elim x; auto with arith.
intro n; elim n; auto with arith.
Qed.

Lemma succ_pred_pred_succZ : forall x : Z, succZ (predZ x) = predZ (succZ x).
intro x; try assumption.
rewrite (pred_succZ x); rewrite (succ_predZ x); trivial with arith.
Qed.

Lemma tech_pred_posZ : forall n : nat, 0 < n -> predZ (pos n) = pos (pred n).
intro n; elim n; auto with arith.
intro H'; elim (lt_n_O 0); auto with arith.
Qed.

Lemma tech_succ_posOZ : forall n : nat, succZ (posOZ n) = pos n.
intro n; elim n; auto with arith.
Qed.


