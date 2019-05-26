Set Implicit Arguments.

Require Import Arith.
Require Import Div2.
Require Import Recdef.

Function ceil_log2_S (n: nat) {wf lt n}: nat :=
  match n with
  | 0 => 0
  | S _ => S (ceil_log2_S (div2 n))
  end.
Proof.
  intros.
  apply lt_div2; auto with arith.
  apply lt_wf.
Defined.

Lemma ceil_log2_S_def n: ceil_log2_S n =
  match n with
  | 0 => 0
  | S _ => S (ceil_log2_S (div2 n))
  end.
Proof. functional induction (ceil_log2_S n); auto. Qed.
