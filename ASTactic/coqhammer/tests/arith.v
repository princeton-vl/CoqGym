From Hammer Require Import Hammer Reconstr.

Hammer_version.
Hammer_objects.

Set Hammer CrushLimit 0.
Set Hammer GSMode 6.

Require Import Arith.

Lemma lem_1 : le 1 2.
  hammer.
Qed.

Lemma lem_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hammer.
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
  hammer.
Qed.

Lemma lem_3 : le 2 3.
  hammer.
Qed.

Lemma lem_4 : le 3 10.
  hammer.
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer.
Qed.

Lemma lem_rew : forall m n : nat, 1 + n + m + 1 = m + 2 + n.
Proof.
  hammer.
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  hammer.
Qed.

Lemma minus_neq_O : forall n i:nat, (i < n) -> (n - i) <> 0.
Proof.
  hammer.
Qed.

Lemma le_minusni_n : forall n i:nat, i <= n -> n - i <= n.
Proof.
  hammer.
Qed.

Lemma even_odd_cor :
  forall n:nat, exists p : nat, n = (2 * p) \/ n = S (2 * p).
Proof.
  induction n; sauto.
  exists 0; ycrush.
  hammer.
Qed.

Lemma le_double : forall m n:nat, 2 * m <= 2 * n -> m <= n.
Proof.
  hammer.
Qed.
