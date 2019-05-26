(* This file reproves using the hammer tool the lemmas about
   arithmetic on natural numbers from Reals.ArithProp. The proofs are
   noticeably simpler than the original ones. *)

From Hammer Require Import Hammer Reconstr.

Require Import Arith.

Lemma minus_neq_O : forall n i:nat, (i < n) -> (n - i) <> 0.
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.sub_gt)
		    Reconstr.Empty.
Qed.

Lemma le_minusni_n : forall n i:nat, i <= n -> n - i <= n.
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.le_sub_l, @Coq.Arith.PeanoNat.Nat.le_0_l)
		    Reconstr.Empty.
Qed.

Lemma lt_minus_O_lt : forall m n:nat, m < n -> 0 < n - m.
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.lt_add_lt_sub_l, @Coq.Arith.PeanoNat.Nat.add_0_r, @Coq.Arith.PeanoNat.Nat.lt_add_lt_sub_r, @Coq.Arith.PeanoNat.Nat.add_0_l, @Coq.Init.Peano.le_n)
		    Reconstr.Empty.
Qed.

Lemma even_odd_cor :
  forall n:nat, exists p : nat, n = (2 * p) \/ n = S (2 * p).
Proof.
  induction n; sauto.
  exists 0; ycrush.
  Reconstr.hsimple Reconstr.Empty
		   (@Coq.Arith.PeanoNat.Nat.add_succ_l, @Coq.Arith.PeanoNat.Nat.add_0_r, @Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.add_0_l)
		   Reconstr.Empty.
Qed.

Lemma le_double : forall m n:nat, 2 * m <= 2 * n -> m <= n.
Proof.
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.Mult.mult_S_le_reg_l, @Coq.Init.Peano.le_n)
		    Reconstr.Empty.
Qed.

Lemma tech8 : forall n i:nat, n <= S n + i.
Proof.
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.le_add_r, @Coq.Arith.PeanoNat.Nat.lt_eq_cases)
		    (@Coq.Init.Peano.lt).
Qed.
