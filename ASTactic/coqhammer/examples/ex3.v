(* This file contains a proof of the fact that the square root of 2 is
   irrational. *)

From Hammer Require Import Hammer Reconstr.

Require Import Reals.
Require Import Arith.
Require Import Wf_nat.
Require Import Even.
Require Import Omega.

Lemma lem_0 : forall n m, n <> 0 -> m * m = 2 * n * n -> m < 2 * n.
Proof.
  intros n m H H0.
  assert (H1: m < 2 * n \/ m >= 2 * n).
  Reconstr.hobvious Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.lt_trichotomy, @Coq.Arith.PeanoNat.Nat.lt_eq_cases)
		    (@Coq.Init.Peano.ge).
  destruct H1 as [ H1 | H1 ]; yisolve.
  exfalso.
  assert (H2: m * m >= 2 * n * (2 * n)).
  assert (H2: m * m >= 2 * n * m).
  Reconstr.htrivial (@H1)
		    (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.mul_le_mono_nonneg_r)
		    (@Coq.Init.Peano.ge).
  assert (H3: 2 * n * m >= 2 * n * (2 * n)).
  Reconstr.htrivial (@H1)
		    (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.mul_le_mono_nonneg_l)
		    (@Coq.Init.Peano.ge).
  eauto with arith.
  assert (HH: 2 * n * (2 * n) = 2 * (2 * n * n)).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.mul_shuffle3)
		    Reconstr.Empty.
  rewrite HH in *; clear HH.
  rewrite H0 in *; clear H0 H1.
  assert (H0: forall a b, 2 * a >= 2 * b -> a >= b).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.ArithProp.le_double)
		    (@Coq.Init.Peano.ge).
  assert (H1: n * n >= 2 * n * n).
  Reconstr.hsimple (@H2, @H0)
		   (@Coq.Arith.Mult.mult_assoc_reverse)
		   Reconstr.Empty.
  clear -H H1.
  assert (H0: n * n <> 0).
  Reconstr.hsimple (@H)
		   Reconstr.Empty
		   (@Coq.Init.Nat.mul, @Coq.Init.Nat.add).
  assert (H2: forall k, k <> 0 -> k < 2 * k).
  cbn; intros; omega.
  assert (n * n < 2 * n * n).
  Reconstr.hexhaustive 0 (@H0, @H2)
		       (@Coq.Arith.Mult.mult_assoc_reverse)
		       Reconstr.Empty.
  omega.
Qed.

Lemma lem_main : forall n m, n * n = 2 * m * m -> m = 0.
Proof.
  intro n; pattern n; apply lt_wf_ind; clear n.
  intros n H m H0.
  assert (H1: n = 0 \/ n <> 0) by ycrush.
  destruct H1 as [H1|H1]; subst.
  Reconstr.hsimple (@H0)
		   (@Coq.Arith.PeanoNat.Nat.mul_pos_pos, @Coq.Arith.PeanoNat.Nat.neq_0_lt_0, @Coq.Arith.PeanoNat.Nat.add_0_r)
		   (@Coq.Init.Nat.add).
  assert (HH: exists k, n = 2 * k \/ n = 2 * k + 1).
  assert (HEven: Nat.Even n \/ Nat.Odd n).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.Even_or_Odd)
		    Reconstr.Empty.
  Reconstr.hobvious (@HEven)
		    (@Coq.Arith.PeanoNat.Nat.mul_0_r)
		    (Reconstr.Empty).
  destruct HH as [k HH].
  destruct HH as [H2|H2]; subst.
  
  assert (2 * k * k = m * m).
  assert (2 * 2 * k * k = (2 * k * (2 * k))).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.mul_shuffle2, @Coq.Arith.Mult.mult_assoc_reverse)
		    Reconstr.Empty.
  assert (2 * 2 * k * k = 2 * m * m) by ycrush.
  assert (forall a b, 2 * a = 2 * b -> a = b).
  cbn; intros; omega.
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Arith.PeanoNat.Nat.mul_shuffle3, @Coq.Arith.Mult.mult_assoc_reverse)
		   Reconstr.Empty.
  clear H0.
  assert (m < 2 * k).
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Arith.PeanoNat.Nat.nlt_0_r, @Coq.Arith.PeanoNat.Nat.neq_0_lt_0, @lem_0, @Coq.Arith.PeanoNat.Nat.lt_0_mul)
		   Reconstr.Empty.
  assert (k = 0) by ycrush.
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.Arith.PeanoNat.Nat.mul_0_r)
		    Reconstr.Empty.
  
  clear -H0.
  assert (HH: (2 * k + 1) * (2 * k + 1) = 2 * (2 * k * k + k + k) + 1).
  Reconstr.heasy Reconstr.Empty
		 (@Coq.Arith.PeanoNat.Nat.add_0_r, @Coq.Arith.PeanoNat.Nat.add_succ_r, @Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Arith.PeanoNat.Nat.mul_comm, @Coq.Arith.PeanoNat.Nat.mul_add_distr_l, @Coq.Arith.PeanoNat.Nat.mul_shuffle3, @Coq.Arith.PeanoNat.Nat.mul_succ_l)
		 Reconstr.Empty.
  rewrite HH in *; clear HH.
  assert (Nat.Odd (2 * (2 * k * k + k + k) + 1)).
  Reconstr.hobvious (@H0)
		    Reconstr.Empty
		    (@Coq.Arith.PeanoNat.Nat.Odd).
  assert (Nat.Even (2 * m * m)).
  Reconstr.hcrush Reconstr.Empty
		  (@Coq.Arith.PeanoNat.Nat.mul_assoc)
		  (@Coq.Arith.PeanoNat.Nat.Even).
  Reconstr.hsimple Reconstr.AllHyps
		   (@Coq.Arith.Mult.odd_even_lem)
		   (@Coq.Arith.PeanoNat.Nat.Even).
Qed.

Theorem thm_irrational :
  forall (p q : nat), q <> 0 -> sqrt 2 <> (INR p / INR q)%R.
Proof.
  unfold not.
  intros p q H H0.
  assert (2 * q * q = p * p).
  assert (((sqrt 2) ^ 2)%R = 2%R).
  Reconstr.hsimple Reconstr.Empty
		   (@Coq.Reals.R_sqrt.Rsqr_sqrt, @Coq.fourier.Fourier_util.Rle_zero_pos_plus1, @Coq.fourier.Fourier_util.Rle_zero_1, @Coq.Reals.Rfunctions.Rsqr_pow2)
		   Reconstr.Empty.
  assert (((INR p / INR q) ^ 2)%R = ((INR p / INR q) * (INR p / INR q))%R).
  Reconstr.hcrush Reconstr.AllHyps
		  (@Coq.Reals.R_sqrt.Rsqr_sqrt, @Coq.Reals.DiscrR.Rlt_R0_R2)
		  (@Coq.Reals.Rdefinitions.Rle, @Coq.Reals.RIneq.Rsqr).
  assert (((INR p / INR q) * (INR p / INR q))%R = ((INR p * INR p) / (INR q * INR q))%R).
  Reconstr.hobvious Reconstr.AllHyps
		    (@Coq.Reals.R_sqr.Rsqr_div, @Coq.Reals.RIneq.not_0_INR)
		    (@Coq.Reals.RIneq.Rsqr).
  assert (HH: 2%R = ((INR p * INR p) / (INR q * INR q))%R).
  Reconstr.htrivial Reconstr.AllHyps
		    (@Coq.fourier.Fourier_util.Rlt_zero_1, @Coq.Reals.RIneq.Rinv_1, @Coq.fourier.Fourier_util.Rle_zero_1)
		    (@Coq.setoid_ring.Field_theory.Fcons2).
  assert (INR q <> 0%R).
  Reconstr.hobvious (@H)
		    (@Coq.Reals.RIneq.not_0_INR)
		    Reconstr.Empty.
  assert (HH2: (2 * INR q * INR q)%R = (INR p * INR p)%R).
  rewrite HH; rewrite Rmult_assoc.
  Reconstr.hcrush Reconstr.AllHyps
	          (@Coq.Reals.RIneq.Rmult_1_r, @Coq.Reals.RIneq.Rmult_integral_contrapositive_currified, @Coq.Reals.Raxioms.Rmult_assoc, @Coq.Reals.RIneq.Rinv_l_sym)
		  (@Coq.Reals.Rdefinitions.Rdiv).
  clear -HH2.
  assert (forall a b, INR a = INR b -> a = b).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.INR_IZR_INZ, @Coq.Reals.RIneq.S_INR, @Coq.Reals.RIneq.INR_eq, @Coq.Arith.Minus.minus_n_O)
		    (@Coq.Reals.RiemannInt_SF.Nbound, @Coq.Init.Nat.pred, @Coq.Reals.Raxioms.INR, @Coq.Init.Nat.sub).
  assert (INR (2 * q * q) = INR (p * p)).
  assert (INR (p * p) = (INR p * INR p)%R).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.mult_INR)
		    Reconstr.Empty.
  assert (INR (2 * q * q) = (2 * INR q * INR q)%R).
  assert (INR (2 * q * q) = (INR 2 * INR q * INR q)%R).
  Reconstr.htrivial Reconstr.Empty
		    (@Coq.Reals.RIneq.mult_INR)
		    Reconstr.Empty.
  Reconstr.htrivial Reconstr.AllHyps
		    Reconstr.Empty
		    (@Coq.Reals.Raxioms.INR).
  ycrush.
  ycrush.
  Reconstr.hcrush Reconstr.AllHyps
		  (@lem_main)
		  Reconstr.Empty.
Qed.
