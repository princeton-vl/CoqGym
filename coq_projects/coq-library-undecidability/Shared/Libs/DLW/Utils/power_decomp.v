(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Base p representation *)

Require Import Arith Nat Omega.
Require Import utils_tac gcd rel_iter sums.

Set Implicit Arguments.

Local Notation power := (mscal mult 1).
Local Notation "∑" := (msum plus 0).

Fact sum_0n_distr_in_out n a b f :
      ∑ n (fun i => (a i+b i) * f i) 
    = ∑ n (fun i => a i * f i) 
    + ∑ n (fun i => b i * f i).
Proof.
  rewrite <- msum_sum; auto.
  + apply msum_ext; intros; ring.
  + intros; ring.
Qed.

Section power_decomp.

  Variable (p : nat) (Hp : 2 <= p).

  Let power_nzero x : power x p <> 0.
  Proof. generalize (@power_ge_1 x p); omega. Qed.

  Fact power_decomp_lt n f a q :  
           (forall i j, i < j < n -> f i < f j)
        -> (forall i, i < n -> f i < q)
        -> (forall i, i < n -> a i < p)
        -> ∑ n (fun i => a i * power (f i) p) < power q p.
  Proof.
    revert q; induction n as [ | n IHn ]; intros q Hf1 Hf2 Ha.
    + rewrite msum_0; apply power_ge_1; omega.
    + rewrite msum_plus1; auto.
      apply lt_le_trans with (1*power (f n) p + a n * power (f n) p).
      * apply plus_lt_le_compat; auto.
        rewrite Nat.mul_1_l.
        apply IHn.
        - intros; apply Hf1; omega.
        - intros; apply Hf1; omega.
        - intros; apply Ha; omega.
      * rewrite <- Nat.mul_add_distr_r.
        replace q with (S (q-1)).
        - rewrite power_S; apply mult_le_compat; auto.
          ++ apply Ha; auto.
          ++ apply power_mono_l; try omega.
             generalize (Hf2 n); intros; omega.
        - generalize (Hf2 0); intros; omega.
  Qed.

  Lemma power_decomp_is_digit n a f : 
           (forall i j, i < j < n -> f i < f j)
        -> (forall i, i < n -> a i < p)
        ->  forall i, i < n -> is_digit (∑ n (fun i => a i * power (f i) p)) p (f i) (a i).
  Proof.
    intros Hf Ha.
    induction n as [ | n IHn ]; intros i Hi.
    + omega.
    + split; auto.
      exists (∑ (n-i) (fun j => a (S i + j) * power (f (S i+j) - f i - 1) p)), 
             (∑ i (fun j => a j * power (f j) p)); split.
      - replace (S n) with (S i + (n-i)) by omega.
        rewrite msum_plus, msum_plus1; auto.
        rewrite <- plus_assoc, plus_comm; f_equal.
        rewrite Nat.mul_add_distr_r, plus_comm; f_equal.
        rewrite <- mult_assoc, mult_comm, <- sum_0n_scal_l.
        apply msum_ext.
        intros j Hj.
        rewrite (mult_comm (_ * _));
        repeat rewrite <- mult_assoc; f_equal.
        rewrite <- power_S, <- power_plus; f_equal.
        generalize (Hf i (S i+j)); intros; omega.
      - apply power_decomp_lt; auto.
        * intros; apply Hf; omega.
        * intros; apply Ha; omega.
  Qed.

  Theorem power_decomp_unique n f a b :
            (forall i j, i < j < n -> f i < f j)
         -> (forall i, i < n -> a i < p)
         -> (forall i, i < n -> b i < p)
         -> ∑ n (fun i => a i * power (f i) p)
          = ∑ n (fun i => b i * power (f i) p)
         -> forall i, i < n -> a i = b i.
  Proof.
    intros Hf Ha Hb E i Hi.
    generalize (power_decomp_is_digit _ _ Hf Ha Hi)
               (power_decomp_is_digit _ _ Hf Hb Hi).
    rewrite E; apply is_digit_fun.
  Qed.

End power_decomp.

Section power_decomp_uniq.

  Variable (p : nat) (Hp : 2 <= p).

  Theorem power_decomp_factor n f a : 
           (forall i, 0 < i < S n -> f 0 < f i)
        -> ∑ (S n) (fun i => a i * power (f i) p) 
         = ∑ n (fun i => a (S i) * power (f (S i) - f 0 - 1) p) * power (S (f 0)) p
         + a 0 * power (f 0) p.
  Proof.
    intros Hf.
    rewrite msum_S, plus_comm; f_equal.
    rewrite <- sum_0n_scal_r.
    apply msum_ext.
    intros i Hi.
    rewrite <- mult_assoc; f_equal.
    rewrite <- power_plus; f_equal.
    generalize (Hf (S i)); intros; omega.
  Qed.

  Let power_nzero x : power x p <> 0.
  Proof.
    generalize (@power_ge_1 x p); omega.
  Qed.

  Let lt_minus_cancel a b c : a < b < c -> b - a - 1 < c - a - 1.
  Proof. intros; omega. Qed. 

  (* Another proof of the above statement *)

  Theorem power_decomp_unique' n f a b :
            (forall i j, i < j < n -> f i < f j)
         -> (forall i, i < n -> a i < p)
         -> (forall i, i < n -> b i < p)
         -> ∑ n (fun i => a i * power (f i) p)
          = ∑ n (fun i => b i * power (f i) p)
         -> forall i, i < n -> a i = b i.
  Proof.
    revert f a b.
    induction n as [ | n IHn ]; intros f a b Hf Ha Hb.
    + intros; omega.
    + assert (forall i, 0 < i < S n -> f 0 < f i)
        by (intros; apply Hf; omega). 
      do 2 (rewrite power_decomp_factor; auto).
      intros E.
      apply div_rem_uniq in E; auto.
      * destruct E as (E1 & E2).
        intros [ | i ] Hi.
        - revert E2; rewrite Nat.mul_cancel_r; auto.
        - apply IHn with (4 := E1); try omega.
          ++ intros u j Hu; apply lt_minus_cancel; split; apply Hf; omega. 
          ++ intros; apply Ha; omega.
          ++ intros; apply Hb; omega.
      * rewrite power_S.
        apply Nat.mul_lt_mono_pos_r.
        - apply power_ge_1; omega.
        - apply Ha; omega.
      * rewrite power_S.
        apply Nat.mul_lt_mono_pos_r.
        - apply power_ge_1; omega.
        - apply Hb; omega.
  Qed.

End power_decomp_uniq.

Fact mult_2_eq_plus x : x + x = 2 *x.
Proof. ring. Qed.

Section power_injective.

  Let power_2_inj_1 i j n : j < i -> 2* power n 2 <> power i 2 + power j 2.
  Proof.
    rewrite <- power_S; intros H4 E.
     generalize (@power_ge_1 j 2); intro C.
     destruct (lt_eq_lt_dec i (S n)) as [ [ H5 | H5 ] | H5 ].
     + apply power_mono_l with (x := 2) in H5; auto.
       rewrite power_S in H5.
       apply power_mono_l with (x := 2) in H4; auto.
       rewrite power_S in H4; omega.
     + subst i; omega.
     + apply power_mono_l with (x := 2) in H5; auto.
      rewrite power_S in H5; omega.
  Qed.

  Fact power_2_inj i j : power i 2 = power j 2 -> i = j.
  Proof.
    intros H.
    destruct (lt_eq_lt_dec i j) as [ [ C | C ] | C ]; auto;
      apply power_smono_l with (x := 2) in C; omega.
  Qed.

  Let power_plus_lt a b c : a < b < c -> power a 2 + power b 2 < power c 2.
  Proof.
    intros [ H1 H2 ].
    apply power_mono_l with (x := 2) in H2; auto.
    apply power_smono_l with (x := 2) in H1; auto.
    rewrite power_S in H2; omega.
  Qed.

  Let power_inj_2 i1 j1 i2 j2 : 
             j1 < i1 
          -> j2 < i2 
          -> power i1 2 + power j1 2 = power i2 2 + power j2 2
          -> i1 = i2 /\ j1 = j2.
  Proof.
    intros H1 H2 H3.
    destruct (lt_eq_lt_dec i1 i2) as [ [ C | C ] | C ].
    + generalize (@power_plus_lt j1 i1 i2); intros; omega.
    + split; auto; apply power_2_inj; subst; omega.
    + generalize (@power_plus_lt j2 i2 i1); intros; omega.
  Qed.

  Theorem sum_2_power_2_injective i1 j1 i2 j2 :
              j1 <= i1 
           -> j2 <= i2 
           -> power i1 2 + power j1 2 = power i2 2 + power j2 2 
           -> i1 = i2 /\ j1 = j2.
  Proof.
    intros H1 H2 E.
    destruct (eq_nat_dec i1 j1) as [ H3 | H3 ];
    destruct (eq_nat_dec i2 j2) as [ H4 | H4 ].
    + subst j1 j2.
      assert (i1 = i2); auto.
      do 2 rewrite mult_2_eq_plus, <- power_S in E.
      apply power_2_inj in E; omega.
    + subst j1; rewrite mult_2_eq_plus in E.
      apply power_2_inj_1 in E; omega.
    + subst j2; symmetry in E.
      rewrite mult_2_eq_plus in E.
      apply power_2_inj_1 in E; omega.
    + revert E; apply power_inj_2; omega.
  Qed. 
 
End power_injective.
