(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Solutions of Pell's equation *)

Require Import Arith Omega Eqdep_dec ZArith.

Require Import utils_tac gcd prime binomial sums matrix Zp.

Set Implicit Arguments.

Section Zp_alpha_2.

  Variable (ak am k l m : nat)
           (H1 : m = (l*k)%nat)
           (H2 : (ak*ak <> 0)%nat).

  Notation "〚 u 〛" := (nat2Zp H2 u).
  Infix "⊗" := (Zp_mult H2) (at level 40, left associativity).

  Hypothesis (H3 : (m <> 0)%nat)
             (H4 : exists q, Zp_invertible H2 q /\〚am〛 = q⊗〚l〛⊗〚ak〛). 

  Let Hak : ak <> 0.  Proof. intro; subst; destruct H2; auto. Qed.
  Let Hl : l <> 0.    Proof. contradict H3; subst; ring. Qed.
  Let Hk : k <> 0.    Proof. contradict H3; subst; ring. Qed.

  Lemma Zp_alpha_congruence_2 : divides (ak*ak) am <-> divides (k*ak) m.
  Proof.
    rewrite mult_comm in H1.
    destruct H4 as (q & Hq1 & Hq2).
    split; intros H.
    + rewrite (proj1 (divides_nat2Zp _ _)) in Hq2; auto.
      symmetry in Hq2.
      rewrite <- Zp_mult_assoc in Hq2.
      apply Zp_invertible_eq_zero in Hq2; auto.
      rewrite <- nat2Zp_mult, <- divides_nat2Zp in Hq2.
      destruct Hq2 as (d & Hd); exists d; subst m.
      rewrite <- Nat.mul_cancel_r with (1 := Hak).
      rewrite <- mult_assoc, Hd; ring.
    + subst m.
      apply divides_mult_inv in H; auto.
      destruct H as (g & Hg); subst l.
      rewrite divides_nat2Zp with (Hp := H2).
      rewrite Hq2, nat2Zp_mult. 
      do 2 rewrite <- Zp_mult_assoc.
      rewrite <- nat2Zp_mult, nat2Zp_p.
      do 2 rewrite (Zp_mult_comm _ _ (Zp_zero H2)), Zp_mult_zero.
      trivial.
  Qed.

End Zp_alpha_2.

Local Infix "│" := divides (at level 70, no associativity).

Section Pell.

  Variable (b_nat : nat) (Hb_nat : 2 <= b_nat).

  Fixpoint alpha_nat n := 
    match n with
      | 0   => 0
      | S p => match p with
        | 0   => 1
        | S r => b_nat * alpha_nat p - alpha_nat r
      end
    end.

  Fact alpha_nat_fix_0 : alpha_nat 0 = 0.    Proof. auto. Qed.
  Fact alpha_nat_fix_1 : alpha_nat 1 = 1.    Proof. auto. Qed.

  Fact alpha_nat_fix_2 n : alpha_nat (S (S n)) = b_nat *alpha_nat (S n) - alpha_nat n.
  Proof. auto. Qed.

  Fact alpha_nat_2 n : b_nat = 2 -> alpha_nat n = n.
  Proof.
    intros Hb.
    induction on n as IHn with measure n.
    destruct n as [ | [ | n ] ]; auto.
    rewrite alpha_nat_fix_2, Hb, IHn, IHn; omega.
  Qed.

  Fact alpha_nat_inc n : alpha_nat n < alpha_nat (S n).
  Proof.
    induction n as [ | n IHn ]; try (simpl; omega).
    rewrite alpha_nat_fix_2.
    replace b_nat with (2+(b_nat-2)) by omega.
    rewrite Nat.mul_add_distr_r.
    generalize ((b_nat -2)*alpha_nat (S n)); intro; omega.
  Qed.

  Corollary alpha_nat_mono i j : i <= j -> alpha_nat i <= alpha_nat j.
  Proof.
    induction 1 as [ | j H1 H2 ]; auto.
    apply le_trans with (1 := H2), lt_le_weak, alpha_nat_inc.
  Qed.

  Corollary alpha_nat_smono i j : i < j -> alpha_nat i < alpha_nat j.
  Proof.
    intros; apply lt_le_trans with (1 := alpha_nat_inc _), alpha_nat_mono; auto.
  Qed.

  Fact alpha_nat_ge_n n : n <= alpha_nat n.
  Proof.
    induction n as [ | n IHn ].
    + simpl; auto.
    + apply le_n_S in IHn.
      apply le_trans with (1 := IHn), alpha_nat_inc.
  Qed.

  Fact alpha_nat_gt_0 : forall n, n <> 0 -> alpha_nat n <> 0.
  Proof.
    intros [ | n ] H; try omega.
    generalize (alpha_nat_ge_n (S n)); omega.
  Qed.

  Fact alpha_nat_le n : alpha_nat n <= b_nat * alpha_nat (S n).
  Proof.
    apply le_trans with (1*alpha_nat (S n)).
    + apply lt_le_weak, lt_le_trans with (1 := alpha_nat_inc _); omega.
    + apply mult_le_compat; omega.
  Qed.

  Notation power := (mscal mult 1).

  Fact alpha_nat_power n : 2 < b_nat -> power n (b_nat-1) <= alpha_nat (S n) <= power n b_nat.
  Proof.
    intros Hb.
    induction on n as IHn with measure n.
    destruct n as [ | [ | n ] ].
    + do 2 rewrite power_0; simpl; omega.
    + do 2 rewrite power_1; simpl; omega.
    + rewrite alpha_nat_fix_2.
      destruct (IHn n) as (H1 & H2); try omega.
      destruct (IHn (S n)) as (H3 & H4); try omega.
      split.
      * replace b_nat with (b_nat-1+1) at 2 by omega.
        rewrite Nat.mul_add_distr_r.
        rewrite <- (Nat.add_sub_assoc (_*_)).
        - apply le_trans with (2 := le_plus_l _ _).
          rewrite power_S; apply mult_le_compat; auto.
        - rewrite Nat.mul_1_l; apply alpha_nat_mono; omega.
      * rewrite power_S.
        apply le_trans with (1 := Nat.le_sub_l _ _).
        apply mult_le_compat_l; auto.
  Qed.

  Open Scope Z.

  Let b := Z.of_nat b_nat.
  Let Hb : 2 <= b.
  Proof. apply inj_le with (n:= 2%nat); omega. Qed. 

  Definition alpha_Z n := 
    match n with 
      | 0%nat => -1
      | S n   => Z.of_nat (alpha_nat n)
    end.

  Notation α := alpha_Z.

  Hint Resolve alpha_nat_le.

  Fact alpha_Z_S n : α (S n) = Z.of_nat (alpha_nat n). Proof. auto. Qed.

  Fact alpha_fix_0 : α (0%nat) = -1.     Proof. auto. Qed.
  Fact alpha_fix_1 : α 1%nat = 0.        Proof. auto. Qed.
  Fact alpha_fix_2 : α 2%nat = 1.        Proof. auto. Qed.
  Fact alpha_fix_3 n : α (S (S n)) = b*α (S n) - α n.
  Proof.
    destruct n as [ | n ].
    1: simpl; ring.
    unfold α at 1.
    rewrite alpha_nat_fix_2.
    rewrite Nat2Z.inj_sub; auto.
    rewrite Nat2Z.inj_mul; auto.
  Qed.
 
  Fact alpha_inc n : α n < α (S n).
  Proof. 
    destruct n; simpl; try omega.
    apply inj_lt, alpha_nat_inc. 
  Qed.

  Fact alpha_ge_0 n : 0 <= α (S n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite alpha_fix_1; omega.
    + apply Zlt_le_weak, Z.le_lt_trans with (2 := alpha_inc _); trivial.
  Qed.

  Opaque α.

  Create HintDb alpha_db.

  Hint Rewrite alpha_fix_0 alpha_fix_1 alpha_fix_2 alpha_fix_3 : alpha_db.

  Ltac alpha := autorewrite with alpha_db.

  Fact alpha_2 : b = 2 -> forall n, α n = Z.of_nat n - 1.
  Proof.
    intros H n.
    induction on n as IHn with measure n.
    destruct n as [ | [ | n ] ]; alpha; auto.
    do 2 (rewrite IHn; try omega).
    repeat rewrite Nat2Z.inj_succ.
    rewrite H; omega.
  Qed.

  Notation MZ := (M22 Z).

  Notation MZ_opp := (MI22 Z.opp).
  Notation MZ_plus := (PL22 Zplus).
  Notation MZ_mult := (MU22 Zplus Zmult).
  Notation MZ_zero := (ZE_22 0).
  Notation MZ_one := (ID_22 0 1).
  Notation MZ_scal := (M22scal Zmult).
  Notation MZ_expo := (mscal MZ_mult MZ_one).
  Notation MZ_det := (Det22 Zplus Zmult Z.opp).

  Local Fact MZ_plus_monoid : monoid_theory MZ_plus MZ_zero.
  Proof. apply M22plus_monoid with (1 := Zring). Qed.
 
  Local Fact MZ_mult_monoid : monoid_theory MZ_mult MZ_one.
  Proof. apply M22mult_monoid with (1 := Zring). Qed.

  Hint Resolve MZ_plus_monoid MZ_mult_monoid.
 
  (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)

  Notation "⊟" := MZ_opp.
  Infix "⊞" := MZ_plus (at level 50, left associativity).
  Infix "⊠" := MZ_mult (at level 40, left associativity).

  Definition B  : MZ := (b,-1,1,0).
  Definition iB : MZ := (0,1,-1,b).

  Definition A n := (α (2+n),-α(1+n),α(1+n),-α n).
  Definition iA n := (-α n,α(1+n),-α(1+n),α (2+n)).

  (* b -1   *   0  1 
     1  0      -1  b  *)

  Notation mI := (-1,0,0,-1).

  (* B has an inverse *)

  Fact B_iB : B ⊠ iB = MZ_one.
  Proof. apply M22_equal; ring. Qed.

  Fact iB_i : iB ⊠ B = MZ_one.
  Proof. apply M22_equal; ring. Qed.

  Fact A_is_sum k : A k = MZ_scal (-α k) MZ_one ⊞ MZ_scal (α (S k)) B.
  Proof.
    simpl; apply M22_equal; simpl; alpha; ring.
  Qed.

  Lemma MZ_expo_A n : MZ_expo n B = A n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite mscal_0.
      unfold B, A; simpl.
      rewrite alpha_fix_2, alpha_fix_1, alpha_fix_0.
      apply M22_equal; ring.
    + rewrite mscal_S, IHn.
      apply M22_equal; simpl plus; try ring.
      - rewrite alpha_fix_3 with (n := S _); ring.
      - alpha; ring.
  Qed.

  Hint Resolve MZ_expo_A.

  Fact A_plus u v : A (u+v)%nat = A u ⊠ A v.
  Proof.
    rewrite <- MZ_expo_A, mscal_plus; auto.
    f_equal; auto.
  Qed.

  Fact A_mult u v : A (u*v)%nat = MZ_expo u (A v).
  Proof.
    rewrite <- MZ_expo_A, mscal_mult; auto.
    f_equal; auto.
  Qed.

  Fact A_plus_mult m n k l : 
          (m = n + l * k)%nat 
       -> A m = A n ⊠ MZ_expo l (A k).
  Proof.
    intro; subst; rewrite A_plus, A_mult; auto.
  Qed.

  Fact MZ_det_B : MZ_det B = 1.
  Proof. simpl; ring. Qed.

  Lemma MZ_det_A n : MZ_det (A n) = 1.
  Proof. 
    rewrite <- MZ_expo_A.
    rewrite Det22_expo with (Rminus := Z.sub); auto. 
    rewrite MZ_det_B.
    rewrite mscal_of_unit; auto.
  Qed.

  Definition Pell x y := x*x -b*x*y+y*y=1.

  Theorem alpha_Pell n : Pell (α (S n)) (α n).
  Proof.
    unfold Pell.
    generalize (MZ_det_A n).
    unfold A; simpl; intros H.
    rewrite <- H.
    rewrite alpha_fix_3; ring.
  Qed.

  Fact A_iA n : A n ⊠ iA n = MZ_one.
  Proof.
    generalize (alpha_Pell n); unfold Pell; intros H. 
    apply M22_equal; try ring; simpl; rewrite alpha_fix_3, <- H; ring.
  Qed.

  Fact iA_A n : iA n ⊠ A n = MZ_one.
  Proof.
    generalize (alpha_Pell n); unfold Pell; intros H. 
    apply M22_equal; try ring; simpl; rewrite alpha_fix_3, <- H; ring.
  Qed.

  Fact A_minus u v : (v <= u)%nat -> A (u-v)%nat = A u ⊠ iA v.
  Proof.
    intros H.
    rewrite <- (MZ_expo_A u).
    replace u with (u-v+v)%nat at 2 by omega.
    rewrite mscal_plus; auto.
    do 2 rewrite MZ_expo_A.
    rewrite <- M22mult_assoc with (1 := Zring).
    rewrite A_iA.
    rewrite M22mult_one_r with (1 := Zring).
    trivial.
  Qed.

  Section alpha_nat_coprime. 

    Let A_eq_3_12 n : exists u v, u*α (S n) + v*α n = 1.
    Proof.
      generalize (alpha_Pell n); unfold Pell; intros H. 
      exists (α (S n)-b*α n), (α n).
      rewrite <- H; ring.
    Qed.

    Lemma alpha_nat_coprime n : is_gcd (alpha_nat (S n)) (alpha_nat n) 1.
    Proof. apply Z_coprime, (A_eq_3_12 (S n)). Qed.

    Corollary alpha_nat_odd n : (rem (alpha_nat (S n)) 2 = 1 \/ rem (alpha_nat n) 2 = 1)%nat.
    Proof.
      destruct rem_2_is_0_or_1 with (x := alpha_nat (S n)) as [ H1 | ]; auto.
      destruct rem_2_is_0_or_1 with (x := alpha_nat n) as [ H2 | ]; auto.
      exfalso; generalize (alpha_nat_coprime n); intros (_ & _ & H3).
      destruct (H3 2%nat) as (? & ?); try omega; apply divides_rem_eq; auto.
    Qed.  

  End alpha_nat_coprime.

  Theorem find_odd_alpha u : exists n, (u <= alpha_nat (S n) /\ rem (alpha_nat (S n)) 2 = 1)%nat.
  Proof.
    destruct (alpha_nat_odd (S u)) as [ H | H ]; [ exists (S u) | exists u ]; split; auto;
      apply le_trans with (1 := alpha_nat_ge_n _), alpha_nat_mono; omega.
  Qed.

  Theorem find_odd_alpha' u : exists n, (u <= alpha_nat n /\ rem (alpha_nat n) 2 = 1)%nat.
  Proof.
    destruct (find_odd_alpha u) as (n & ?); exists (S n); auto.
  Qed.

  (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)
 
  Notation expoZ := (mscal Zmult 1).

  Fact expoZ_power n x : expoZ n (Z.of_nat x) = Z.of_nat (power n x).
  Proof. 
    symmetry; apply mscal_morph; auto.
    intros; apply Nat2Z.inj_mul.
  Qed.

  Fact mscal_Zplus n : mscal Zplus 0 n 1 = Z.of_nat n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite mscal_0; auto.
    + rewrite mscal_S, IHn.
      rewrite Nat2Z.inj_succ; ring.
  Qed.

  Notation "∑" := (msum MZ_plus MZ_zero).

  Theorem MA_expo_A_binomial m k l :
          (m = l * k)%nat 
       -> A m = ∑ (S l) (fun i => MZ_scal ( expoZ (l-i) (-1)
                                          * Z.of_nat (binomial l i) 
                                          * expoZ i (α (S k)) 
                                          * expoZ (l-i) (α k) ) 
                                     (MZ_expo i B)).
  Proof.
    intro; subst m.
    rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A, A_is_sum; auto.
    rewrite binomial_Newton with (zero := MZ_zero); auto.
    2: apply M22plus_comm with (1 := Zring).
    2: apply M22plus_cancel with (1 := Zring).
    2: apply M22_mult_distr_l with (1 := Zring).
    2: apply M22_mult_distr_r with (1 := Zring).
    2: apply M22_equal; ring.
    apply msum_ext; intros i Hi.
    repeat rewrite expo22_scal with (1 := Zring).
    rewrite  mscal_of_unit; auto.
    rewrite <- M22scal_MU22_l with (1 := Zring).
    rewrite <- M22scal_MU22_r with (1 := Zring).
    rewrite M22mult_one_l with (1 := Zring).
    rewrite M22scal_mult with (1 := Zring).
    rewrite mscal_M22scal with (1 := Zring).
    rewrite M22scal_mult with (1 := Zring).
    f_equal.
    rewrite mscal_Zplus.
    replace (- α k) with ((-1)*α k) by ring.
    rewrite mscal_sum; auto; ring.
  Qed.

  Section A2m.

    Variable (l m v : nat) (Hv : Z.of_nat v = α (2+m) - α m).

    Fact alpha_SSm_m_neq_0 : v <> 0%nat.
    Proof. 
      intros H; subst; simpl in Hv.
      generalize (alpha_inc m) (alpha_inc (S m)); omega.
    Qed.

    Notation Hv' := alpha_SSm_m_neq_0.

    Let Z2Zp_morph := Z2Zp_morphishm Hv'.

    Notation f := (Z2Zp Hv').
    Notation "〚 x 〛" :=  (f x).
    Notation "〘 x 〙" := (morph22 f x).
    Notation "⊟" := (MI22 (Zp_opp Hv')).
    Infix "⊠" := (MU22 (Zp_plus Hv') (Zp_mult Hv')) (at level 40, left associativity).

    Let Am_iAm_mod :〘A m〙= ⊟〘iA m〙.
    Proof.
      apply M22_equal.
      + rewrite Z2Zp_opp, Zp_opp_inv.
        apply Z2Zp_inj.
        exists 1; rewrite Hv; ring.
      + rewrite Z2Zp_opp; auto.
      + rewrite Z2Zp_opp, Zp_opp_inv; auto.
      + rewrite <- Z2Zp_opp.
        apply Z2Zp_inj.
        exists 1; rewrite Hv; ring.
    Qed.
    
    Fact A2m_mod : 〘A (2*m)〙= ⊟〘MZ_one〙.
    Proof.
      rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
      rewrite mscal_S, mscal_1; auto.
      rewrite MU22_morph with (1 := Z2Zp_morph).
      rewrite Am_iAm_mod at 1.
      do 2 rewrite <- MI22_morph with (1 := Z2Zp_morph).
      rewrite <- MU22_morph with (1 := Z2Zp_morph).
      f_equal.
      rewrite M22_opp_mult_l with (1 := Zring); f_equal.
      apply iA_A.
    Qed.

    Fact A2lm_mod : 〘A (2*l*m)〙= 〘MZ_scal (mscal Zmult 1 l (-1)) MZ_one〙.
    Proof.
      replace (2*l*m)%nat with (l*(2*m))%nat by ring.
      rewrite <- MZ_expo_A, mscal_mult, MZ_expo_A; auto.
      rewrite expo22_morph with (1 := Z2Zp_morph).
      rewrite A2m_mod.
      rewrite <- MI22_morph with (1 := Z2Zp_morph).
      rewrite <- expo22_morph with (1 := Z2Zp_morph).
      f_equal.
      rewrite <- M22scal_MI22 with (1 := Zring).
      change (-(1)) with (-1).
      rewrite expo22_scal with (1 := Zring); f_equal.
      rewrite mscal_of_unit; auto.
    Qed.

    Let expoZ_opp1 i : expoZ i (-1) = 1 \/ expoZ i (-1) = -1.
    Proof.
      induction i as [ | i IHi ].
      + rewrite mscal_0; auto.
      + rewrite mscal_S; omega.
    Qed. 

    Variable (j : nat) (Hl : (l <> 0)%nat) (Hj : (j <= m)%nat).

    Fact alpha_2lm_plus_j :〚α (S (2*l*m+j))〛=〚expoZ l (-1)*α (S j)〛.
    Proof.
      generalize (A_plus (2*l*m) j); intros H.
      apply f_equal with (f := morph22 f) in H.
      rewrite MU22_morph with (1 := Z2Zp_morph) in H.
      rewrite A2lm_mod in H.
      rewrite <- MU22_morph with (1 := Z2Zp_morph) in H.
      apply M22_proj12 in H.
      rewrite Z.mul_0_r, Z.mul_0_l, Z.mul_1_r, Z.add_0_l in H.
      apply H.
    Qed.

    Let Hj' : (j <= 2*l*m)%nat.
    Proof.
      apply le_trans with (1*m)%nat; try omega.
      apply mult_le_compat; omega.
    Qed.

    Fact alpha_2lm_minus_j :〚α (S (2*l*m-j))〛=〚expoZ (S l) (-1)*α (S j)〛.
    Proof.
      generalize (A_minus Hj'); intros H.
      apply f_equal with (f := morph22 f) in H.
      rewrite MU22_morph with (1 := Z2Zp_morph) in H.
      rewrite A2lm_mod in H.
      rewrite <- MU22_morph with (1 := Z2Zp_morph) in H.
      apply M22_proj12 in H.
      rewrite Z.mul_0_r, Z.mul_0_l, Z.mul_1_r, Z.add_0_l in H.
      unfold plus in H; rewrite H; f_equal.
      rewrite mscal_S; ring.
    Qed.
  
    Theorem alpha_nat_2lm_plus_j : nat2Zp Hv' (alpha_nat (2*l*m+j)) = nat2Zp Hv' (alpha_nat j)
                                \/ nat2Zp Hv' (alpha_nat (2*l*m+j)) = Zp_opp Hv' (nat2Zp Hv' (alpha_nat j)).
    Proof.
      generalize (alpha_2lm_plus_j).
      destruct (expoZ_opp1 l) as [ E | E ]; rewrite E; intros H; [ left | right ].
      + repeat rewrite alpha_Z_S in H.
        rewrite Z2Zp_of_nat, Z.mul_1_l, Z2Zp_of_nat in H; auto.
      + repeat rewrite alpha_Z_S in H.
        change (-1) with (-(1)) in H.
        rewrite Z.mul_opp_l, Z.mul_1_l, Z2Zp_opp in H.
        repeat rewrite Z2Zp_of_nat in H; auto.
    Qed.

    Theorem alpha_nat_2lm_minus_j : nat2Zp Hv' (alpha_nat (2*l*m-j)) = nat2Zp Hv' (alpha_nat j)
                                 \/ nat2Zp Hv' (alpha_nat (2*l*m-j)) = Zp_opp Hv' (nat2Zp Hv' (alpha_nat j)).
    Proof.
      generalize (alpha_2lm_minus_j).
      destruct (expoZ_opp1 (S l)) as [ E | E ]; rewrite E; intros H; [ left | right ].
      + repeat rewrite alpha_Z_S in H.
        rewrite Z2Zp_of_nat, Z.mul_1_l, Z2Zp_of_nat in H; auto.
      + repeat rewrite alpha_Z_S in H.
        change (-1) with (-(1)) in H.
        rewrite Z.mul_opp_l, Z.mul_1_l, Z2Zp_opp in H.
        repeat rewrite Z2Zp_of_nat in H; auto.
    Qed.

  End A2m.

  Section expo_congruence.

    Variable (q : nat). 
   
    Notation m := (b_nat*q-q*q-1)%nat.

    Hypothesis Hm : m <> 0%nat.

    Let Hq : (1+q*q < b_nat*q)%nat.
    Proof. omega. Qed.

    Let VP : MZ := (Z.of_nat q,0,1,0).

    Notation Zm_ring := (Zp_is_ring Hm).

    Local Add Ring m_ring : Zm_ring.

    Notation qz := (Z.of_nat q).

    Let Z2Zp_morph := Z2Zp_morphishm Hm.

    (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)

    Infix "⊕" := (Zp_plus Hm) (at level 50, left associativity).
    Infix "⊗" := (Zp_mult Hm) (at level 40, left associativity).
    Notation "∸" := (Zp_opp Hm).
    Notation f := (Z2Zp Hm).
    Notation "〚 x 〛" :=  (f x).
 
    Let qz_eq :〚b〛⊗〚qz〛 ⊕ ∸ (〚qz〛⊗〚qz〛 ⊕〚1〛) = Zp_zero Hm.
    Proof.
      do 2 rewrite <- Z2Zp_mult.
      rewrite <- Z2Zp_plus, <- Z2Zp_opp, <- Z2Zp_plus.
      unfold b.
      do 2 rewrite <- Nat2Z.inj_mul.
      change 1 with (Z.of_nat 1%nat).
      rewrite Z.add_opp_r, <- Nat2Z.inj_add, <- Nat2Z.inj_sub; try omega.
      rewrite Nat.sub_add_distr; fold m.
      rewrite Z2Zp_of_nat, nat2Zp_p; auto.
    Qed.

    Notation "〘 x 〙" := (morph22 f x).
    Infix "⊠" := (MU22 (Zp_plus Hm) (Zp_mult Hm)) (at level 40, left associativity).
    Notation scal := (M22scal (Zp_mult Hm)).

    Let BVP : 〘 B 〙 ⊠ 〘 VP 〙= scal〚qz〛〘 VP 〙.
    Proof.
      apply M22_equal; try rewrite Z2Zp_zero; try ring.
      change (-1) with (-(1)).
      rewrite Z2Zp_opp, Zp_opp_mult, <- (Z2Zp_mult _ 1).
      rewrite Z.mul_1_l, <- (Zp_plus_zero Hm), <- qz_eq.
      ring.
    Qed.    

    Let AnVP n :〘 A n 〙 ⊠ 〘 VP 〙= scal〚expoZ n qz〛〘 VP 〙.
    Proof.
      rewrite <- MZ_expo_A.
      induction n as [ | n IHn ].
      + do 2 rewrite mscal_0.
        apply M22_equal; try rewrite Z2Zp_zero; try rewrite Z2Zp_one; ring.
      + rewrite mscal_plus1; auto.
        rewrite MU22_morph with (1 := Z2Zp_morph).
        rewrite <- M22mult_assoc with (1 := Zm_ring).
        rewrite BVP.
        rewrite <- M22scal_MU22_r with (1 := Zm_ring).
        rewrite IHn, mscal_S, M22scal_mult with (1 := Zm_ring).
        f_equal.
        rewrite Z2Zp_mult; auto.
    Qed.

    Theorem expo_congruence_Z n : nat2Zp Hm q ⊗〚α (S n)〛=〚α n〛⊕ nat2Zp Hm (power n q).
    Proof.
      destruct Z2Zp_morph as [ G1 G2 G3 G4 G5 ].
      generalize (AnVP n); intros H.
      apply  M22_proj12 in H.
      rewrite Z2Zp_one in H. 
      do 2 rewrite Zp_mult_one_r in H.
      rewrite expoZ_power in H. 
      rewrite (Z2Zp_of_nat _ (power _ _)) in H.
      rewrite <- H, Z2Zp_of_nat. 
      simpl plus; rewrite Z2Zp_opp; ring.
    Qed.

    Theorem expo_congruence n : (0 < n)%nat -> nat2Zp Hm (q * alpha_nat n) = nat2Zp Hm (alpha_nat (n-1) + power n q).
    Proof.
      destruct n as [ | n ]; try omega.
      replace (S n-1)%nat with n by omega.
      rewrite nat2Zp_mult.
      generalize (expo_congruence_Z (S n)); intros H.
      do 2 rewrite alpha_Z_S in H.
      do 2 rewrite Z2Zp_of_nat in H.
      rewrite H, nat2Zp_plus; auto.
    Qed.

  End expo_congruence.

  Fact Pell_sym x y : Pell x y <-> Pell y x.
  Proof.
    unfold Pell; split; intros H; rewrite <- H; ring.
  Qed.

  Theorem Pell_zero_left y : Pell 0 y <-> y = 1 \/ y = -1.
  Proof.
    unfold Pell; split.
    + intros H.
      assert ((y-1)*(y+1) = 0) as H1.
      { ring_simplify in H.
        ring_simplify; omega. }
      apply  Zmult_integral in H1; omega.
    + intros [ | ]; subst; ring.
  Qed.

  Theorem Pell_zero_right x : Pell x 0 <-> x = 1 \/ x = -1.
  Proof.
    rewrite Pell_sym; apply Pell_zero_left.
  Qed.

  Theorem Pell_not_diag x : ~ Pell x x.
  Proof.   
    unfold Pell.
    intros H.
    assert (x*((2-b)*x) = 1) as H1.
    { rewrite <- H; ring. }
    generalize H1; intros H2.
    apply Z.eq_mul_1 in H1.
    destruct H1; subst; omega.
  Qed.

  Theorem Pell_opposite_not x y : y < 0 -> 0 < x -> ~ Pell x y.
  Proof.
    intros H1 H2 H3.
    red in H3.
    assert (0 <= - (b *x*y)) as H4.
    { replace (-(b*x*y)) with (b*x*-y) by ring.
      apply Z.mul_nonneg_nonneg; try omega.
      apply Z.mul_nonneg_nonneg; omega. }
    assert (0 < x*x) as H5.
    { apply Z.mul_pos_pos; auto. }
    assert (0 < y*y) as H6.
    { apply Z.mul_neg_neg; auto. }
    revert H3 H4 H5 H6.
    generalize (x*x) (y*y) (b*x*y); intros; omega.
  Qed.

  Theorem Pell_alpha x y : 0 <= y < x -> Pell x y -> { n | x = α (S (S n)) /\ y = α (S n) }.
  Proof.
    induction on x y as IH with measure (Z.to_nat y); intros Hxy HP.
    destruct (Z.eq_dec y 0) as [ Hy | Hy ].
    + exists 0%nat.
      rewrite alpha_fix_1, alpha_fix_2; split; auto.
      subst y; rewrite Pell_zero_right in HP; omega.
    + red in HP.
      assert (x*x = 1 + (b*y)*x - y*y) as H1.
      { rewrite <- HP; ring. }
      assert (0 < y*y) as H2.
      { apply Z.mul_pos_pos; omega. }
      assert (x <= (b*y)) as H3.
      { apply Zmult_le_reg_r with x; [ | rewrite H1 ]; omega. }
      assert (-(y*x) <= - (y*y)) as H4.
      { rewrite <- Z.opp_le_mono.
        apply Zmult_le_compat; omega. }
      assert (x > b*y-y) as H5.
      { apply Zmult_gt_reg_r with x; try omega.
        rewrite H1; rewrite Z.mul_sub_distr_r; omega. }
      destruct (IH y (b*y-x)) as (m & G1 & G2); try omega.
      - apply Z2Nat.inj_lt; omega.
      - red; rewrite <- HP; ring.
      - exists (S m); split; auto.
        rewrite alpha_fix_3, <- G2, <- G1; ring.
  Qed.

End Pell.

Theorem alpha_nat_Pell b n : 
    2 <= b -> alpha_nat b (S n)*alpha_nat b (S n) +  alpha_nat b n * alpha_nat b n  
            = 1 + b*(alpha_nat b (S n) * alpha_nat b n).
Proof.
  intros Hb.
  generalize (alpha_Pell Hb (S n)); intros H; red in H.
  unfold alpha_Z in H.
  apply Nat2Z.inj.
  repeat rewrite Nat2Z.inj_add.
  repeat rewrite Nat2Z.inj_mul.
  change (Z.of_nat 1) with (1%Z).
  rewrite <- H; ring.
Qed.

Theorem alpha_nat_Pell' b n : 
    2 <= b -> alpha_nat b n*alpha_nat b n +  alpha_nat b (S n) * alpha_nat b (S n)  
            = 1 + b*(alpha_nat b n * alpha_nat b (S n)).
Proof.
  rewrite plus_comm, (mult_comm (alpha_nat b n) (alpha_nat b (S n))).
  apply alpha_nat_Pell.
Qed.

Theorem Pell_alpha_nat b x y : 2 <= b -> y <= x -> x*x+y*y = 1+b*(x*y) -> { n | x = alpha_nat b (S n) /\ y = alpha_nat b n }.
Proof.
  intros Hb H2 H1.
  apply f_equal with (f := Z.of_nat) in H1.
  do 2 rewrite Nat2Z.inj_add in H1.
  do 4 rewrite Nat2Z.inj_mul in H1.
  simpl Z.of_nat in H1.
  apply Z.sub_move_r in H1.
  destruct (le_lt_dec x y) as [ H3 | H3 ].
  + revert H1; replace y with x by omega; clear y H2 H3; intros H1.
    exfalso.
    apply (@Pell_not_diag _ Hb (Z.of_nat x)); red.
    rewrite <- H1; ring.
  + destruct (@Pell_alpha _ Hb (Z.of_nat x) (Z.of_nat y)) as (n & P1 & P2).
    * split.
      - apply Zle_0_nat. 
      - apply inj_lt; trivial.
    * red; rewrite <- H1; ring.
    * unfold alpha_Z in P1, P2.
      apply Nat2Z.inj in P1.
      apply Nat2Z.inj in P2.
      exists n; auto.
Qed.

Corollary Pell_alpha_nat' b x y : 2 <= b -> x*x+y*y = 1+b*(x*y) -> { n | x = alpha_nat b n }.
Proof.
  intros H1 H2.
  destruct (le_lt_dec y x) as [ H3 | H3 ].
  + destruct Pell_alpha_nat with (3 := H2) as (n & ? & ?); auto.
    exists (S n); auto.
  + rewrite plus_comm, (mult_comm x y) in H2.
    destruct Pell_alpha_nat with (3 := H2) as (n & ? & ?); auto; try omega.
    exists n; auto.
Qed.

Theorem alpha_nat_2lm b n m l j v : 
          2 <= b 
       -> v = alpha_nat b (S (S m)) - alpha_nat b m
       -> arem n (S m) l j 
       -> rem (alpha_nat b n) v = rem (alpha_nat b j) v
       \/ rem (alpha_nat b n + alpha_nat b j) v = 0.
Proof.
  intros Hb Hv.
  assert (Hv' : Z.of_nat v = (alpha_Z b (S(2 + m)) - alpha_Z b (S m))%Z).
  { rewrite Hv.
    rewrite Nat2Z.inj_sub; auto.
    apply lt_le_weak, alpha_nat_smono; omega. }
  intros (Hk & [ Hl | (Hl1 & Hl2) ] ).
  + destruct alpha_nat_2lm_plus_j with (Hb_nat := Hb) (Hv := Hv') (l := l) (j := j) as [ H | H ].
    - rewrite nat2Zp_inj in H; subst; auto.
    - right; rewrite <- rem_of_0 with v.
      rewrite <- nat2Zp_inj with (Hp := alpha_SSm_m_neq_0 Hb (S m) Hv').
      rewrite nat2Zp_plus, Hl, H, Zp_plus_comm, Zp_minus, nat2Zp_zero; auto.
  + destruct alpha_nat_2lm_minus_j with (Hb_nat := Hb) (Hv := Hv') (l := l) (j := j) as [ H | H ]; auto.
    - rewrite nat2Zp_inj in H; subst; auto.
    - right; rewrite <- rem_of_0 with v.
      rewrite <- nat2Zp_inj with (Hp := alpha_SSm_m_neq_0 Hb (S m) Hv').
      rewrite nat2Zp_plus, Hl2, H, Zp_plus_comm, Zp_minus, nat2Zp_zero; auto.
Qed.

Section divisibility_1.

  Variable (b : nat) (Hb : 2 <= b) (k : nat) (Hk : k <> 0).

  Let Hak : alpha_nat b k <> 0.
  Proof. apply alpha_nat_gt_0; auto. Qed.

  Section equation.

    Variable (m n l : nat) (Hm : m = n+l*k).

    Infix "⊗" := (Zp_mult Hak) (at level 40, left associativity).
    Notation expo := (mscal (Zp_mult Hak) (Zp_one Hak)).

    Hint Resolve Zle_0_nat.

    Section in_Z.

      Notation "〚 x 〛" := (Z2Zp Hak x).  (* congruence class modulo alpha_nat b k *)

      Let Z2ZP_morph := Z2Zp_morphishm Hak.

      Open Scope Z_scope.

      Fact A_k_morph22 : morph22 (Z2Zp Hak) (A b k) = (〚alpha_Z b (2+k)〛,Zp_zero Hak,Zp_zero Hak,〚-alpha_Z b k〛).
      Proof.
        destruct k as [ | k' ]; try omega.
        unfold A; apply M22_equal; auto;
        simpl plus; unfold alpha_Z.
        + rewrite Z2Zp_opp, Z2Zp_pos, Nat2Z.id, nat2Zp_p, Zp_opp_zero; auto.
        + rewrite Z2Zp_pos, Nat2Z.id, nat2Zp_p; auto.
      Qed.

      Lemma alpha_Z_mnlk_eq : 〚 alpha_Z b (1+m) 〛 = 〚 alpha_Z b (1+n) 〛⊗ expo l〚 alpha_Z b (2+k) 〛.
      Proof.
        generalize (A_plus_mult Hb _ _ _ Hm); intros H. 
        apply f_equal with (f := morph22 (Z2Zp Hak)) in H.
        rewrite MU22_morph with (1 := Z2ZP_morph) in H.
        rewrite expo22_morph with (1 := Z2ZP_morph) in H.
        rewrite A_k_morph22 in H.
        rewrite Diag22_expo with (1 := Zp_is_ring Hak) in H.
        unfold A, morph22 in H.
        rewrite MU22_Diag22 with (1 := Zp_is_ring Hak) in H.
        inversion H; auto.
      Qed.

    End in_Z.

    Section in_nat.

      Notation "〚 x 〛" := (nat2Zp Hak x).  (* congruence class modulo alpha_nat b k *)

      Theorem alpha_nat_mnlk_eq : 〚 alpha_nat b m 〛 = 〚 alpha_nat b n 〛⊗ expo l〚 alpha_nat b (1+k) 〛.
      Proof.
        generalize alpha_Z_mnlk_eq.
        simpl plus.
        unfold alpha_Z.
        do 3 (rewrite Z2Zp_pos; auto).
        do 3 rewrite Nat2Z.id; auto.
      Qed.

    End in_nat.

  End equation.

  (* This is property 3.23 *)

  Theorem alpha_nat_divides_k_ge_1 m : alpha_nat b k │ alpha_nat b m <-> k │ m.
  Proof.
    split.
    + intros H1.
      destruct (euclid m Hk) as (l & [ | n ] & E1 & E2).
      { exists l; omega. }
      rewrite plus_comm in E1.
      generalize (alpha_nat_mnlk_eq _ _ E1); intros H2.
      rewrite <- nat2Zp_expo, <- nat2Zp_mult in H2.
      apply nat2Zp_divides in H2; auto.
      apply is_rel_prime_div_r in H2.
      2: apply is_rel_prime_expo, is_gcd_sym, alpha_nat_coprime; auto.
      apply divides_le in H2.
      * apply alpha_nat_smono with (1 := Hb) in E2; omega.
      * apply alpha_nat_gt_0; omega.
    + intros (l & Hl).
      generalize (alpha_nat_mnlk_eq 0 _ Hl); intros H2.
      rewrite <- nat2Zp_expo, <- nat2Zp_mult in H2.
      simpl in H2.
      rewrite nat2Zp_inj in H2.
      rewrite rem_of_0 in H2.
      generalize (div_rem_spec1 (alpha_nat b m) (alpha_nat b k)).
      exists (div (alpha_nat b m) (alpha_nat b k)); omega.
  Qed.

End divisibility_1.

Theorem alpha_nat_divisibility_1 b k m : 2 <= b -> alpha_nat b k │ alpha_nat b m <-> k │ m.
Proof.
  intros Hb.
  destruct (eq_nat_dec k 0) as [ | Hk ]; subst.
  + simpl; split; intros H; apply divides_0_inv in H.
    - destruct (eq_nat_dec m 0) as [ | Hm ]; subst.
      * apply divides_0.
      * generalize (alpha_nat_gt_0 Hb Hm); omega.
    - subst; apply divides_0.
  + apply alpha_nat_divides_k_ge_1; auto.
Qed.

Check alpha_nat_divisibility_1.
Print Assumptions alpha_nat_divisibility_1.

Section divisibility_2.

  Variable (b : nat) (Hb : 2 <= b) (k : nat) (Hk : k <> 0).

  Let Hak : alpha_nat b k <> 0.
  Proof. apply alpha_nat_gt_0; auto. Qed.

  Let ak2 := alpha_nat b k * alpha_nat b k.

  Let Hak2 : ak2 <> 0.
  Proof.
    unfold ak2; intros H.
    apply mult_is_O in H; destruct H as [ H | H ];
     revert H; apply alpha_nat_gt_0; auto. 
  Qed.

  Section equation.

    Variable (m l : nat) (Hm : m = l*k) (Hl : l <> 0).

    (* ⊕  ⊗  ∸    ⊞ ⊠ ⊟ *)

    Infix "⊕" := (Zp_plus Hak2) (at level 50, left associativity).
    Infix "⊗" := (Zp_mult Hak2) (at level 40, left associativity).
    Notation expoZp := (mscal (Zp_mult Hak2) (Zp_one Hak2)).

    Hint Resolve Zle_0_nat.

    Section in_Zp.

      Notation "〚 x 〛" := (Z2Zp Hak2 x).  (* congruence class modulo alpha_nat b k *)

      Let Z2Zp_morph := Z2Zp_morphishm Hak2.

      Open Scope Z_scope.

      Let Zmult_monoid : monoid_theory Zmult 1.
      Proof. exists; intros; ring. Qed.

      Notation MZp := (M22 ak2).
      Infix "⊞" := (PL22 (Zp_plus Hak2)) (at level 50, left associativity).
      Infix "⊠" := (MU22 (Zp_plus Hak2) (Zp_mult Hak2)) (at level 40, left associativity).
      Notation MZp_Z := (ZE_22 (Zp_zero Hak2)).
      Notation MZp_I := (ID_22 (Zp_zero Hak2) (Zp_one Hak2)).
      Notation MZp_expo := (mscal (fun u v => u⊠v) MZp_I).
      Notation MZp_scal := (M22scal (Zp_mult Hak2)).

      Fact A_m_morph22 : morph22 (Z2Zp Hak2) (A b m) 
                       = MZp_scal (expoZp l〚-1〛⊗ expoZp l〚alpha_Z b k〛) MZp_I
                       ⊞ MZp_scal (expoZp (l-1)〚-1〛⊗ nat2Zp Hak2 l ⊗ 〚alpha_Z b (S k)〛⊗ expoZp (l-1)〚alpha_Z b k〛) (morph22 (Z2Zp Hak2) (B b)).
      Proof.
        generalize (MA_expo_A_binomial Hb _ _ Hm); intros H.
        apply f_equal with (f := morph22 (Z2Zp Hak2)) in H.

        rewrite msum_morph with (m2 := fun u v => u⊞v) (u2 := MZp_Z) in H.
        2: simpl; apply M22_equal; apply Z2Zp_zero.
        2: intros (((?&?)&?)&?) (((?&?)&?)&?); apply M22_equal; apply Z2Zp_plus.

        rewrite msum_first_two in H; try omega.
        2: apply M22plus_monoid with (1 := Zp_is_ring Hak2).
        2: { intros i Hi.
             rewrite M22scal_morph with (1 := Z2Zp_morph).
             repeat rewrite Z2Zp_mult.
             replace i with (2+(i-2))%nat at 3 by omega.
             rewrite mscal_plus, Z2Zp_mult; auto.
             rewrite mscal_S, mscal_1; auto.
             unfold alpha_Z at 1 2.
             rewrite <- Nat2Z.inj_mul. 
             fold ak2.
             rewrite (@Z2Zp_pos _ Hak2 (Z.of_nat ak2)); auto.
             rewrite Nat2Z.id, nat2Zp_p. 
             repeat rewrite Zp_mult_zero.
             rewrite (Zp_mult_comm _ _ (Zp_zero _)).
             repeat rewrite Zp_mult_zero.
             apply M22scal_zero with (1 := Zp_is_ring Hak2). }

        rewrite H.
        repeat rewrite M22scal_morph with (1 := Z2Zp_morph).
        repeat rewrite Z2Zp_mult.
        rewrite binomial_n1; try omega.
        rewrite binomial_n0.
        rewrite Nat.sub_0_r.
        repeat rewrite mscal_0.
        repeat rewrite Z2Zp_one.
        f_equal.
        + f_equal; auto.
          2: apply M22_equal; try rewrite Z2Zp_one; auto; rewrite Z2Zp_zero; auto.
          rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
          2: rewrite Z2Zp_one; auto.
          2: apply Z2Zp_mult.
          rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
          2: rewrite Z2Zp_one; auto.
          2: apply Z2Zp_mult.
          repeat rewrite <- Zp_mult_assoc.
          repeat rewrite Zp_mult_one; auto.
        + repeat (rewrite mscal_1; auto).
          2: apply  M22mult_monoid with (1 := Zring).
          rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
          2: rewrite Z2Zp_one; auto.
          2: apply Z2Zp_mult.
          rewrite <- mscal_morph with (m1 := Zmult) (u1 := 1).
          2: rewrite Z2Zp_one; auto.
          2: apply Z2Zp_mult.
          do 4 f_equal.
          rewrite Z2Zp_pos, Nat2Z.id; auto.
      Qed.

      Lemma alpha_Z_ml_eq : 〚 alpha_Z b (S m) 〛 
                          = expoZp (l-1) 〚-1〛
                          ⊗ nat2Zp Hak2 l
                          ⊗〚 alpha_Z b (S k) 〛
                          ⊗ expoZp (l-1)〚 alpha_Z b k 〛.
      Proof.
        generalize A_m_morph22; intros H.
        unfold morph22, A, B in H.
        unfold M22scal, PL22, MZp_I in H.
        apply M22_proj12 in H.
        unfold plus in H; rewrite H; clear H.
        rewrite Zp_mult_comm, Zp_mult_zero, Zp_plus_zero.
        rewrite Z2Zp_one, Zp_mult_comm, Zp_mult_one; auto.
      Qed.

    End in_Zp.

    Local Add Ring myring2 : (Zp_is_ring Hak2).

    Corollary alpha_square_nat : exists q, Zp_invertible Hak2 q /\ nat2Zp Hak2 (alpha_nat b m) = q ⊗ nat2Zp Hak2 l  ⊗ nat2Zp Hak2 (alpha_nat b k).
    Proof.
      exists (expoZp (l-1) (Z2Zp Hak2 (-1)) ⊗ expoZp (l-1) (Z2Zp Hak2 (alpha_Z b k))); split.
      + apply Zp_mult_invertible; apply Zp_expo_invertible.
        * apply Zp_opp_invertible. 
          rewrite <- Z2Zp_opp.
          replace (- (-1))%Z with 1%Z by omega.
          rewrite Z2Zp_one.
          apply Zp_one_invertible.
        * destruct k; try omega; simpl.
          rewrite Z2Zp_of_nat.
          apply nat2Zp_invertible.
          unfold ak2.
          apply is_gcd_sym, is_rel_prime_mult; 
            apply is_gcd_sym, alpha_nat_coprime; auto.
      + generalize alpha_Z_ml_eq; intros H.
        unfold alpha_Z in H at 1 2.
        do 2 rewrite Z2Zp_of_nat in H.
        rewrite H; ring.
    Qed.
  
  End equation.

  Theorem alpha_nat_divides_2_pos m : alpha_nat b k * alpha_nat b k │ alpha_nat b m <-> k*alpha_nat b k │ m.
  Proof.
    destruct m as [ | m ].
    + simpl; split; intros; apply divides_0.
    + destruct (divides_dec (S m) k) as [ (l & Hl) | C ].
      * apply Zp_alpha_congruence_2 with (1 := Hl) (H2 := Hak2); try omega.
        apply alpha_square_nat; auto.
        intro; subst; discriminate.
      * split; intros H; exfalso; apply C.
        - rewrite <- alpha_nat_divisibility_1 with (1 := Hb).
          apply divides_trans with (2 := H), divides_mult, divides_refl.
        - apply divides_trans with (2 := H).
          rewrite mult_comm.
          apply divides_mult, divides_refl.
  Qed.

End divisibility_2.

(** Second divisibility property *)

Theorem alpha_nat_divisibility_2 b k m : 
    2 <= b -> alpha_nat b k * alpha_nat b k │ alpha_nat b m <-> k*alpha_nat b k │ m.
Proof.
  intros Hb.
  destruct k as [ | k ].
  * simpl.
    destruct m as [ | m ]; try (simpl; tauto).
    split; intros H; apply divides_0_inv in H; try discriminate.
    contradict H; apply alpha_nat_gt_0; omega.
  * apply alpha_nat_divides_2_pos; omega.
Qed.

Check alpha_nat_divisibility_2.
Print Assumptions alpha_nat_divisibility_2.

Section congruence_1.

  Variable (b1 b2 : nat) (Hb1 : 2 <= b1) (Hb2 : 2 <= b2)
           (q : nat) (Hq : q <> 0) (Hb : nat2Zp Hq b1 = nat2Zp Hq b2).

  Hint Resolve Zle_0_nat.

  Theorem alpha_Z_congr n : Z2Zp Hq (alpha_Z b1 n) = Z2Zp Hq (alpha_Z b2 n).
  Proof.
    induction on n as IHn with measure n.
    destruct n as [ | [ | n ] ]; try reflexivity.
    do 2 (rewrite alpha_fix_3; auto).
    do 2 rewrite Z2Zp_minus, Z2Zp_mult.
    do 2 f_equal; try (apply IHn; omega).
    do 2 (rewrite Z2Zp_pos; auto).
    do 2 rewrite Nat2Z.id; auto.
  Qed.

End congruence_1.

Theorem alpha_nat_congruence_0 b1 b2 q n : 
           2 <= b1 
        -> 2 <= b2
        -> rem b1 q = rem b2 q 
        -> rem (alpha_nat b1 n) q = rem (alpha_nat b2 n) q.
Proof.
  intros H1 H2 H3.
  destruct (eq_nat_dec q 0) as [ H4 | H4 ].
  + subst; do 2 rewrite rem_0 in H3; subst; auto.
  + rewrite <- nat2Zp_inj with (Hp := H4) in H3.
    apply alpha_Z_congr with (n := S n) in H3; auto.
    simpl in H3.
    do 2 rewrite Z2Zp_of_nat in H3.
    rewrite nat2Zp_inj in H3.
    trivial.
Qed.

Corollary alpha_nat_congruence_1 b n : b-2 <> 0 -> rem (alpha_nat b n) (b-2) = rem n (b-2).
Proof.
  intros Hb.
  rewrite <- alpha_nat_2 with (b_nat := 2) (n := n) at 2; auto.
  apply alpha_nat_congruence_0; try omega.
  replace b with ((b-2)+2) at 1 by omega.
  apply rem_erase with 1; omega.
Qed.

Check alpha_nat_congruence_0.
Check alpha_nat_congruence_1.

Section congruence_2.

  (** This section might notbe needed anymore *)

  Variable (b : nat) (Hb : b - 2 <> 0).

  Notation "〚 x 〛" := (Z2Zp Hb x).  (* congruence class modulo (b-2) *)

  Hint Resolve Zle_0_nat.

  Open Scope Z_scope.

  Theorem alpha_Z_b_2 n : 〚 alpha_Z b n 〛 = Zp_plus Hb 〚 Z.of_nat n 〛〚 -1 〛.
  Proof.
    rewrite <- Z2Zp_plus.
    replace (Z.of_nat n + -1) with (Z.of_nat n -1) by omega.
    rewrite <- (@alpha_2 2); auto.
    apply alpha_Z_congr; try omega.
    replace b with (2+(b-2))%nat at 3 by omega.
    rewrite nat2Zp_plus.
    rewrite nat2Zp_p, Zp_plus_comm, Zp_plus_zero; auto.
  Qed.

End congruence_2.

Lemma rem_eq_eq a b v : 2*a < v -> 2*b < v -> rem a v = rem b v -> a = b.
Proof.
  intros H1 H2 H3.
  do 2 (rewrite rem_lt in H3; try omega).
Qed.

Lemma rem_eq_diff_eq a b v : 2*a < v -> 2*b < v -> (rem a v = rem b v) \/ (rem (a+b) v = 0) -> a = b.
Proof.
  intros H1 H2 [ H3 | H3 ].
  + do 2 (rewrite rem_lt in H3; try omega).
  + rewrite rem_lt in H3; omega.
Qed.

Section diophantine_sufficiency.

  Variables (a b c : nat) (u t r s v w x y : nat).

  Definition alpha_conditions :=
                    3 < b
                 /\ u*u+t*t = 1+b*(u*t)
                 /\ s*s+r*r = 1+b*(s*r)
                 /\ r < s
                 /\ u*u │ s
                 /\ v+2*r = b*s
                 /\ rem w v = rem b v
                 /\ rem w u = rem 2 u
                 /\ 2 < w
                 /\ x*x+y*y = 1+w*(x*y)
                 /\ 2*a < u
                 /\ 2*a < v
                 /\ rem a v = rem x v
                 /\ 2*c < u
                 /\ rem c u = rem x u.

  Theorem alpha_sufficiency : alpha_conditions -> 3 < b /\ a = alpha_nat b c.
  Proof.
    intros (H41 & H42 & H43 & H44 & H45 & H46 & H47 & H48 & H49 & H50 &
            H51 & H52 & H53 & H54 & H55).
    split; auto.
    destruct Pell_alpha_nat' with (2 := H42) as (k & Hu); try omega.
    destruct Pell_alpha_nat with (3 := H43) as (m & Hs & Hr); try omega.
    destruct Pell_alpha_nat' with (2 := H50) as (n & Hx); try omega.
    destruct (@division_by_even n (S m)) as (l & j & Hlj); try omega.
    assert (divides (k*u) (S m)) as H60'.
    { subst u s; apply alpha_nat_divisibility_2; try omega; auto. }
    assert (divides u (S m)) as H60.
    { apply divides_trans with (2 := H60'), divides_mult, divides_refl. }
    assert (v = alpha_nat b (S (S m)) - alpha_nat b m) as H61.
    { rewrite alpha_nat_fix_2, <- Hs, <- Hr; omega. }
    assert (rem x v = rem (alpha_nat b n) v) as H62_1.
    { rewrite Hx; apply alpha_nat_congruence_0; omega. }
    assert (rem x u = rem n u) as H65.
    { rewrite Hx, alpha_nat_congruence_0 with (3 := H48); try omega.
      f_equal; apply alpha_nat_2; auto. }
    assert (2 <= b) as Hb by omega.
    generalize (alpha_nat_2lm Hb H61 Hlj); intros H62_2.
    assert (2*alpha_nat b j < v) as H63.
    { apply le_lt_trans with ((b-2)*alpha_nat b (S m)).
      { apply mult_le_compat; try omega.
        red in Hlj; apply alpha_nat_mono; tauto. }
      apply plus_lt_reg_l with (2*r).
      rewrite (plus_comm _ v), H46, Hr, Hs.
      replace b with (2+(b-2)) at 4 by omega.
      rewrite Nat.mul_add_distr_r.
      apply plus_lt_le_compat; auto.
      apply mult_lt_compat_l; auto.
      apply alpha_nat_inc; auto. }
    rewrite plus_comm, <- rem_plus_rem, <- H62_1, <- H53, rem_plus_rem, plus_comm in H62_2.
    apply rem_eq_diff_eq in H62_2; auto.
    assert (2*j < u) as H66.
    { apply le_lt_trans with (2 := H51), mult_le_compat; auto.
      subst; apply alpha_nat_ge_n; auto. }
    rewrite <- H55 in H65.
    assert (c = j) as H67.
    { destruct H60 as (q & Hq).
      destruct Hlj as (G1 & [ G2 | (G2 & G3) ]).
      + apply rem_eq_diff_eq with u; auto.
        left.
        rewrite H65, rem_erase with (n := 2*l*q) (r := j); auto.
        rewrite G2, Hq; ring.
      + apply rem_eq_diff_eq with u; auto.
        right.
        rewrite plus_comm, <- rem_plus_rem, H65, rem_plus_rem, G3.
        apply rem_prop with (2*l*q); try omega.
        rewrite Hq, mult_assoc.
        assert (2*l*q <> 0) as G4.
        { intros H.
          apply mult_is_O in H; destruct H as [ H | H ]; try (subst; discriminate).
          apply mult_is_O in H; destruct H; omega. }
        assert (1*u <= 2*l*q*u).
        { apply mult_le_compat; auto.
          revert G4; generalize (2*l*q); intros; omega. }
        rewrite Nat.mul_1_l in H.
        revert H; generalize (2*l*q*u); intros; omega. }
    subst; auto.
  Qed.

End diophantine_sufficiency.

Section diophantine_necessity.

  Variables (a b c : nat).

  Theorem alpha_necessity : 3 < b /\ a = alpha_nat b c -> exists u t r s v w x y, alpha_conditions a b c u t r s v w x y.
  Proof.
    intros (H1 & H2).
    assert (2 <= b) as Hb by omega.
    destruct find_odd_alpha' with (b_nat := b) (u := 1+2*a+2*c) as (k & Hk1 & Hk2); try omega.
    remember (alpha_nat b k) as u.
    remember (alpha_nat b (S k)) as t.
    remember (u*k) as m.
    destruct m as [ | m ].
    { symmetry in Heqm.
      apply mult_is_O in Heqm.
      destruct Heqm; subst; try omega.
       rewrite alpha_nat_fix_0, rem_of_0 in Hk2; discriminate. }
    remember (alpha_nat b m) as r.
    remember (alpha_nat b (S m)) as s.
    assert (s*s+r*r = 1+b*(s*r)) as Hrs.
    { rewrite Heqr, Heqs; apply alpha_nat_Pell; auto. }
    assert (k <> 0) as Hk.
    { intro; subst; discriminate. }
    assert (divides (u*u) s) as Hus.
    { rewrite Hequ, Heqs.
      apply alpha_nat_divisibility_2; auto.
      rewrite <- Hequ, Heqm, mult_comm.
      apply divides_refl. }
    assert (2*a < b*s - 2*r) as H3.
    { apply lt_le_trans with (2*u).
      { apply mult_lt_compat_l; omega. }
      apply le_trans with (2*(S m)).
      { apply mult_le_compat_l; rewrite Heqm.
        rewrite <- (Nat.mul_1_r u) at 1.
        apply mult_le_compat; omega. }
      apply le_trans with (2*alpha_nat b (S m)).
      { apply mult_le_compat_l.
        apply le_trans with (1 := alpha_nat_ge_n Hb _).
        apply alpha_nat_mono; omega. }
      apply le_trans with (4*s - 2*r).
      { rewrite Heqs, Heqr.
        generalize (alpha_nat_inc Hb m); intros; omega. }
      apply Nat.sub_le_mono_r, mult_le_compat_r; omega. }
    remember (b*s-2*r) as v.
    assert (is_gcd u v 1) as Huv.
    { split; [ | split ]; try apply divides_1.
      intros d Hd1 Hd2.
      assert (divides d s) as F1.
      { apply divides_trans with (2 := Hus).
        apply divides_trans with (1 := Hd1).
        apply divides_mult, divides_refl. }
      assert (divides d (2*r)) as F2.
      { apply divides_plus_inv with (1 := Hd2).
        replace (v+2*r) with (b*s) by omega.
        apply divides_mult; auto. }
      apply is_rel_prime_div in F2.
      + apply divides_plus_inv with (b*(s*r)).
        * do 2 apply divides_mult; auto.
        * rewrite plus_comm, <- Hrs.
          apply divides_plus; apply divides_mult; auto.
      + apply is_gcd_sym, no_common_prime_is_coprime; try discriminate.
        intros z G0 G1 G2.
        apply divides_2_inv in G1; destruct G1; subst z.
        destruct G0; omega.
        replace (rem u 2) with 0 in Hk2; try discriminate.
        symmetry; apply divides_rem_eq; try discriminate.
        apply divides_trans with (1 := G2); auto. }
    assert (exists w, rem w u = rem 2 u /\ rem w v = rem b v /\ 2 < w) as Hw.
    { apply CRT; auto; try omega. }
    destruct Hw as (w & Hw1 & Hw2 & Hw3).
    remember (alpha_nat w c) as x.
    remember (alpha_nat w (S c)) as y.
    exists u, t, r, s, v, w, x, y; repeat (split; auto); 
      try (subst; (apply alpha_nat_Pell || apply alpha_nat_Pell' || apply alpha_nat_inc)); try omega; auto.
    + rewrite Heqx, alpha_nat_congruence_0 with (3 := Hw2), H2; try omega.
    + rewrite Heqx; symmetry.
      rewrite alpha_nat_congruence_0 with (3 := Hw1); try omega.
      f_equal; apply alpha_nat_2; omega.
  Qed.

End diophantine_necessity.

Theorem alpha_diophantine a b c : 3 < b /\ a = alpha_nat b c 
                              <-> exists u t r s v w x y, alpha_conditions a b c u t r s v w x y.
Proof.
  split.
  + apply alpha_necessity.
  + intros (u & t & r & s & v & w & x & y & H); revert H.
    apply alpha_sufficiency.
Qed.

