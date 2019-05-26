(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** ** Exponentiation is Diophantine *)

Require Import Arith Omega Eqdep_dec ZArith.

Require Import utils_tac gcd sums Zp alpha.

Set Implicit Arguments.

Local Notation expo := (mscal mult 1).

Section expo_diophantine.

  Variables (p q r : nat).

  Definition expo_conditions :=       
      r = 0 /\ p = 1
   \/ q = 0 /\ 0 < r /\ p = 0
   \/ (0 < r /\ q <> 0) /\ exists b m a1 a2 a3, 
             (3 < q+4 /\ a1 = alpha_nat (q+4) (1+r)) 
          /\ (3 < b   /\ a2 = alpha_nat b r)
          /\ (3 < b   /\ a3 = alpha_nat b (1+r))
          /\ b = a1+q*q+2
          /\ m + q*q + 1 = b*q
          /\ p < m
          /\ rem (p+b*a2) m = rem (q*a2+a3) m.

  Let H_q3_q : 0 < q -> q*q+2 <= q*q*q+2*q.
  Proof.
    intros H. 
    apply plus_le_compat; try omega.
    replace q with (1+(q-1)) at 3 by omega.
    rewrite <- mult_assoc, Nat.mul_add_distr_r, Nat.mul_1_l.
    apply le_plus_l.
  Qed.

  Lemma expo_sufficiency : p = expo r q -> expo_conditions.
  Proof.
    intros H.
    destruct (le_lt_dec r 0) as [ Hr | Hr ]; red.
    1: { left; revert H; replace r with 0 by omega; rewrite mscal_0; tauto. } 
    destruct (eq_nat_dec q 0) as [ Hq | Hq ].
    1: { right; left; subst; rewrite power_of_0; auto. }
    remember (alpha_nat (q+4) (S r)) as a1.
    remember (a1+q*q+2) as b.
    remember (alpha_nat b r) as a2.
    remember (alpha_nat b (1+r)) as a3.
    remember (b*q-q*q-1) as m.
    right; right; split; auto; exists b, m, a1, a2, a3.
    assert (3 < b) as Hb.
    { rewrite Heqb.
      apply lt_le_trans with (1+(1*1)+2); try omega.
      repeat apply plus_le_compat; auto.
      + rewrite Heqa1.
        apply alpha_nat_mono with (i := 1); omega.
      + apply mult_le_compat; omega. }
    assert (2 <= b) as Hb' by omega.
    destruct (@alpha_nat_power (q+4)) with (n := r)
        as (H1 & H2); try omega.
    assert (q*q+2 <= q*q*q+2*q) as Hq'.
    { apply H_q3_q; omega. }
    assert (m <> 0) as Hm.
    { rewrite Heqm, Heqb.
      do 2 rewrite  Nat.mul_add_distr_r.
      assert (a1*q <> 0) as Ha1.
      { intros E; apply mult_is_O in E.
        destruct E as [ E | ]; try omega.
        revert E; rewrite Heqa1.
        apply alpha_nat_gt_0; omega. }
      revert Ha1; generalize (a1*q); intros x Hx.
      omega. }
    assert (expo r q < m) as Hexpo.
    { rewrite Heqm, Heqb. 
      do 2 rewrite Nat.mul_add_distr_r.
      rewrite <- Heqa1 in H1.
      apply lt_le_trans with (a1*1+1).
      + rewrite plus_comm, Nat.mul_1_r; apply le_n_S.
        apply le_trans with (2 := H1).
        apply power_mono_r; omega.
      + rewrite <- Nat.sub_add_distr, <- plus_assoc, <- Nat.add_sub_assoc; try omega.
        apply plus_le_compat; try omega.
        apply mult_le_compat; omega. }  
    repeat (split; auto); try omega.
    rewrite <- nat2Zp_inj with (Hp := Hm).
    do 2 rewrite nat2Zp_plus.
    rewrite Heqa2. 
    revert Hm; rewrite Heqm; intros Hm.
    rewrite expo_congruence; auto.
    rewrite <- H, plus_comm, nat2Zp_plus, <- Zp_plus_assoc; f_equal.
    rewrite <- nat2Zp_plus; f_equal.
    rewrite Heqa3.
    destruct r as [ | r' ]; try omega.
    replace (S r' -1) with r' by omega.
    simpl plus at 2.
    rewrite alpha_nat_fix_2.
    generalize (alpha_nat_le Hb' r'); omega.
  Qed.

  Infix "⊕" := (Zp_plus _) (at level 50, left associativity).
  Infix "⊗" := (Zp_mult _) (at level 40, left associativity).
  Notation "∸" := (Zp_opp _).
  Notation f := (nat2Zp _).
  Notation "〚 x 〛" :=  (f x).

  Ltac fold_nat2Zp := 
    repeat match goal with 
      | |- context[nat2Zp _ ?x ⊕ nat2Zp _ ?y] => rewrite <- nat2Zp_plus
      | |- context[nat2Zp _ ?x ⊗ nat2Zp _ ?y] => rewrite <- nat2Zp_mult
      | |- context[∸ nat2Zp _ ?x] => fail
    end.

  Lemma expo_necessity : expo_conditions -> p = expo r q.
  Proof.
    unfold expo_conditions.
    intros [ (H1 & H2) | [ (H1 & H2 & H3) | ((H0 & H1) & b & m & a1 & a2 & a3 & (_ & H2) & 
                                            (H3 & H4) & (H5 & H6) & H7 & H8 & H9 & H10) ] ].
    + subst; auto.    
    + subst; rewrite power_of_0; auto.
    + assert (m = b*q - q*q -1) as Hm1 by omega.
      assert (m <> 0) as Hm by omega.
      assert (q*q+2 <= q*q*q+2*q) as Hq'.
      { apply H_q3_q; omega. }
      assert (expo r q < m) as Hq.
      { rewrite Hm1, H7.
        do 2 rewrite Nat.mul_add_distr_r.
        apply lt_le_trans with (a1*1+1).
        + rewrite plus_comm, Nat.mul_1_r; apply le_n_S.
          destruct alpha_nat_power with (b_nat := q+4) (n := r)
            as (G1 & _); try omega.
          rewrite H2. 
          apply le_trans with (2 := G1), power_mono_r; omega.
        + rewrite <- Nat.sub_add_distr, <- plus_assoc, <- Nat.add_sub_assoc; try omega.
          apply plus_le_compat; try omega.
          apply mult_le_compat; omega. }
      rewrite <- (rem_lt Hm H9), <- (rem_lt Hm Hq).
      revert H10. 
      rewrite Hm1 in Hm |- *.
      do 2 rewrite <- nat2Zp_inj with (Hp := Hm).
      do 2 rewrite nat2Zp_plus.
      rewrite H4, expo_congruence; auto; [ | omega ].
      rewrite H6, nat2Zp_plus.
      destruct r as [ | r' ]; [ omega | ].
      replace (S r' -1) with r' by omega.
      simpl plus.
      rewrite alpha_nat_fix_2, nat2Zp_minus. 
      2: apply alpha_nat_le; omega.
      intros H; rewrite Zp_opp_plus_eq in H.
      rewrite H.
      rewrite (Zp_plus_comm _ 〚b * _〛 (∸ _)).
      repeat rewrite <- Zp_plus_assoc.
      rewrite Zp_minus, Zp_plus_zero_r.
      rewrite Zp_plus_comm, <- Zp_plus_assoc.
      rewrite (Zp_plus_comm _ (∸ _)), Zp_minus, Zp_plus_zero_r.
      trivial.
  Qed.

End expo_diophantine.

Local Hint Resolve expo_sufficiency expo_necessity.

Theorem expo_diophantine p q r : p = expo r q <-> expo_conditions p q r.
Proof. split; auto. Qed.
