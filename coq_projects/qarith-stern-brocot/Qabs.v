(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)


Require Export Qsyntax.
Require Export Field_Theory_Q.
Require Export Q_ordered_field_properties.

Definition Qabs (q:Q):Q:= 
  match q with 
  | Zero => Zero
  | Qpos qp => Qpos qp
  | Qneg qp => Qpos qp
  end.

Lemma Qabs_eq: forall q, Zero<=q -> Qabs q = q. 
Proof.
 intros [|q|q] Hq; simpl; trivial; unfold Qle in Hq; contradiction Hq; auto.
Qed.

Lemma Qabs_non_eq: forall q, q<=Zero -> Qabs q = (-q).
Proof.
 intros [|q|q] Hq; simpl; trivial; unfold Qle in Hq; contradiction Hq; auto.
Qed.

Lemma Qabs_eq_pos: forall q, Zero<q -> Qabs q = q. 
Proof.
 intros [|q|q] Hq; simpl; trivial; contradiction (Zero_not_lt_Qneg q). 
Qed.

Lemma Qabs_non_eq_neg: forall q, q<Zero -> Qabs q = (-q).
Proof.
 intros [|q|q] Hq; simpl; trivial; contradiction (Qpos_not_lt_Zero q). 
Qed.

Lemma Qabs_Qmult: forall q1 q2, Qabs (q1*q2) = (Qabs q1) * (Qabs q2).
Proof.
 intros [|q1|q1] [|q2|q2]; simpl; trivial.  
Qed.

Lemma Qabs_5: forall q p, Qabs q <= p -> (- p <= q)/\ (q<= p).
Proof.
 intros [|q|q] [|p|p]; simpl; unfold Qle; intros Hqp; split; auto;
 solve [ apply Zero_not_lt_Qneg|apply Qpos_not_lt_Qneg|apply Qle_opp; simpl; assumption].
Qed.  

Lemma Qabs_6: forall q p, Qabs q <= p -> q<= p.
Proof.
 intros q p H; apply (proj2 (Qabs_5 _ _ H)).
Qed.

Lemma Qabs_7: forall q p, Qabs q <= p -> - p <= q.
 intros q p H; apply (proj1 (Qabs_5 _ _ H)).
Qed.

Lemma Qabs_8: forall q p, - p <= q -> q <= p -> Qabs q <= p.
Proof.
 intros [|q|q] [|p|p]; simpl; unfold Qle; intros H1 H2; auto; apply Qle_opp; simpl; assumption.
Qed.

Lemma Qabs_nonneg: forall q, Zero <= Qabs q.
Proof.
 intros [|q|q]; simpl; auto. 
Qed.

Lemma Qle_Qabs: forall q, q <= Qabs q.
Proof.
 intros [|q|q]; simpl; auto. 
Qed.

Lemma Qle_Qabs_Qopp: forall q, -q <= Qabs q.
Proof.
 intros [|q|q]; simpl; auto. 
Qed.

Lemma Qabs_Qle_Qopp: forall q, - (Qabs q) <= q.
Proof.
 intros [|qp|qp]; simpl; auto.
Qed.

Lemma Qabs_triangle: forall p q, Qabs (p + q) <= Qabs p + Qabs q.
Proof.
 intros p q. 
 destruct (Q_le_lt_dec Zero p) as [Hp|Hp]; destruct (Q_le_lt_dec Zero q) as [Hq|Hq].
  repeat rewrite Qabs_eq; auto.

  assert (Hp1:=Qabs_eq _ Hp); assert (Hq1:=Qabs_non_eq_neg _ Hq); rewrite Hp1; rewrite Hq1;
  destruct (Q_le_lt_dec Zero (p+q)) as [Hpq|Hpq].
   rewrite Qabs_eq; trivial; apply Qle_Zero_Qminus_neg; stepl (q+q);[|ring]; auto.
   rewrite Qabs_non_eq_neg; trivial; apply Qle_Zero_Qminus; stepr (p+p);[|ring]; auto.
   
  assert (Hp1:=Qabs_non_eq_neg _ Hp); assert (Hq1:=Qabs_eq _ Hq); rewrite Hp1; rewrite Hq1;
  destruct (Q_le_lt_dec Zero (p+q)) as [Hpq|Hpq].
   rewrite Qabs_eq; trivial; apply Qle_Zero_Qminus_neg; stepl (p+p);[|ring]; auto.
   rewrite Qabs_non_eq_neg; trivial; apply Qle_Zero_Qminus; stepr (q+q);[|ring]; auto.

  repeat rewrite Qabs_non_eq_neg; auto; (stepr (-(p+q)) by ring); trivial.
Qed.
   
Lemma Qabs_Qopp:forall q, Qabs q = Qabs (-q).
Proof.
 intros [|qp|qp]; trivial.
Qed.

Lemma Qabs_Qminus_sym:forall q1 q2, Qabs (q1-q2) = Qabs (q2-q1).
Proof.
 intros q1 q2; rewrite Qabs_Qopp; apply (f_equal Qabs); ring.
Qed.

Lemma Qabs_nonzero_pos:forall q, q<> Zero -> Zero < Qabs q.
Proof.
 intros [|qp|qp] H; simpl; trivial; contradiction H; trivial. 
Qed.

Lemma Qabs_Qminus_Zero_eq:forall q1 q2, Qabs (q1-q2) = Zero -> q1=q2.
Proof.
 intros q1 q2 Hq; destruct (Q_zerop (q1-q2)) as [H|H]; auto; contradiction (Qlt_irreflexive Zero);
 stepr (Qabs (q1 - q2)); trivial; apply Qabs_nonzero_pos; trivial.
Qed.


Lemma Qabs_Zero_Qminus_eq:forall q1 q2, q1=q2 -> Qabs (q1-q2) = Zero.
Proof.
 intros q1 q2 Hq; rewrite Hq; replace (q2-q2) with Zero by ring; reflexivity. 
Qed.

Lemma Qabs_Qminus_bound:forall low up q1 q2, low <= q1 -> q1 <= up -> low <= q2 -> q2 <= up -> Qabs (q1-q2) <= up-low.  
Proof.
 intros l u q1 q2 Hq1l Hq1u Hq2l Hq2u.
 destruct (Q_le_lt_dec q2 q1) as [H|H];
 [ rewrite Qabs_eq;
  [ 
  | apply Qle_Qminus_Zero
  ]
 | rewrite Qabs_non_eq_neg;
   [ stepl (q2-q1);[|ring]
   | apply Qlt_Qminus_Zero_neg
   ]
 ]; trivial; unfold Qminus; apply Qle_plus_plus; try apply Qopp_Qle; trivial.
Qed.

Lemma upper_bound_affine_base_interval_twice:forall a b c d x, -Qone<=x -> x<=Qone -> 
 (a*x+b)*(c*x+d) <= Qabs (a*c) + Qabs (a*d+c*b)+b*d.
Proof.
 intros a b c d x Hxl Hxu.
 assert (Hxx0:=Qmult_mult_nonneg x).
 assert (Hxx1:=Qmult_mult_Qle_Qone_Qopp_Qone _ Hxl Hxu). 
 stepl ((a*c)*(x*x)+(a*d+c*b)*x+b*d); [|ring].
 repeat apply Qle_plus_plus; trivial.
  stepr (Qabs (a*c)*Qone); [|ring];
  apply Qle_trans with (Qabs (a*c)*(x*x));
  [apply Qle_reg_mult_r_strong; trivial; apply Qle_Qabs| apply Qle_reg_mult_l_strong; trivial; apply Qabs_nonneg]...
  apply Qle_trans with (Qabs((a*d+c*b)*x)); [apply Qle_Qabs|];
  rewrite Qabs_Qmult; stepr (Qabs(a*d+c*b)*Qone); [|ring];
  apply Qle_reg_mult_l_strong; [apply Qabs_nonneg|];
  apply Qabs_8; trivial...
Qed.


Lemma lower_bound_affine_base_interval_twice:forall a b c d x, -Qone<=x -> x<=Qone -> 
        -Qabs (a*c) + -Qabs (a*d+c*b)+b*d <= (a*x+b)*(c*x+d).
Proof.
 intros a b c d x Hxl Hxu.
 assert (Hxx0:=Qmult_mult_nonneg x).
 assert (Hxx1:=Qmult_mult_Qle_Qone_Qopp_Qone _ Hxl Hxu). 
 stepr ((a*c)*(x*x)+(a*d+c*b)*x+b*d); [|ring].
 repeat apply Qle_plus_plus; trivial.
  stepl (-Qabs (a*c)*Qone); [|ring];
  apply Qle_trans with (-Qabs (a*c)*(x*x));
  [ apply Qle_opp; 
    repeat rewrite <- Qmult_Qopp_left; apply Qle_reg_mult_l_strong; trivial; rewrite Qopp_involutive; apply Qabs_nonneg
  | apply Qle_reg_mult_r_strong; trivial; apply Qabs_Qle_Qopp
  ]...
  apply Qle_trans with (-Qabs((a*d+c*b)*x)); [|apply Qabs_Qle_Qopp];
  apply Qopp_Qle;
  rewrite Qabs_Qmult; stepr (Qabs(a*d+c*b)*Qone); [|ring];
  apply Qle_reg_mult_l_strong; [apply Qabs_nonneg|];
  apply Qabs_8; trivial...
Qed.
