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


Definition Qmax p q := if Q_le_lt_dec p q then q else p.

Definition Qmin p q := if Q_le_lt_dec p q then p else q.

Lemma Qle_max_l: forall p q, p <= Qmax p q.
Proof.
 intros p q; unfold Qmax; destruct (Q_le_lt_dec p q); simpl; trivial.
Qed.

Lemma Qle_max_r: forall p q, q <= Qmax p q.
Proof.
 intros p q; unfold Qmax; destruct (Q_le_lt_dec p q); auto. 
Qed.

Lemma Qmax_lub: forall q1 q2 p, q1 <= p -> q2 <= p -> Qmax q1 q2 <= p.
Proof.
 intros q1 q2 p H1 H2; unfold Qmax; destruct (Q_le_lt_dec q1 q2); trivial.
Qed.

Lemma Qmax_Qlt_upper_bound:forall p q1 q2, p<q1 -> p<q2 ->p < Qmax q1 q2.
Proof.
 intros p q1 q2 H1 H2; unfold Qmax; destruct (Q_le_lt_dec q1 q2); trivial.
Qed.

Lemma Qmax_nondecreasing: forall q1 q2 p1 p2, q1 <= p1 -> q2 <= p2 -> Qmax q1 q2 <= Qmax p1 p2.
Proof.
 intros q1 q2 p1 p2 H1 H2; unfold Qmax; destruct (Q_le_lt_dec q1 q2); destruct (Q_le_lt_dec p1 p2); trivial; 
 [apply Qlt_le_weak; apply Qle_lt_trans with p2 | apply Qle_trans with p1]; trivial.
Qed.

Lemma Qmin_Qmax_Qle:forall q1 q2, Qmin q1 q2 <= Qmax q1 q2.
Proof.
 intros q1 q2; unfold Qmax, Qmin; destruct (Q_le_lt_dec q1 q2); trivial; apply Qlt_le_weak; assumption.
Qed.

Lemma Qmin_nondecreasing: forall q1 q2 p1 p2, q1 <= p1 -> q2 <= p2 -> Qmin q1 q2 <= Qmin p1 p2.
Proof.
 intros q1 q2 p1 p2 H1 H2; unfold Qmin; destruct (Q_le_lt_dec q1 q2); destruct (Q_le_lt_dec p1 p2); trivial;
 [apply Qle_trans with q2| apply Qlt_le_weak; apply Qlt_le_trans with q1]; trivial.
Qed.

Lemma Qmin_glb: forall q1 q2 p, p<=q1 -> p<=q2 -> p<=Qmin q1 q2.
Proof.
 intros q1 q2 p H1 H2; unfold Qmin; destruct (Q_le_lt_dec q1 q2); trivial.
Qed.

Lemma Qmin_Qlt_upper_bound:forall p q1 q2, p<q1 -> p<q2 ->p < Qmin q1 q2.
Proof.
 intros p q1 q2 H1 H2; unfold Qmin; destruct (Q_le_lt_dec q1 q2); trivial.
Qed.

Lemma Qle_min_l: forall p q : Q, Qmin p q <= p.
Proof.
 intros p q; unfold Qmin; destruct (Q_le_lt_dec p q); trivial ; apply Qlt_le_weak; assumption.
Qed.

Lemma Qle_min_r: forall p q : Q, Qmin p q <= q.
Proof.
 intros p q; unfold Qmin; destruct (Q_le_lt_dec p q); trivial ; apply Qlt_le_weak; assumption.
Qed.

Lemma Qmax_or_informative:forall p q, {Qmax p q = p} + {Qmax p q = q}.
Proof.
 intros p q; unfold Qmax; destruct (Q_le_lt_dec p q); auto.
Qed.

Lemma Qmin_or_informative:forall p q, {Qmin p q = p} + {Qmin p q = q}.
Proof.
 intros p q; unfold Qmin; destruct (Q_le_lt_dec p q); auto.
Qed.

Definition Qmax4 q1 q2 q3 q4 := Qmax (Qmax q1 q2) (Qmax q3 q4).
Definition Qmin4 q1 q2 q3 q4 := Qmin (Qmin q1 q2) (Qmin q3 q4).

Lemma Qmax4_informative:forall q1 q2 q3 q4, {Qmax4 q1 q2 q3 q4=q1} + {Qmax4 q1 q2 q3 q4=q2} + {Qmax4 q1 q2 q3 q4=q3} + {Qmax4 q1 q2 q3 q4=q4}.
Proof.
 intros q1 q2 q3 q4; unfold Qmax4; 
 destruct (Qmax_or_informative (Qmax q1 q2) (Qmax q3 q4)) as [H|H]; rewrite H;
  [ left; left; exact (Qmax_or_informative q1 q2)
  | destruct (Qmax_or_informative q3 q4) as [H'|H']; rewrite H'; auto]. 
Qed. 

Lemma Qmin4_informative:forall q1 q2 q3 q4, {Qmin4 q1 q2 q3 q4=q1} + {Qmin4 q1 q2 q3 q4=q2} + {Qmin4 q1 q2 q3 q4=q3} + {Qmin4 q1 q2 q3 q4=q4}.
Proof.
 intros q1 q2 q3 q4; unfold Qmin4; 
 destruct (Qmin_or_informative (Qmin q1 q2) (Qmin q3 q4)) as [H|H]; rewrite H;
  [ left; left; exact (Qmin_or_informative q1 q2)
  | destruct (Qmin_or_informative q3 q4) as [H'|H']; rewrite H'; auto]. 
Qed. 

Lemma Qmin4_Qmax4_Qle:forall q1 q2 q3 q4, Qmin4 q1 q2 q3 q4<= Qmax4 q1 q2 q3 q4.
Proof.
 intros q1 q2 q3 q4; unfold Qmax4, Qmin4;
 apply Qle_trans with (Qmin (Qmax q1 q2) (Qmax q3 q4)); [apply Qmin_nondecreasing|]; apply Qmin_Qmax_Qle.
Qed.

Lemma Qle_Qmax4_1:forall q1 q2 q3 q4, q1<=Qmax4 q1 q2 q3 q4.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmax q1 q2); unfold Qmax4; apply Qle_max_l.
Qed.

Lemma Qle_Qmax4_2:forall q1 q2 q3 q4, q2<=Qmax4 q1 q2 q3 q4.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmax q1 q2); unfold Qmax4; apply Qle_max_l || apply Qle_max_r.
Qed.

Lemma Qle_Qmax4_3:forall q1 q2 q3 q4, q3<=Qmax4 q1 q2 q3 q4.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmax q3 q4); unfold Qmax4; apply Qle_max_l || apply Qle_max_r.
Qed.

Lemma Qle_Qmax4_4:forall q1 q2 q3 q4, q4<=Qmax4 q1 q2 q3 q4.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmax q3 q4); unfold Qmax4; apply Qle_max_r.
Qed.

Lemma Qle_Qmin4_1:forall q1 q2 q3 q4, Qmin4 q1 q2 q3 q4<= q1.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmin q1 q2); unfold Qmin4; apply Qle_min_l.
Qed.

Lemma Qle_Qmin4_2:forall q1 q2 q3 q4, Qmin4 q1 q2 q3 q4<= q2.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmin q1 q2); unfold Qmin4; apply Qle_min_l || apply Qle_min_r.
Qed.

Lemma Qle_Qmin4_3:forall q1 q2 q3 q4, Qmin4 q1 q2 q3 q4<= q3.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmin q3 q4); unfold Qmin4; apply Qle_min_l || apply Qle_min_r.
Qed.

Lemma Qle_Qmin4_4:forall q1 q2 q3 q4, Qmin4 q1 q2 q3 q4<= q4.
Proof.
 intros q1 q2 q3 q4; apply Qle_trans with (Qmin q3 q4); unfold Qmin4; apply Qle_min_r.
Qed.

Lemma Qmax4_Qlt_upper_bound:forall p q1 q2 q3 q4, p<q1 -> p<q2 -> p<q3 -> p<q4 -> p < Qmax4 q1 q2 q3 q4.
Proof.
 intros p q1 q2 q3 q4 H1 H2 H3 H4; unfold Qmax4; repeat apply Qmax_Qlt_upper_bound; assumption.
Qed.

Lemma Qlt_Qmin_upper_bound: forall p q1 q2 : Q, p < Qmin q1 q2 -> p < q1 /\ p < q2.
Proof.
 intros p q1 q2; split; apply Qlt_le_trans with (Qmin q1 q2); trivial; [apply Qle_min_l|apply Qle_min_r].
Qed.

Definition Qlt_Qmin_upper_bound_l p q1 q2 (hyp:p < Qmin q1 q2) : p < q1 :=proj1 (Qlt_Qmin_upper_bound p q1 q2 hyp).
Definition Qlt_Qmin_upper_bound_r p q1 q2 (hyp:p < Qmin q1 q2) : p < q2 :=proj2 (Qlt_Qmin_upper_bound p q1 q2 hyp).

Lemma Qmax_Qlt_lower_bound: forall p q1 q2 : Q, q1 < p  -> q2 < p -> Qmax q1 q2 < p.
Proof.
 intros p q1 q2 H1 H2; unfold Qmax; destruct (Q_le_lt_dec q1 q2); trivial.
Qed.

Lemma Qlt_Qmax_lower_bound: forall p q1 q2 : Q, Qmax q1 q2 < p -> q1 < p /\ q2 < p.
Proof.
 intros p q1 q2; split; apply Qle_lt_trans with (Qmax q1 q2); trivial; [apply Qle_max_l|apply Qle_max_r].
Qed.

Definition Qlt_Qmax_lower_bound_l p q1 q2 (hyp:Qmax q1 q2 < p) := proj1 (Qlt_Qmax_lower_bound p q1 q2 hyp).
Definition Qlt_Qmax_lower_bound_r p q1 q2 (hyp:Qmax q1 q2 < p) := proj2 (Qlt_Qmax_lower_bound p q1 q2 hyp).

Lemma Qmin_involutive : forall q, Qmin q q = q.
Proof.
 intros q; destruct (Qmin_or_informative q q); trivial.
Qed.

Lemma Qmax_involutive : forall q, Qmax q q = q.
Proof.
 intros q; destruct (Qmax_or_informative q q); trivial.
Qed.

Definition Qmean (x y:Q):Q := (x+y) / (Qone + Qone).

Lemma Qmean_property:forall (x y:Q), x < y -> x < Qmean x y /\ Qmean x y < y.
Proof.
 intros x y H; split; unfold Qmean.
  apply Qmult_pos_Qlt_Qdiv; auto; stepl (x+x); auto; ring.  
  apply Qmult_pos_Qdiv_Qlt; auto; stepr (y+y); auto; ring.
Qed.

Definition Qmean_property_l x y (hyp:x<y) := proj1 (Qmean_property x y hyp).
Definition Qmean_property_r x y (hyp:x<y) := proj2 (Qmean_property x y hyp).

Lemma Qmean_incr: forall x1 x2 y1 y2, x1< x2 -> y1 < y2 ->  Qmean x1 y1 < Qmean x2 y2.
Proof.
 intros x1 x2 y1 y2 Hx Hy; unfold Qmean;
 apply Qmult_Qdiv_pos; auto;
 (stepl (x1 + x1 + y1 + y1) by ring); stepr (x2 + x2 + y2 + y2) ; auto; ring. 
Qed.

Theorem Q_is_dense:forall x y, x<y -> {z:Q | x<z /\ z<y}.
Proof.
 intros x y Hxy; exists (Qmean x y); apply Qmean_property; trivial.
Qed.
