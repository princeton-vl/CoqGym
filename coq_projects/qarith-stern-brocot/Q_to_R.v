(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/lgpl-2.1.html>         *)
(************************************************************************)

(* This file contains properties of the injection from Q into R. *)

Require Import Q_ordered_field_properties.
Require Import R_addenda.
Require Import Raxioms.
Require Import RIneq.


(** We define the injection from Q into R *)

Definition Q_to_R (q:Q) : R := ((IZR (numerator q))/(IZR (denominator q)))%R.

Coercion Q_to_R : Q>->R.


Lemma Q_to_Req: forall x y, @eq Q  x y -> ((Q_to_R x)=(Q_to_R y))%R.
Proof.
 exact (f_equal Q_to_R).
Qed.

Lemma Q_to_R_Zero: (Q_to_R Zero=0)%R.
Proof.
 unfold Q_to_R, numerator, denominator, decode_Q; simpl; field; apply R1_neq_R0. 
Qed.

Lemma Q_to_R_Qone: (Q_to_R Qone=1)%R.
Proof.
 unfold Q_to_R, numerator, denominator, decode_Q; simpl; field; apply R1_neq_R0. 
Qed.

Lemma Q_to_R_Qneg_One: (Q_to_R (Qneg One)=(-1))%R.
Proof.
 unfold Q_to_R, numerator, denominator, decode_Q; simpl; field; apply R1_neq_R0. 
Qed.

Lemma Q_to_Ropp: forall x, Q_to_R (Qopp x) = Ropp (Q_to_R x).
 intros [ |p|p]. 
  simpl; rewrite Q_to_R_Zero; ring.
  (* Qpos *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qopp, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  field; auto.  
  (* Qneg *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qopp, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  field; auto.  
Qed.

Lemma Q_to_Rplus: forall x y, Q_to_R (Qplus x y) = (Rplus (Q_to_R x) (Q_to_R y)).
Proof.
 intros [ |p|p] [ |p'|p']; try rewrite Q_to_R_Zero; try rewrite Qplus_zero_left; 
 try rewrite Qplus_zero_right; try rewrite Rplus_0_r;
 try rewrite Rplus_0_l; trivial.
  (* 00 *)
  unfold Q_to_R, numerator, denominator, decode_Q; simpl; field; apply R1_neq_R0...
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qplus, fst, snd;
  unfold Qpositive_plus.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S q0' + S p0' * S q0)%nat with (S (q0'+p0*(S q0')+S (q0+p0'*(S q0))))%nat; auto with arith.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; auto with arith.
  set (m:=((q0' + p0 * S q0') + S (q0 + p0' * S q0))%nat).
  set (n:=(q0' + q0 * S q0')%nat).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c  (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite <- INR_IZR_INZ.
  rewrite Rplus_Rdiv; auto.
  rewrite <- (Rdiv_Rmult_simplify (INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite S_INR.
  repeat rewrite mult_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
  (* +- *)
  unfold Q_to_R at 1, numerator, denominator, decode_Q, Qplus, fst, snd.
  destruct (Qpositive_le_dec p p') as [H_le_dec|H_le_dec].
  destruct (Qpositive_eq_dec p p') as [H_eq_dec|H_eq_dec].
   (* p=p' *)
   subst p; rewrite Qopp_Qpos; rewrite Q_to_Ropp; rewrite Rplus_opp_r; simpl; field; auto.
   (* p<p' *)
   unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
   unfold Qpositive_sub.
   generalize (Qpositive_le_to_Qpositive_le' p p' H_le_dec); unfold Qpositive_le'.
   generalize (Qpositive_le_noneq_explicit p p' H_le_dec H_eq_dec).
   destruct (interp_non_zero p) as [p0 [q0 H]].
   destruct (interp_non_zero p') as [p0' [q0' H']].
   rewrite H; rewrite H'; intros H_le_dec_unfolded H_let.
   assert (H_le_unfold:   (S q0' + p0 * S q0' <= q0 + p0' * S q0)%nat); auto with arith. 
   replace (S p0' * S q0 - S p0 * S q0')%nat with (S (q0+p0'*(S q0)- (S q0'+p0*(S q0'))))%nat;
   [| rewrite (minus_Sn_m _ _ H_le_unfold); auto with arith ].
   replace (S q0' * S q0)%nat with (S (q0+q0'*(S q0)))%nat; auto with arith.
   replace (S p0' * S q0 + S p0 * S q0')%nat with (S (q0+p0'*(S q0)+S (q0'+p0*(S q0'))))%nat; auto with arith.
   set (m':=((q0 + p0' * S q0) + S (q0' + p0 * S q0'))%nat).
   set (m:=((q0 + p0' * S q0) - (S q0' + p0 * S q0'))%nat).
   set (n:=(q0 + q0' * S q0)%nat).
   assert (H_m':(S m + S n <= S m' + S n)%nat);
    [ subst m m' n; apply plus_le_compat_r; apply le_n_S; apply le_trans with (q0 + p0' * S q0)%nat; auto with arith;
      apply le_minus |].
   destruct (construct_correct2  (S m'+S n) m n H_m') as [factor [H_factor1 H_factor2]].
   generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
   set (P:=(Qpositive_c  (S m) (S n) (S m' + S n))).
   destruct (interp_non_zero P) as [P0 [Q0 H'']].
   rewrite H''.
   unfold fst, snd. 
   intros H_factor1  H_factor2.
   repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
   rewrite Rplus_Rdiv; auto.
   rewrite <- (Rdiv_Rmult_simplify (- INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
   rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
   rewrite <- H_factor1; rewrite <- H_factor2.
   apply Rmult_Rdiv; auto.
   subst m n.
   repeat rewrite S_INR.
   rewrite minus_INR; trivial.
   repeat rewrite plus_INR.
   repeat rewrite mult_INR.
   repeat rewrite S_INR.
   ring.
   (* p<p' *)
   unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
   unfold Qpositive_sub.
   generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_le_dec)).
   generalize (not_Qpositive_le_Qpositive_le' _ _ H_le_dec); 
   clear H_le_dec; intros H_le_dec H_eq_dec.
   generalize (Qpositive_le_to_Qpositive_le' p' p H_le_dec); unfold Qpositive_le'.
   generalize (Qpositive_le_noneq_explicit p' p H_le_dec H_eq_dec).
   destruct (interp_non_zero p) as [p0 [q0 H]].
   destruct (interp_non_zero p') as [p0' [q0' H']].
   rewrite H; rewrite H'; intros H_le_dec_unfolded H_lt.
   assert (H_le_unfold:   (S q0 + p0' * S q0 <= q0' + p0 * S q0')%nat); auto with arith. 
   replace (S p0 * S q0' - S p0' * S q0)%nat with (S (q0'+p0*(S q0')- (S q0+p0'*(S q0))))%nat;
   [| rewrite (minus_Sn_m _ _ H_le_unfold); auto with arith ].
   replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; auto with arith.
   replace (S p0 * S q0' + S p0' * S q0)%nat with (S (q0'+p0*(S q0')+S (q0+p0'*(S q0))))%nat; auto with arith.
   set (m':=((q0' + p0 * S q0') + S (q0 + p0' * S q0))%nat).
   set (m:=((q0' + p0 * S q0') - (S q0 + p0' * S q0))%nat).
   set (n:=(q0' + q0 * S q0')%nat).
   assert (H_m':(S m + S n <= S m' + S n)%nat);
    [ subst m m' n; apply plus_le_compat_r; apply le_n_S; apply le_trans with (q0' + p0 * S q0')%nat; auto with arith;
      apply le_minus |].
   destruct (construct_correct2  (S m'+S n) m n H_m') as [factor [H_factor1 H_factor2]].
   generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
   set (P:=(Qpositive_c  (S m) (S n) (S m' + S n))).
   destruct (interp_non_zero P) as [P0 [Q0 H'']].
   rewrite H''.
   unfold fst, snd. 
   intros H_factor1  H_factor2.
   repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
   rewrite Rplus_Rdiv; auto.
   rewrite <- (Rdiv_Rmult_simplify (INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
   rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
   rewrite <- H_factor1; rewrite <- H_factor2.
   apply Rmult_Rdiv; auto.
   subst m n.
   repeat rewrite S_INR.
   rewrite minus_INR; trivial.
   repeat rewrite plus_INR.
   repeat rewrite mult_INR.
   repeat rewrite S_INR.
   ring.
  (* -+ *)
  unfold Q_to_R at 1, numerator, denominator, decode_Q, Qplus, fst, snd.
  destruct (Qpositive_le_dec p p') as [H_le_dec|H_le_dec].
  destruct (Qpositive_eq_dec p p') as [H_eq_dec|H_eq_dec].
   (* p=p' *)
   subst p; rewrite Qopp_Qpos; rewrite Q_to_Ropp; rewrite Rplus_opp_l; simpl; field; auto.
   (* p<p' *)
   unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
   unfold Qpositive_sub.
   generalize (Qpositive_le_to_Qpositive_le' p p' H_le_dec); unfold Qpositive_le'.
   generalize (Qpositive_le_noneq_explicit p p' H_le_dec H_eq_dec).
   destruct (interp_non_zero p) as [p0 [q0 H]].
   destruct (interp_non_zero p') as [p0' [q0' H']].
   rewrite H; rewrite H'; intros H_le_dec_unfolded H_let.
   assert (H_le_unfold:   (S q0' + p0 * S q0' <= q0 + p0' * S q0)%nat); auto with arith. 
   replace (S p0' * S q0 - S p0 * S q0')%nat with (S (q0+p0'*(S q0)- (S q0'+p0*(S q0'))))%nat;
   [| rewrite (minus_Sn_m _ _ H_le_unfold); auto with arith ].
   replace (S q0' * S q0)%nat with (S (q0+q0'*(S q0)))%nat; auto with arith.
   replace (S p0' * S q0 + S p0 * S q0')%nat with (S (q0+p0'*(S q0)+S (q0'+p0*(S q0'))))%nat; auto with arith.
   set (m':=((q0 + p0' * S q0) + S (q0' + p0 * S q0'))%nat).
   set (m:=((q0 + p0' * S q0) - (S q0' + p0 * S q0'))%nat).
   set (n:=(q0 + q0' * S q0)%nat).
   assert (H_m':(S m + S n <= S m' + S n)%nat);
    [ subst m m' n; apply plus_le_compat_r; apply le_n_S; apply le_trans with (q0 + p0' * S q0)%nat; auto with arith;
      apply le_minus |].
   destruct (construct_correct2  (S m'+S n) m n H_m') as [factor [H_factor1 H_factor2]].
   generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
   set (P:=(Qpositive_c  (S m) (S n) (S m' + S n))).
   destruct (interp_non_zero P) as [P0 [Q0 H'']].
   rewrite H''.
   unfold fst, snd. 
   intros H_factor1  H_factor2.
   repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
   rewrite Rplus_Rdiv; auto.
   rewrite <- (Rdiv_Rmult_simplify (INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
   rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
   rewrite <- H_factor1; rewrite <- H_factor2.
   apply Rmult_Rdiv; auto.
   subst m n.
   repeat rewrite S_INR.
   rewrite minus_INR; trivial.
   repeat rewrite plus_INR.
   repeat rewrite mult_INR.
   repeat rewrite S_INR.
   ring.
   (* p<p' *)
   unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
   unfold Qpositive_sub.
   generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_le_dec)).
   generalize (not_Qpositive_le_Qpositive_le' _ _ H_le_dec); 
   clear H_le_dec; intros H_le_dec H_eq_dec.
   generalize (Qpositive_le_to_Qpositive_le' p' p H_le_dec); unfold Qpositive_le'.
   generalize (Qpositive_le_noneq_explicit p' p H_le_dec H_eq_dec).
   destruct (interp_non_zero p) as [p0 [q0 H]].
   destruct (interp_non_zero p') as [p0' [q0' H']].
   rewrite H; rewrite H'; intros H_le_dec_unfolded H_lt.
   assert (H_le_unfold:   (S q0 + p0' * S q0 <= q0' + p0 * S q0')%nat); auto with arith. 
   replace (S p0 * S q0' - S p0' * S q0)%nat with (S (q0'+p0*(S q0')- (S q0+p0'*(S q0))))%nat;
   [| rewrite (minus_Sn_m _ _ H_le_unfold); auto with arith ].
   replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; auto with arith.
   replace (S p0 * S q0' + S p0' * S q0)%nat with (S (q0'+p0*(S q0')+S (q0+p0'*(S q0))))%nat; auto with arith.
   set (m':=((q0' + p0 * S q0') + S (q0 + p0' * S q0))%nat).
   set (m:=((q0' + p0 * S q0') - (S q0 + p0' * S q0))%nat).
   set (n:=(q0' + q0 * S q0')%nat).
   assert (H_m':(S m + S n <= S m' + S n)%nat);
    [ subst m m' n; apply plus_le_compat_r; apply le_n_S; apply le_trans with (q0' + p0 * S q0')%nat; auto with arith;
      apply le_minus |].
   destruct (construct_correct2  (S m'+S n) m n H_m') as [factor [H_factor1 H_factor2]].
   generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
   set (P:=(Qpositive_c  (S m) (S n) (S m' + S n))).
   destruct (interp_non_zero P) as [P0 [Q0 H'']].
   rewrite H''.
   unfold fst, snd. 
   intros H_factor1  H_factor2.
   repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
   rewrite Rplus_Rdiv; auto.
   rewrite <- (Rdiv_Rmult_simplify (-INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
   rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
   rewrite <- H_factor1; rewrite <- H_factor2.
   apply Rmult_Rdiv; auto.
   subst m n.
   repeat rewrite S_INR.
   rewrite minus_INR; trivial.
   repeat rewrite plus_INR.
   repeat rewrite mult_INR.
   repeat rewrite S_INR.
   ring.
  (* -- *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qplus, fst, snd;
  unfold Qpositive_plus.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S q0' + S p0' * S q0)%nat with (S (q0'+p0*(S q0')+S (q0+p0'*(S q0))))%nat; auto with arith.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; auto with arith.
  set (m:=((q0' + p0 * S q0') + S (q0 + p0' * S q0))%nat).
  set (n:=(q0' + q0 * S q0')%nat).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c  (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  rewrite Rplus_Rdiv; auto.
  rewrite <- (Rdiv_Rmult_simplify (-INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite S_INR.
  repeat rewrite mult_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
Qed.

Lemma Q_to_Rmult: forall x y, Q_to_R (Qmult x y) = (Rmult (Q_to_R x) (Q_to_R y)).
Proof.
 intros [ |p|p] [ |p'|p']; try rewrite Q_to_R_Zero; try rewrite Qmult_zero;
 try rewrite Qmult_zero_right; try rewrite Rmult_0_r;
 try rewrite Rmult_0_l; try rewrite Q_to_R_Zero; trivial.
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qmult, fst, snd;
  unfold Qpositive_mult.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S p0')%nat with (S (p0'+p0*(S p0')))%nat; trivial.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; trivial.
  set (m:=((p0' + p0 * S p0')%nat)).
  set (n:=((q0' + q0 * S q0')%nat)).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite <- INR_IZR_INZ.
  rewrite Rdiv_Rmult_numerator_denominator; auto.
  rewrite <- (Rdiv_Rmult_simplify (INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
  (* +- *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qmult, fst, snd;
  unfold Qpositive_mult.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S p0')%nat with (S (p0'+p0*(S p0')))%nat; trivial.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; trivial.
  set (m:=((p0' + p0 * S p0')%nat)).
  set (n:=((q0' + q0 * S q0')%nat)).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  rewrite Rdiv_Rmult_numerator_denominator; auto.
  rewrite <- (Rdiv_Rmult_simplify (- INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
  (* +- *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qmult, fst, snd;
  unfold Qpositive_mult.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S p0')%nat with (S (p0'+p0*(S p0')))%nat; trivial.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; trivial.
  set (m:=((p0' + p0 * S p0')%nat)).
  set (n:=((q0' + q0 * S q0')%nat)).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  rewrite Rdiv_Rmult_numerator_denominator; auto.
  rewrite <- (Rdiv_Rmult_simplify (- INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qmult, fst, snd;
  unfold Qpositive_mult.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  replace (S p0 * S p0')%nat with (S (p0'+p0*(S p0')))%nat; trivial.
  replace (S q0 * S q0')%nat with (S (q0'+q0*(S q0')))%nat; trivial.
  set (m:=((p0' + p0 * S p0')%nat)).
  set (n:=((q0' + q0 * S q0')%nat)).
  destruct (construct_correct2  (S m+S n) m n  (le_n _)) as [factor [H_factor1 H_factor2]].
  generalize H_factor1 H_factor2; clear H_factor1 H_factor2.
  set (P:=(Qpositive_c (S m) (S n) (S m + S n))).
  destruct (interp_non_zero P) as [P0 [Q0 H'']].
  rewrite H''.
  unfold fst, snd. 
  intros H_factor1  H_factor2.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  rewrite Rdiv_Rmult_numerator_denominator; auto.
  rewrite <- (Rdiv_Rmult_simplify (INR (S P0)) (INR (S Q0)) (INR (S factor))); auto.
  rewrite Ropp_mult_distr_l_reverse; do 2 rewrite <- mult_INR.
  rewrite <- H_factor1; rewrite <- H_factor2.
  apply Rmult_Rdiv; auto.
  subst m n.
  repeat rewrite S_INR.
  repeat rewrite plus_INR.
  repeat rewrite mult_INR.
  repeat rewrite S_INR.
  ring.
Qed.

Lemma Q_to_Rinv: forall x, ~(x=Zero) -> Q_to_R (Qinv x) = Rinv (Q_to_R x).
Proof.
 intros [ |p|p] H_zero.
  apply False_ind; auto.
  (* Qpos *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qinv, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite (inv_correct p _ _ H); rewrite H.
  repeat rewrite <- INR_IZR_INZ.
  rewrite Rpower.Rinv_Rdiv; auto.
  (* Qneg *)
  unfold Q_to_R, numerator, denominator, decode_Q, Qinv, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite (inv_correct p _ _ H); rewrite H.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  rewrite Rpower.Rinv_Rdiv; auto.
  unfold Rdiv; rewrite <- Rmult_opp_opp;
  rewrite Ropp_involutive;
  rewrite Ropp_inv_permute; auto.
Qed.


Lemma Q_to_Rminus: forall x y, Q_to_R (Qminus x y) = (Rminus (Q_to_R x) (Q_to_R y)).
Proof.
 intros x y; unfold Qminus; rewrite Q_to_Rplus; rewrite Q_to_Ropp; trivial.
Qed.

Lemma Q_to_Rdiv: forall x y, ~(y=Zero) -> Q_to_R (Qdiv x y) = (Rdiv (Q_to_R x) (Q_to_R y)).
Proof.
 intros x y Hy; unfold Qdiv; rewrite Q_to_Rmult; rewrite Q_to_Rinv; trivial.
Qed.

Lemma not_Qlt:forall x y, ~(Qlt y x) -> (Qle x y).
Proof.
 intros x y.
 destruct (Q_le_lt_dec x y); trivial.
Qed.
 
Lemma Q_to_Rle: forall x y, Qle x y -> Rle (Q_to_R x) (Q_to_R y).
Proof.
 intros [ |p|p] [ |p'|p'] H_Q_le; 
 try solve [ apply Rle_refl
           | apply False_ind; apply (Qlt_irreflexive Zero); apply Qle_lt_trans with (Qneg p'); trivial
           | apply False_ind; apply (Qlt_irreflexive Zero); apply Qlt_le_trans with (Qpos p); trivial
           | apply False_ind; apply (Qlt_irreflexive (Qpos p)); apply Qle_lt_trans with (Qneg p'); trivial
           ].
  (* 0+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  simpl; destruct (interp_non_zero p') as [p0 [q0 H]].
  rewrite H;
  repeat rewrite <- INR_IZR_INZ.
  stepl R0; try field; auto.
  unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto.  
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  generalize (Qpositive_le_to_Qpositive_le' _ _ (Qle_Qpositive_le_pos _ _ H_Q_le)); unfold Qpositive_le'.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'; intro H_Q_le_unfold.
  repeat rewrite <- INR_IZR_INZ.
  apply Rmult_Rdiv_pos_Rle; auto.
  repeat rewrite <- mult_INR.
  apply le_INR; trivial.
  (* -0 *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  simpl; destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H.
  rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Ropp_le_cancel. 
  stepl R0; try field; auto.
  stepr (INR (S p0) / INR (S q0))%R; [|field; auto].
  unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto.  
  (* -+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rle_trans with R0.
   apply Ropp_le_cancel; stepl R0; try field; auto; stepr (INR (S p0) / INR (S q0))%R; [|field; auto]; 
                                               unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto.  
   stepl R0; try field; auto; unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto.  
  (* -- *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  generalize (Qpositive_le_to_Qpositive_le' _ _ (Qle_Qpositive_le_neg _ _ H_Q_le)); unfold Qpositive_le'.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'; intro H_Q_le_unfold.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rmult_Rdiv_pos_Rle; auto.
  apply Ropp_le_cancel.
  stepr (INR (S p0) * INR (S q0'))%R; [|field; auto].
  stepl (INR (S p0') * INR (S q0))%R; [|field; auto].
  repeat rewrite <- mult_INR.
  apply le_INR; trivial.
Qed.

Lemma Q_to_Rlt: forall x y, Qlt x y -> Rlt (Q_to_R x) (Q_to_R y).
Proof.
 intros [ |p|p] [ |p'|p'] H_Q_lt;
 try solve [ apply False_ind; apply (Qlt_irreflexive Zero); trivial
           | apply False_ind; apply (Qlt_irreflexive Zero); apply Qlt_transitive with (Qneg p'); trivial
           | apply False_ind; apply (Qlt_irreflexive Zero); apply Qlt_transitive with (Qpos p); trivial
           | apply False_ind; apply (Qlt_irreflexive (Qpos p)); apply Qlt_transitive with (Qneg p'); trivial
           ].
  (* 0+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  simpl; destruct (interp_non_zero p') as [p0 [q0 H]].
  rewrite H;
  repeat rewrite <- INR_IZR_INZ.
  stepl R0; try field; auto.
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  inversion_clear H_Q_lt as [x y H_not_le| | | | ].
  generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_not_le)).
  generalize (not_Qpositive_le_Qpositive_le' _ _ H_not_le).
  intros H_Q_le H_neq.
  generalize (Qpositive_le_noneq_explicit _ _ H_Q_le H_neq).
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'; intro H_Q_lt_unfold.
  repeat rewrite <- INR_IZR_INZ.
  apply Rmult_Rdiv_pos_Rlt; auto.
  repeat rewrite <- mult_INR.
  apply lt_INR; trivial.
  (* -0 *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  simpl; destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H;
  rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Ropp_lt_cancel. 
  stepl R0; try field; auto.
  stepr (INR (S p0) / INR (S q0))%R; [|field; auto].
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* -+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rlt_trans with R0.
   apply Ropp_lt_cancel; stepl R0; try field; auto; stepr (INR (S p0) / INR (S q0))%R; [|field; auto]; 
                                               unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
   stepl R0; try field; auto; unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* -- *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  inversion_clear H_Q_lt as [ |x y H_not_le| | | ].
  generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_not_le)).
  generalize (not_Qpositive_le_Qpositive_le' _ _ H_not_le).
  intros H_Q_le H_neq.
  generalize (Qpositive_le_noneq_explicit _ _ H_Q_le H_neq).
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'; intro H_Q_lt_unfold.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rmult_Rdiv_pos_Rlt; auto.
  apply Ropp_lt_cancel.
  stepr (INR (S p0) * INR (S q0'))%R; [|field; auto].
  stepl (INR (S p0') * INR (S q0))%R; [|field; auto].
  repeat rewrite <- mult_INR.
  apply lt_INR; trivial.
Qed.

Lemma Q_to_R_not_eq: forall x y, ~(x=y)->~(Q_to_R x = Q_to_R y).
Proof.
 intros [ |p|p] [ |p'|p'] H_not_eq.
  (* 00 *)
  apply False_ind; apply H_not_eq; trivial.
  (* 0+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p') as [p0 [q0 H]].
  rewrite H.
  repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq;
  stepl R0; [|simpl; field];
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* 0- *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p') as [p0 [q0 H]].
  rewrite H.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq'.
  apply Ropp_lt_cancel. 
  stepl R0; [|simpl; field];
  stepr (INR (S p0) / INR (S q0))%R; [|field; auto].
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* 0+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H.
  repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq'.
  stepl R0; [|simpl; field];
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* ++ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (not_Qeq_inf _ _ H_not_eq) as [H_Q_lt|H_Q_lt];
  inversion_clear H_Q_lt as [x y H_not_le| | | | ];
  generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_not_le));
  generalize (not_Qpositive_le_Qpositive_le' _ _ H_not_le); intros H_Q_le H_neq;
  generalize (Qpositive_le_noneq_explicit _ _ H_Q_le H_neq);
  destruct (interp_non_zero p) as [p0 [q0 H]];
  destruct (interp_non_zero p') as [p0' [q0' H']];
  rewrite H; rewrite H'; intro H_Q_lt_unfold;
  [ apply Rlt_not_eq | apply Rlt_not_eq'];
  repeat rewrite <- INR_IZR_INZ; apply Rmult_Rdiv_pos_Rlt; auto; repeat rewrite <- mult_INR; apply lt_INR; trivial.
  (* +- *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq'.
  apply Rlt_trans with R0.
   apply Ropp_lt_cancel;
    stepl R0; try field; auto;
    stepr (INR (S p0') / INR (S q0'))%R; [|field; auto]; unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
   stepl R0; try field; auto; unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* -0 *) 
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  rewrite H.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq.
  apply Ropp_lt_cancel. 
  stepl R0; [|simpl; field];
  stepr (INR (S p0) / INR (S q0))%R; [|field; auto].
  unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* -+ *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (interp_non_zero p) as [p0 [q0 H]].
  destruct (interp_non_zero p') as [p0' [q0' H']].
  rewrite H; rewrite H'.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ.
  apply Rlt_not_eq.
  apply Rlt_trans with R0.
   apply Ropp_lt_cancel;
    stepl R0; try field; auto;
    stepr (INR (S p0) / INR (S q0))%R; [|field; auto]; unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
   stepl R0; try field; auto; unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto.  
  (* -- *)
  unfold Q_to_R, numerator, denominator, decode_Q, fst, snd.
  destruct (not_Qeq_inf _ _ H_not_eq) as [H_Q_lt|H_Q_lt];
  inversion_clear H_Q_lt as [ |x y H_not_le| | | ];
  generalize (sym_not_eq (not_Qpositive_le_not_eq _ _ H_not_le));
  generalize (not_Qpositive_le_Qpositive_le' _ _ H_not_le); intros H_Q_le H_neq;
  generalize (Qpositive_le_noneq_explicit _ _ H_Q_le H_neq);
  destruct (interp_non_zero p) as [p0 [q0 H]];
  destruct (interp_non_zero p') as [p0' [q0' H']];
  rewrite H; rewrite H'; intro H_Q_lt_unfold;
  [ apply Rlt_not_eq | apply Rlt_not_eq'];
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ;
  apply Rmult_Rdiv_pos_Rlt; auto; apply Ropp_lt_cancel. 
    stepr (INR (S p0) * INR (S q0'))%R; [|field; auto];
    stepl (INR (S p0') * INR (S q0))%R; [|field; auto]; repeat rewrite <- mult_INR;
    apply lt_INR; trivial...
    stepr (INR (S p0') * INR (S q0))%R; [|field; auto];
    stepl (INR (S p0) * INR (S q0'))%R; [|field; auto]; repeat rewrite <- mult_INR;
    apply lt_INR; trivial...
Qed.

Lemma Q_to_R_Qle:forall x y : Q, Rle (Q_to_R x) (Q_to_R y) -> Qle x y. 
Proof.
 intros x y H_Rle; destruct (Q_le_lt_dec x y) as [Hxy|Hxy]; trivial; apply False_ind; generalize (Q_to_Rlt _ _ Hxy);
 apply RIneq.Rle_not_lt; assumption.
Qed.

Lemma Q_to_R_Qlt:forall x y : Q, Rlt (Q_to_R x) (Q_to_R y) -> Qlt x y. 
Proof.
 intros x y H_Rlt; destruct (Q_le_lt_dec y x) as [Hxy|Hxy]; trivial;
 apply False_ind; generalize (Q_to_Rle _ _ Hxy); apply RIneq.Rlt_not_le; assumption.
Qed.

Lemma Q_to_R_Qneq:forall x y : Q,  (Q_to_R x)<>(Q_to_R y) ->  x<>y. 
Proof.
  intros x y H_Rneq; contradict H_Rneq; rewrite H_Rneq; trivial.
Qed.

Lemma Q_to_R_Qeq:forall x y : Q,  (Q_to_R x)=(Q_to_R y) ->  x=y. 
Proof.
 intros x y H_Req; destruct (Q_eq_dec x y) as [Hxy|Hxy]; trivial;
 apply False_ind; apply (Q_to_R_not_eq _ _ Hxy); assumption.
Qed.
  
Lemma Z_to_Q_to_R_IZR: forall z, Q_to_R (Z_to_Q z) = IZR z.
Proof.
 intros [|p|p].
  (* 0 *)
  simpl; rewrite <- Q_to_R_Zero; trivial.
  (* + *)
  unfold Z_to_Q, Q_to_R, numerator, denominator, decode_Q, fst, snd.
  rewrite (Qpositive_i_c (nat_of_P p) (S (nat_of_P p)) (lt_O_nat_of_P _)); trivial;
  repeat rewrite <- INR_IZR_INZ; unfold IZR, INR at 2; rewrite <- INR_IPR; field; auto.
  (* - *)
  unfold Z_to_Q, Q_to_R, numerator, denominator, decode_Q, fst, snd.
  rewrite (Qpositive_i_c (nat_of_P p) (S (nat_of_P p)) (lt_O_nat_of_P _)); trivial.
  repeat rewrite Ropp_Ropp_IZR; repeat rewrite <- INR_IZR_INZ; unfold IZR, INR at 2; rewrite <- INR_IPR; field; auto.
Qed.

(** These tactics transfer hypotheses and goals from Q to R *)

Ltac realify_Q_assumptions :=
 repeat 
 match goal with 
 | [ id : (Qlt ?X1 ?X2) |- _ ] => generalize (Q_to_Rlt _ _ id); clear id; try unfold fst, snd
 | [ id : (Qle ?Xe ?X2) |- _ ] => generalize (Q_to_Rle _ _ id); clear id; try unfold fst, snd
 | [ id : (@eq Q ?Xe ?X2) |- _ ] => generalize (Q_to_Req _ _ id); clear id; try unfold fst, snd
 | [ id : ~(@eq Q ?Xe ?X2) |- _ ] => generalize (Q_to_R_not_eq _ _ id); clear id; try unfold fst, snd
 end.

Ltac realify_Q_goal :=   
 match goal with 
 | [ |- context [(Q_to_R (Qplus ?X1 ?X2))] ] => rewrite Q_to_Rplus; realify_Q_goal
 | [ |- context [(Q_to_R (Qminus ?X1 ?X2))] ] => rewrite Q_to_Rminus; realify_Q_goal
 | [ |- context [(Q_to_R (Qmult ?X1 ?X2))] ] => rewrite Q_to_Rmult; realify_Q_goal
 | [ |- context [(Q_to_R (Qdiv ?X1 ?X2))] ] => rewrite Q_to_Rdiv; realify_Q_goal
 | [ |- context [(Q_to_R (Qopp ?X1))] ] => rewrite Q_to_Ropp; realify_Q_goal
 | [ |- context [(Q_to_R (Qinv ?X1))] ] => rewrite Q_to_Rinv; realify_Q_goal
 | [ |- context [(Q_to_R Zero)] ] => rewrite Q_to_R_Zero; realify_Q_goal
 | [ |- context [(Q_to_R Qone)] ] => rewrite Q_to_R_Qone; realify_Q_goal
 | [ |- context [(Q_to_R (Qneg One))] ] => rewrite Q_to_R_Qneg_One; realify_Q_goal
 | [ |- context [(Q_to_R (Z_to_Q ?X1))] ] => rewrite Z_to_Q_to_R_IZR; realify_Q_goal
 | [ |- _ ] => idtac
 end.

Ltac realify_Q := try realify_Q_assumptions; realify_Q_goal.

Ltac rationalify_R_goal :=   
 match goal with 
 | [ |- context [(Rplus (Q_to_R ?X1) (Q_to_R ?X2))] ] => rewrite <- Q_to_Rplus; rationalify_R_goal
 | [ |- context [(Rminus (Q_to_R ?X1) (Q_to_R ?X2))] ] => rewrite <- Q_to_Rminus; rationalify_R_goal
 | [ |- context [(Rmult (Q_to_R ?X1) (Q_to_R ?X2))] ] => rewrite <- Q_to_Rmult; rationalify_R_goal
 | [ |- context [(Rdiv (Q_to_R ?X1) (Q_to_R ?X2))] ] => rewrite <- Q_to_Rdiv; auto; rationalify_R_goal
 | [ |- context [(Ropp (Q_to_R ?X1)) ]] => rewrite <- Q_to_Ropp; rationalify_R_goal
 | [ |- context [(Rinv (Q_to_R ?X1))] ] => rewrite <- Q_to_Rinv; auto; rationalify_R_goal
 | [ |- context [R0] ] => rewrite <- Q_to_R_Zero; rationalify_R_goal
 | [ |- context [R1] ] => rewrite <- Q_to_R_Qone; rationalify_R_goal
 | [ |- context [(IZR ?X1)] ] => rewrite <- Z_to_Q_to_R_IZR; realify_Q_goal
 | [ |- _ ] => idtac
 end.

Ltac rationalify_R := rationalify_R_goal;
 match goal with 
 | [ |- Rlt (Q_to_R ?X1) (Q_to_R ?X2)] => apply Q_to_Rlt
 | [ |- Rle (Q_to_R ?X1) (Q_to_R ?X2)] => apply Q_to_Rle
 | [ |- @eq Q (Q_to_R ?X1) (Q_to_R ?X2)] => apply (f_equal Q_to_R)
 | [ |- ~(@eq Q (Q_to_R ?X1) (Q_to_R ?X2))] => apply Q_to_R_not_eq
 | [ |- ~(@eq Q ?X1 Zero)] => idtac
 | [ |- _ ] => fail 1
 end.
