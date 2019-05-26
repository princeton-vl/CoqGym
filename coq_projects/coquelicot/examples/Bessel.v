(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive Series PSeries Lim_seq.
Require Import AutoDerive.

(** This file is an example of how to use power series. It defines and
gives properties of the Bessel functions. *)

Definition Bessel1_seq (n k : nat) :=
  (-1)^(k)/(INR (fact (k)) * INR (fact (n + (k)))).

Lemma Bessel1_seq_neq_0 (n : nat) :
  forall k, Bessel1_seq n k <> 0.
Proof.
  move => k.
  apply Rmult_integral_contrapositive_currified.
  apply pow_nonzero, Ropp_neq_0_compat, R1_neq_R0.
  apply Rinv_neq_0_compat, Rmult_integral_contrapositive_currified ;
  apply INR_fact_neq_0.
Qed.

Lemma CV_Bessel1 (n : nat) :
  CV_radius (Bessel1_seq n) = p_infty.
Proof.
  apply CV_radius_infinite_DAlembert.
    by apply Bessel1_seq_neq_0.
  apply is_lim_seq_ext with (fun p => / (INR (S p) * INR (S (n + p)))).
  move => p ; rewrite /Bessel1_seq -plus_n_Sm /fact -/fact !mult_INR.
  simpl ((-1)^(S p)).
  field_simplify (-1 * (-1) ^ p /
    (INR (S p) * INR (fact p) * (INR (S (n + p)) * INR (fact (n + p)))) /
    ((-1) ^ p / (INR (fact p) * INR (fact (n + p))))).
  rewrite Rabs_div.
  rewrite Rabs_Ropp Rabs_R1 /Rdiv Rmult_1_l Rabs_pos_eq.
  by [].
  apply Rmult_le_pos ; apply pos_INR.
  apply Rgt_not_eq, Rmult_lt_0_compat ;
  apply lt_0_INR, lt_O_Sn.
  repeat split.
  by apply INR_fact_neq_0.
  by apply INR_fact_neq_0.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply pow_nonzero, Rlt_not_eq, (IZR_lt (-1) 0).
  replace (Finite 0) with (Rbar_inv p_infty) by auto.
  apply is_lim_seq_inv.
  eapply is_lim_seq_mult.
  apply -> is_lim_seq_incr_1.
  by apply is_lim_seq_INR.
  apply is_lim_seq_ext with (fun k => INR (k + S n)).
  intros k.
  by rewrite (Plus.plus_comm n k) plus_n_Sm.
  apply is_lim_seq_incr_n.
  by apply is_lim_seq_INR.
  by [].
  by [].
Qed.

Lemma ex_Bessel1 (n : nat) (x : R) :
  ex_pseries (Bessel1_seq n) x.
Proof.
  apply CV_radius_inside.
  by rewrite CV_Bessel1.
Qed.

Definition Bessel1 (n : nat) (x : R) :=
  (x/2)^n * PSeries (Bessel1_seq n) ((x/2)^2).

Lemma is_derive_Bessel1 (n : nat) (x : R) :
  is_derive (Bessel1 n) x
      ((x / 2) ^ S n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2)
      + (INR n)/2 * (x / 2) ^ pred n * PSeries (Bessel1_seq n) ((x / 2) ^ 2)).
Proof.
  rewrite /Bessel1.
  auto_derive.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  rewrite Derive_PSeries.
  rewrite /Rdiv ; simpl ; field.
  by rewrite CV_Bessel1.
Qed.

Lemma is_derive_2_Bessel1 (n : nat) (x : R) :
  is_derive_n (Bessel1 n) 2 x
    (((x/2)^(S (S n)) * PSeries (PS_derive (PS_derive (Bessel1_seq n))) ((x / 2) ^ 2))
    + ((INR (2*n+1)/2) * (x/2)^n * PSeries (PS_derive (Bessel1_seq n)) ((x / 2) ^ 2))
    + (INR (n * pred n) / 4 * (x / 2) ^ pred (pred n) * PSeries (Bessel1_seq n) ((x / 2) ^ 2))).
Proof.
  rewrite plus_INR ?mult_INR ; simpl INR.
  eapply is_derive_ext.
  move => y ;
  by apply sym_eq, is_derive_unique, is_derive_Bessel1.
  auto_derive.
  repeat split.
  apply ex_derive_PSeries.
  by rewrite CV_radius_derive CV_Bessel1.
  apply ex_derive_PSeries.
  by rewrite CV_Bessel1.
  rewrite !Derive_PSeries.
  case: n => [ | n] ; rewrite ?S_INR /Rdiv /= ;
  field.
  by rewrite CV_Bessel1.
  by rewrite CV_radius_derive CV_Bessel1.
Qed.

Lemma Bessel1_correct (n : nat) (x : R) :
  x^2 * Derive_n (Bessel1 n) 2 x + x * Derive (Bessel1 n) x + (x^2 - (INR n)^2) * Bessel1 n x = 0.
Proof.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) ;
  rewrite /Derive_n (is_derive_unique _ _ _ (is_derive_2_Bessel1 _ _)) ;
  rewrite /Bessel1 plus_INR ?mult_INR ; simpl INR.
  set y := x/2 ; replace x with (2 * y) by (unfold y ; field).

  replace (_ + _)
  with (4 * y^S (S n) * (y^2 * PSeries (PS_derive (PS_derive (Bessel1_seq n))) (y ^ 2)
    + (INR n + 1) * PSeries (PS_derive (Bessel1_seq n)) (y ^ 2)
    + PSeries (Bessel1_seq n) (y ^ 2))).
  Focus 2.
  case: n => [|[|n]] ; rewrite ?S_INR /= ; field.

  apply Rmult_eq_0_compat_l.

  rewrite -PSeries_incr_1 -PSeries_scal -?PSeries_plus.

  unfold PS_derive, PS_incr_1, PS_scal, PS_plus.
  rewrite -(PSeries_const_0 (y^2)).
  apply PSeries_ext.
  case => [ | p] ; rewrite /Bessel1_seq ;
  rewrite -?plus_n_Sm ?plus_0_r /fact -/fact ?mult_INR ?S_INR ?plus_INR ; simpl INR ; simpl pow ;
  rewrite ?Rplus_0_l ?Rmult_1_l.
  rewrite /plus /zero /scal /= /mult /=.
  field.
  split ; rewrite -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  rewrite /plus /scal /= /mult /=.
  field.
  repeat split ; rewrite -?plus_INR -?S_INR ; apply Rgt_not_eq.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply INR_fact_lt_0.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.
  by apply (lt_INR 0), lt_O_Sn.

  apply CV_radius_inside.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  apply Rbar_min_case.
  by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
  rewrite CV_radius_scal.
  by rewrite CV_radius_derive CV_Bessel1.
  now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
  by apply ex_Bessel1.
  apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
  by rewrite CV_radius_incr_1 ?CV_radius_derive CV_Bessel1.
  apply ex_pseries_R, ex_series_Rabs, CV_disk_inside.
  rewrite CV_radius_scal.
  by rewrite CV_radius_derive CV_Bessel1.
  now rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
Qed.

Lemma Bessel1_equality_1 (n : nat) (x : R) : x <> 0
  -> Bessel1 (S n)%nat x = INR n * Bessel1 n x / x - Derive (Bessel1 n) x.
Proof.
  move => Hx.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
  set y := (x / 2).
  replace x with (2 * y) by (unfold y ; field).

(* Supprimer les PSeries *)
  have Hy : y <> 0.
  unfold y ; contradict Hx.
  replace x with (2 * (x/2)) by field ; rewrite Hx ; ring.
  case: n => [ | n] ; simpl ; field_simplify => // ; rewrite Rdiv_1 -/(pow _ 2).
(* * cas n = 0 *)
  replace (- 2 * y ^ 2 * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2) / (2 * y))
    with (y * ((-1) * PSeries (PS_derive (Bessel1_seq 0)) (y ^ 2)))
    by (simpl ; unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive plus_0_l.
  replace (1+k)%nat with (S k) by ring.
  rewrite /fact -/fact mult_INR /pow -/pow.
  change scal with Rmult.
  field ; split.
  exact: INR_fact_neq_0.
  by apply not_0_INR, not_eq_sym, O_S.
(* * cas S n *)
  replace (-2 * y ^ 2 * y ^ n * PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2) / 2)
    with (y^2 * y^n * (((-1)* PSeries (PS_derive (Bessel1_seq (S n))) (y ^ 2))))
    by (unfold y ; field => //).
  apply f_equal.
  rewrite -PSeries_scal.
  apply PSeries_ext => k.
  rewrite /Bessel1_seq /PS_scal /PS_derive -?plus_n_Sm ?plus_Sn_m.
  rewrite /pow -/pow /fact -/fact ?mult_INR ?S_INR plus_INR.
  change scal with Rmult.
  field.
  rewrite -plus_INR -?S_INR.
  repeat split ;
  try by [exact: INR_fact_neq_0 | apply not_0_INR, not_eq_sym, O_S].
Qed.

Lemma Bessel1_equality_2 (n : nat) (x : R) : (0 < n)%nat -> x<>0
  -> Bessel1 (S n)%nat x + Bessel1 (pred n)%nat x = (2*INR n)/x * Bessel1 n x.
Proof.
  case: n => [ | n] Hn Hx.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl pred.
  rewrite /Bessel1 S_INR.
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))
    with ((x/2)^n *
      ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) +
      PSeries (Bessel1_seq n) ((x / 2) ^ 2)))
    by (simpl ; ring).
  replace (2 * (INR n + 1) / x *
      ((x / 2) ^ S n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    with ((x/2)^n * ((INR n + 1) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    by (simpl ; field ; exact: Hx).
  apply f_equal.
  rewrite -PSeries_incr_1 -PSeries_scal -PSeries_plus.
Focus 2. (* ex_pseries (PS_incr_1 (Bessel1_seq (S (S n))) (S (S n))) ((x / 2) ^ 2) *)
  by apply ex_pseries_incr_1, ex_Bessel1.
Focus 2. (* ex_pseries (PS_incr_n (Bessel1_seq n) n) ((x / 2) ^ 2) *)
  by apply ex_Bessel1.
  apply PSeries_ext => k.
(* egalité *)
  rewrite /PS_plus /PS_scal /PS_incr_1 /Bessel1_seq ;
  case: k => [ | k] ;
  rewrite ?plus_0_r -?plus_n_Sm ?plus_Sn_m
    /fact -/fact ?mult_INR ?S_INR ?plus_INR /=.
  rewrite plus_zero_l /scal /= /mult /=.
  field.
  rewrite -S_INR ; split ;
  by [apply not_0_INR, sym_not_eq, O_S | apply INR_fact_neq_0].
  rewrite /plus /scal /= /mult /=.
  field ;
  rewrite -?plus_INR -?S_INR ; repeat split ;
  by [apply INR_fact_neq_0 | apply not_0_INR, sym_not_eq, O_S].
Qed.

Lemma Bessel1_equality_3 (n : nat) (x : R) : (0 < n)%nat ->
  Bessel1 (S n)%nat x - Bessel1 (pred n)%nat x = - 2 * Derive (Bessel1 n) x.
Proof.
  move => Hn.
  rewrite (is_derive_unique _ _ _ (is_derive_Bessel1 _ _)) /Bessel1.
  case: n Hn => [ | n] Hn.
  by apply lt_irrefl in Hn.
  clear Hn ; simpl pred.
  replace ((x / 2) ^ S (S n) * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) -
      (x / 2) ^ n * PSeries (Bessel1_seq n) ((x / 2) ^ 2))
    with ((x/2)^n *
      ((x/2)^2 * PSeries (Bessel1_seq (S (S n))) ((x / 2) ^ 2) -
      PSeries (Bessel1_seq n) ((x / 2) ^ 2)))
    by (simpl ; ring).
  replace (-2 *((x / 2) ^ S (S n) * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2) +
      INR (S n) / 2 * (x / 2) ^ n * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    with ((x/2)^n * (-2 * ((x/2)^2  * PSeries (PS_derive (Bessel1_seq (S n))) ((x / 2) ^ 2)) -
      INR (S n) * PSeries (Bessel1_seq (S n)) ((x / 2) ^ 2)))
    by (rewrite S_INR ; simpl ; field).
  set y := (x / 2).
  apply f_equal.
  rewrite -?PSeries_incr_1 -?PSeries_scal -?PSeries_minus.
  apply PSeries_ext => k.
  rewrite  /PS_minus /PS_incr_1 /PS_scal /PS_derive /Bessel1_seq.
  case: k => [ | k] ; rewrite -?plus_n_Sm ?plus_Sn_m /fact -/fact ?mult_INR ?S_INR -?plus_n_O ?plus_INR /= ;
  rewrite /plus /opp /zero /scal /= /mult /= ;
  field ; rewrite -?plus_INR -?S_INR.
  split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
  repeat split ; (apply INR_fact_neq_0 || apply not_0_INR, sym_not_eq, O_S).
  apply @ex_pseries_scal, @ex_pseries_incr_1, ex_pseries_derive.
  by apply Rmult_comm.
  by rewrite CV_Bessel1.
  apply ex_pseries_scal, ex_Bessel1.
  by apply Rmult_comm.
  by apply ex_pseries_incr_1, ex_Bessel1.
  by apply ex_Bessel1.
Qed.

(** * Unicity *)

Lemma Bessel1_uniqueness_aux_0 (a : nat -> R) (n : nat) :
  Rbar_lt 0 (CV_radius a) ->
  (forall x : R, Rbar_lt (Rabs x) (CV_radius a) -> x^2 * Derive_n (PSeries a) 2 x + x * Derive (PSeries a) x + (x^2 - (INR n)^2) * PSeries a x = 0)
  ->
  (a 0%nat = 0 \/ n = O) /\
  (a 1%nat = 0 \/ n = 1%nat) /\
  (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0).
Proof.
  move => Ha H.
  cut (forall k,
    (PS_plus (PS_plus (PS_incr_n (PS_derive_n 2 a) 2)
      (PS_incr_1 (PS_derive a))) (PS_plus (PS_incr_n a 2) (PS_scal (- INR n ^ 2) a))) k = 0).
  intros Haux.
  split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
(* n = 0 *)
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive in Haux.
  rewrite /plus /zero /scal /= /mult /= in Haux.
  ring_simplify in Haux.
  apply Rmult_integral in Haux ; case: Haux => Haux.
  right.
  suff : ~ n <> 0%nat.
  by intuition.
  contradict Haux.
  apply Ropp_neq_0_compat.
  apply pow_nonzero.
  by apply not_0_INR.
  by left.
  split ; [move: (Haux 0%nat) | move: (fun k => Haux (S k))] => {Haux} Haux.
(* n = 1 *)
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive /= in Haux.
  rewrite /plus /zero /scal /= /mult /= in Haux.
  ring_simplify in Haux.
  replace (- a 1%nat * INR n ^ 2 + a 1%nat) with ((1 - INR n ^ 2) * a 1%nat) in Haux.
  apply Rmult_integral in Haux ; case: Haux => Haux.
  right.
  suff : ~ n <> 1%nat.
  by intuition.
  contradict Haux.
  replace (1 - INR n ^ 2) with ((1-INR n) * (1 + INR n)) by ring.
  apply Rmult_integral_contrapositive_currified.
  apply Rminus_eq_contra.
  apply sym_not_eq.
  by apply not_1_INR.
  apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
  apply Rminus_le_0 ; ring_simplify.
  by apply pos_INR.
  by left.
  ring.
(* n >= 2 *)
  move => k ; rewrite ?S_INR /= ;
  move: (Haux k) ;
  rewrite /PS_plus /= /PS_incr_1 /PS_derive_n /PS_scal /PS_derive -?S_INR.
  replace (k + 2)%nat with (S (S k)) by ring.
  rewrite /fact -/fact ?mult_INR ?S_INR => {Haux} Haux.
  rewrite /plus /scal /= /mult /= in Haux.
  field_simplify in Haux.
  field_simplify.
  by rewrite (Rmult_comm (INR n ^ 2)).
  move: Haux.
  by apply INR_fact_neq_0.

  move => k.
  apply (PSeries_ext_recip _ (fun _ => 0)).
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  apply Rbar_min_case.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  apply Rbar_min_case.
  rewrite /PS_incr_n ?CV_radius_incr_1.
  by rewrite CV_radius_derive_n.
  rewrite CV_radius_incr_1.
  by rewrite CV_radius_derive.
  apply Rbar_lt_le_trans with (2 := CV_radius_plus _ _).
  apply Rbar_min_case.
  by rewrite /PS_incr_n ?CV_radius_incr_1.
  destruct n.
  rewrite -(CV_radius_ext (fun _ => 0)) ?CV_radius_const_0.
  by [].
  intros n ; rewrite /PS_scal /= /scal /= /mult /= ; ring.
  rewrite CV_radius_scal ?Ha //.
  apply Ropp_neq_0_compat, pow_nonzero, not_0_INR, sym_not_eq, O_S.
  by rewrite CV_radius_const_0.
  assert (0 < Rbar_min 1 (CV_radius a)).
    destruct (CV_radius a) as [ca | | ] ; try by auto.
    apply Rbar_min_case => //.
    by apply Rlt_0_1.
    apply Rbar_min_case_strong => // _.
    by apply Rlt_0_1.
  exists (mkposreal _ H0) => x Hx.
  assert (Rbar_lt (Rabs x) (CV_radius a)).
    destruct (CV_radius a) as [ca | | ] ; try by auto.
    simpl.
    eapply Rlt_le_trans.
    rewrite -(Rminus_0_r x).
    by apply Hx.
    simpl.
    apply Rmin_case_strong => // H1.
    by apply Req_le.

  rewrite PSeries_const_0 ?PSeries_plus.
  rewrite ?PSeries_incr_n PSeries_incr_1 PSeries_scal -Derive_n_PSeries.
  rewrite -Derive_PSeries.
  rewrite -Rmult_plus_distr_r.
  apply H.

  by apply H1.
  by apply H1.
  by apply H1.
  apply ex_pseries_incr_n, CV_radius_inside, H1.
  apply ex_pseries_scal, CV_radius_inside.
  by apply Rmult_comm.
  by apply H1.
  apply ex_pseries_incr_n.
  apply CV_radius_inside.
  rewrite CV_radius_derive_n.
  by apply H1.
  apply ex_pseries_incr_1, ex_pseries_derive.
  by apply H1.
  apply ex_pseries_plus.
  apply ex_pseries_incr_n.
  apply CV_radius_inside.
  by rewrite CV_radius_derive_n ; apply H1.
  apply ex_pseries_incr_1, ex_pseries_derive.
  by apply H1.
  apply ex_pseries_plus.
  apply ex_pseries_incr_n.
  apply CV_radius_inside.
  by apply H1.
  apply ex_pseries_scal.
  by apply Rmult_comm.
  apply CV_radius_inside ; by apply H1.
Qed.

Lemma Bessel1_uniqueness_aux_1 (a : nat -> R) (n : nat) :
  (a 0%nat = 0 \/ n = O) ->
  (a 1%nat = 0 \/ n = 1%nat) ->
  (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0) ->
  (forall k : nat, (k < n)%nat -> a k = 0)
  /\ (forall p : nat, a (n + 2 * p + 1)%nat = 0)
  /\ (forall p : nat, a (n + 2 * p)%nat = Bessel1_seq n p * / 2 ^ (2 * p) * INR (fact n) * a n).
Proof.
  intros Ha0 Ha1 Ha.
  assert (forall k, S (S k) <> n -> a (S (S k)) = - a k / (INR (S (S k)) ^ 2 - INR n ^ 2)).
    intros k Hk.
    replace (a k) with (- (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k))).
    field.
    replace (INR (S (S k)) ^ 2 - INR n ^ 2)
    with ((INR (S (S k)) - INR n) * (INR (S (S k)) + INR n))
    by ring.
    apply Rmult_integral_contrapositive_currified.
    apply Rminus_eq_contra.
    by apply not_INR.
    rewrite -plus_INR plus_Sn_m.
    by apply (not_INR _ O), sym_not_eq, O_S.
    replace (a k)
    with ((INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k - (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)))
    by ring.
    rewrite Ha ; ring.
  assert (forall k : nat, (k < n)%nat -> a k = 0).
    destruct n => k Hk.
    by apply lt_n_O in Hk.
    case: Ha0 => // Ha0.
    destruct n.
    destruct k => //.
    by apply lt_S_n, lt_n_O in Hk.
    case: Ha1 => // Ha1.
    move: k Hk.
    apply (Div2.ind_0_1_SS (fun k => (k < S (S n))%nat -> a k = 0)) => // k IH Hk.
    rewrite H.
    rewrite IH /Rdiv.
    ring.
    eapply lt_trans, Hk.
    eapply lt_trans ; apply lt_n_Sn.
    by apply MyNat.lt_neq.
  repeat split.
  by [].
  elim => [ | p IH].
  replace (n + 2 * 0 + 1)%nat with (S n) by ring.
  destruct n => //=.
  case: Ha1 => // Ha1.
  case: Ha0 => // Ha0.
  rewrite H ; try by intuition.
  rewrite H0 /Rdiv.
  ring.
  by apply lt_n_Sn.
  replace (n + 2 * S p + 1)%nat with (S (S (n + 2 * p + 1)%nat)) by ring.
  rewrite H ; try by intuition.
  rewrite IH /Rdiv.
  ring.
  elim => [ | p IH].
  replace (n + 2 * 0)%nat with (n) by ring.
  rewrite /Bessel1_seq /= -plus_n_O.
  field ; by apply INR_fact_neq_0.
  replace (n + 2 * S p)%nat with (S (S (n + 2 * p)%nat)) by ring.
  rewrite H ; try by intuition.
  rewrite IH /Rdiv.
  rewrite /Bessel1_seq -plus_n_Sm.
  rewrite !pow_sqr /fact -/fact !mult_INR !S_INR !plus_INR /=.
  field ; rewrite -!plus_INR -!S_INR ;
  repeat split ;
  try (by apply INR_fact_neq_0) ;
  try (by apply (not_INR _ 0), sym_not_eq, O_S).
  apply pow_nonzero, Rgt_not_eq ; apply Rmult_lt_0_compat ; by apply Rlt_0_2.
  rewrite -Rsqr_plus_minus.
  apply Rmult_integral_contrapositive_currified.
  rewrite -plus_INR.
  apply Rgt_not_eq, lt_0_INR.
  lia.
  apply Rminus_eq_contra, not_INR.
  lia.
Qed.

Lemma Bessel1_uniqueness (a : nat -> R) (n : nat) :
  (Rbar_lt 0 (CV_radius a)) ->
  (forall x : R, x^2 * Derive_n (PSeries a) 2 x + x * Derive (PSeries a) x + (x^2 - (INR n)^2) * PSeries a x = 0)
  -> {b : R | forall x, PSeries a x = b * Bessel1 n x}.
Proof.
  intros Hcv_a Ha.
  assert ((a 0%nat = 0 \/ n = O) /\
    (a 1%nat = 0 \/ n = 1%nat) /\
    (forall k, (INR (S (S k)) ^ 2 - INR n ^ 2) * a (S (S k)) + a k = 0)).
  by apply Bessel1_uniqueness_aux_0.
  assert ((forall k : nat, (k < n)%nat -> a k = 0)
  /\ (forall p : nat, a (n + 2 * p + 1)%nat = 0)
  /\ (forall p : nat, a (n + 2 * p)%nat = Bessel1_seq n p * / 2 ^ (2 * p) * INR (fact n) * a n)).
  apply Bessel1_uniqueness_aux_1 ; by apply H.
  exists (2^n * INR (fact n) * a n) => x.
  rewrite /Bessel1 (PSeries_decr_n_aux _ n).
  case: H0 => _ H0.
  rewrite Rpow_mult_distr -Rinv_pow.
  field_simplify ; rewrite ?Rdiv_1.
  rewrite !(Rmult_assoc (x ^ n)).
  apply Rmult_eq_compat_l.
  rewrite PSeries_odd_even.
  replace (PSeries (fun n0 : nat => PS_decr_n a n (2 * n0 + 1)) (x ^ 2))
  with 0.
  case: H0 => _ H0.
  rewrite Rmult_0_r Rplus_0_r.
  rewrite -PSeries_scal.
  apply Series_ext => k.
  rewrite /PS_decr_n /PS_scal.
  rewrite H0.
  rewrite -!pow_mult.
  rewrite Rpow_mult_distr -Rinv_pow.
  rewrite /scal /= /mult /=.
  ring.
  by apply Rgt_not_eq, Rlt_0_2.
  apply sym_eq.
  rewrite -(PSeries_const_0 (x^2)).
  apply PSeries_ext => k.
  rewrite /PS_decr_n.
  replace (n + (2 * k + 1))%nat with (n + 2 * k + 1)%nat by ring.
  by apply H0.
  eapply ex_pseries_ext.
  move => p ;
  apply sym_eq.
  apply H0.
  eapply ex_pseries_ext.
  intros p ; rewrite Rmult_assoc ; apply Rmult_comm.
  apply @ex_pseries_scal.
  by apply Rmult_comm.
  case: (Req_dec x 0) => Hx0.
  rewrite Hx0.
  rewrite /= Rmult_0_l.
  by apply @ex_pseries_0.
  apply ex_series_Rabs.
  apply ex_series_DAlembert with 0.
  by apply Rlt_0_1.
  intros p.
  apply Rmult_integral_contrapositive_currified.
  rewrite pow_n_pow.
  by apply pow_nonzero, pow_nonzero.
  apply Rmult_integral_contrapositive_currified.
  by apply Bessel1_seq_neq_0.
  apply Rinv_neq_0_compat.
  apply pow_nonzero.
  by apply Rgt_not_eq, Rlt_0_2.
  apply is_lim_seq_ext with (fun p => x^2 / 4 * / (INR (S p) * INR (S (n + p)))).
  intros p ; rewrite !pow_n_pow !pow_mult.
  rewrite /Bessel1_seq -plus_n_Sm /fact -/fact !mult_INR.
  replace (@scal R_AbsRing R_NormedModule) with Rmult by auto.
  simpl (_^(S p)) ; rewrite -!/(pow _ 2) ; ring_simplify (2^2).
  field_simplify (x ^ 2 * (x ^ 2) ^ p *
   (-1 * (-1) ^ p /
    (INR (S p) * INR (fact p) * (INR (S (n + p)) * INR (fact (n + p)))) *
    / (4 * 4 ^ p)) /
   ((x ^ 2) ^ p * ((-1) ^ p / (INR (fact p) * INR (fact (n + p))) * / 4 ^ p))).
  rewrite Rabs_div.
  rewrite Rabs_Ropp /Rdiv !Rabs_pos_eq.
  field.
  split ; apply (not_INR _ 0), sym_not_eq, O_S.
  change 4 with (INR 2 * INR 2).
  repeat apply Rmult_le_pos ; apply pos_INR.
  by apply pow2_ge_0.
  change 4 with (INR 2 * INR 2).
  apply Rgt_not_eq ; repeat apply Rmult_lt_0_compat ;
  apply lt_0_INR, lt_O_Sn.
  repeat split.
  apply pow_nonzero, Rgt_not_eq ; repeat apply Rmult_lt_0_compat ; apply Rlt_0_2.
  by apply INR_fact_neq_0.
  by apply INR_fact_neq_0.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply Rgt_not_eq, lt_0_INR, lt_O_Sn.
  by apply pow_nonzero, Rlt_not_eq, (IZR_lt (-1) 0).
  rewrite -pow_mult ; by apply pow_nonzero.
  evar_last.
  apply is_lim_seq_scal_l.
  apply is_lim_seq_inv.
  eapply is_lim_seq_mult.
  apply -> is_lim_seq_incr_1.
  by apply is_lim_seq_INR.
  apply is_lim_seq_ext with (fun k => INR (k + S n)).
  intros k.
  by rewrite (Plus.plus_comm n k) plus_n_Sm.
  apply is_lim_seq_incr_n.
  by apply is_lim_seq_INR.
  by [].
  by [].
  simpl ; apply f_equal ; ring.
  apply ex_pseries_ext with (fun  _ => 0).
  intros k.
  rewrite /PS_decr_n /=.
  replace (n + (k + (k + 0) + 1))%nat with (n + 2 * k + 1)%nat by ring.
  by rewrite (proj1 H0).
  eapply ex_series_ext.
  intros k.
  rewrite /scal /= /mult /= Rmult_0_r.
  reflexivity.
  exists 0 ; apply filterlim_ext with (fun _ => 0).
  elim => /= [ | k IH].
  by rewrite sum_O.
  by rewrite sum_Sn plus_zero_r.
  by apply filterlim_const.
  by apply pow_nonzero, Rgt_not_eq, Rlt_0_2.
  by apply Rgt_not_eq, Rlt_0_2.
  by apply H0.
Qed.
