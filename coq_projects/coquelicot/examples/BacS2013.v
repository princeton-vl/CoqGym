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



Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.
Require Import Rcomplements Rbar Hierarchy.
Require Import Derive RInt Continuity Lim_seq ElemFct RInt_analysis.

(** This file describes an experiment: most 18-year old French
students pass an exam called Baccalaureate which ends the high school
and is required for attending the university. We took the 2013
mathematics test of the scientific Baccalaureate at the same time as
the students. The pdf of the test is available #<a href="https://www.lri.fr/~lelay/Bac2013/Bac_S_2013_Metropole.pdf">here</a>#. *)


Ltac pos_rat :=
  repeat ( apply Rdiv_lt_0_compat
         || apply Rplus_lt_0_compat
         || apply Rmult_lt_0_compat) ;
  try by apply Rlt_0_1.

Lemma sign_0_lt : forall x, 0 < x <-> 0 < sign x.
Proof.
intros x.
unfold sign.
destruct total_order_T as [[H|H]|H] ; lra.
Qed.

Lemma sign_lt_0 : forall x, x < 0 <-> sign x < 0.
Proof.
intros x.
unfold sign.
destruct total_order_T as [[H|H]|H] ; lra.
Qed.

(** * Exercice 2 *)
(* 8:14 *)

Definition fab (a b x : R) : R := (a + b * ln x) / x.

(** ** Questions 1 *)

(** 1.a. On voit sur le graphique que l'image de 1 par f correspond au point B(1,2). On a donc f(1) = 2.
Comme la tangente (BC) à la courbe en ce point admet pour coefficient directeur 0, f'(1) = 0 *)

(** 1.b *)

Lemma Dfab (a b : R) : forall x, 0 < x
  -> is_derive (fab a b) x (((b - a) - b * ln x) / x ^ 2).
Proof.
  move => x Hx.
  evar_last.
  apply is_derive_div.
  apply @is_derive_plus.
  apply is_derive_const.
  apply is_derive_scal.
  now apply is_derive_Reals, derivable_pt_lim_ln.
  apply is_derive_id.
  by apply Rgt_not_eq.
  rewrite /Rdiv /plus /zero /one /=.
  field.
  by apply Rgt_not_eq.
Qed.

(** 1.c *)

Lemma Val_a_b (a b : R) : fab a b 1 = 2 -> Derive (fab a b) 1 = 0 -> a = 2 /\ b = 2.
Proof.
  move => Hf Hdf.
  rewrite /fab in Hf.
  rewrite ln_1 in Hf.
  rewrite Rdiv_1 in Hf.
  rewrite Rmult_0_r in Hf.
  rewrite Rplus_0_r in Hf.
  rewrite Hf in Hdf |- * => {a Hf}.
  split.
  reflexivity.
  replace (Derive (fab 2 b) 1) with (((b - 2) - b * ln 1) / 1 ^ 2) in Hdf.
  rewrite ln_1 /= in Hdf.
  field_simplify in Hdf.
  rewrite !Rdiv_1 in Hdf.
  by apply Rminus_diag_uniq.
  apply sym_eq, is_derive_unique.
  apply Dfab.
  by apply Rlt_0_1.
Qed.

Definition f (x : R) : R := fab 2 2 x.

(** ** Questions 2 *)
(* 8:38 *)
(** 2.a. *)

Lemma Signe_df : forall x, 0 < x -> sign (Derive f x) = sign (- ln x).
Proof.
  move => x Hx.
  rewrite (is_derive_unique f x _ (Dfab 2 2 x Hx)).
  replace ((2 - 2 - 2 * ln x) / x ^ 2) with (2 / x ^ 2 * (- ln x)) by (field ; now apply Rgt_not_eq).
  rewrite sign_mult sign_eq_1.
  apply Rmult_1_l.
  apply Rdiv_lt_0_compat.
  apply Rlt_0_2.
  apply pow2_gt_0.
  by apply Rgt_not_eq.
Qed.

(** 2.b. *)

Lemma filterlim_f_0 :
  filterlim f (at_right 0) (Rbar_locally m_infty).
Proof.
  unfold f, fab.
  eapply (filterlim_comp_2 _ _ Rmult).
  eapply filterlim_comp_2.
  apply filterlim_const.
  eapply filterlim_comp_2.
  apply filterlim_const.
  by apply is_lim_ln_0.
  apply (filterlim_Rbar_mult 2 m_infty m_infty).
  unfold is_Rbar_mult, Rbar_mult'.
  case: Rle_dec (Rlt_le _ _ Rlt_0_2) => // H _ ;
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ Rlt_0_2) => //.
  apply (filterlim_Rbar_plus 2 _ m_infty).
  by [].
  by apply filterlim_Rinv_0_right.
  by apply (filterlim_Rbar_mult m_infty p_infty).
Qed.

Lemma Lim_f_p_infty : is_lim f p_infty 0.
Proof.
  apply is_lim_ext_loc with (fun x => 2 / x + 2 * (ln x / x)).
    exists 0.
    move => y Hy.
    rewrite /f /fab.
    field.
    by apply Rgt_not_eq.
  eapply is_lim_plus.
  apply is_lim_scal_l.
  apply is_lim_inv.
  by apply is_lim_id.
  by [].
  apply is_lim_scal_l.
  by apply is_lim_div_ln_p.
  unfold is_Rbar_plus, Rbar_plus' ; apply f_equal, f_equal ; ring.
Qed.

(** 2.c. *)

Lemma Variation_1 : forall x y, 0 < x -> x < y -> y < 1 -> f x < f y.
Proof.
  apply (incr_function _ 0 1 (fun x => (2 - 2 - 2 * ln x) / x ^ 2)).
  move => x H0x Hx1.
  by apply (Dfab 2 2 x).
  move => x H0x Hx1.
  apply sign_0_lt.
  rewrite -(is_derive_unique _ _ _ (Dfab 2 2 x H0x)).
  rewrite Signe_df.
  apply -> sign_0_lt.
  apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
  rewrite -ln_1.
  by apply ln_increasing.
  by apply H0x.
Qed.

Lemma Variation_2 : forall x y, 1 < x -> x < y -> f x > f y.
Proof.
  move => x y H1x Hxy.
  apply Ropp_lt_cancel.
  apply (incr_function (fun x => - f x) 1 p_infty (fun z => - ((2 - 2 - 2 * ln z) / z ^ 2))).
  move => z H1z _.
  apply: is_derive_opp.
  apply (Dfab 2 2 z).
  by apply Rlt_trans with (1 := Rlt_0_1).
  move => z H1z _.
  apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
  apply sign_lt_0.
  rewrite -(is_derive_unique _ _ _ (Dfab 2 2 z (Rlt_trans _ _ _ Rlt_0_1 H1z))).
  rewrite Signe_df.
  apply -> sign_lt_0.
  apply Ropp_lt_cancel ; rewrite Ropp_0 Ropp_involutive.
  rewrite -ln_1.
  apply ln_increasing.
  by apply Rlt_0_1.
  by apply H1z.
  by apply Rlt_trans with (1 := Rlt_0_1).
  by [].
  by [].
  by [].
Qed.

(** ** Questions 3 *)
(* 9:40 *)

(** 3.a *)

Lemma f_eq_1_0_1 : exists x, 0 < x <= 1 /\ f x = 1.
Proof.
  case: (IVT_Rbar_incr (fun x => f (Rabs x)) 0 1 m_infty 2 1).
    eapply filterlim_comp.
    apply filterlim_Rabs_0.
    by apply filterlim_f_0.
  apply is_lim_comp with 1.
  replace 2 with (f 1).
  apply is_lim_continuity.
  apply derivable_continuous_pt.
  exists (((2 - 2) - 2 * ln 1) / 1 ^ 2) ; apply is_derive_Reals, Dfab.
  by apply Rlt_0_1.
  rewrite /f /fab ln_1 /= ; field.
  rewrite -{2}(Rabs_pos_eq 1).
  apply (is_lim_continuity Rabs 1).
  by apply continuity_pt_filterlim, continuous_Rabs.
  by apply Rle_0_1.
  exists (mkposreal _ Rlt_0_1) => /= x H0x Hx.
  rewrite /ball /= /AbsRing_ball /= in H0x.
  apply Rabs_lt_between' in H0x.
  rewrite Rminus_eq_0 in H0x.
  contradict Hx.
  rewrite -(Rabs_pos_eq x).
  by apply Rbar_finite_eq.
  by apply Rlt_le, H0x.
  move => x H0x Hx1.
  apply (continuity_pt_comp Rabs).
  by apply continuity_pt_filterlim, continuous_Rabs.
  rewrite Rabs_pos_eq.
  apply derivable_continuous_pt.
  exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
  by [].
  by apply Rlt_le.
  by apply Rlt_0_1.
  split => //.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  move => x [H0x [Hx1 Hfx]].
  rewrite Rabs_pos_eq in Hfx.
  exists x ; repeat split.
  by apply H0x.
  by apply Rlt_le.
  by apply Hfx.
  by apply Rlt_le.
Qed.

(** 3.b. *)

Lemma f_eq_1_1_p_infty : exists x, 1 <= x /\ f x = 1.
Proof.
  case: (IVT_Rbar_incr (fun x => - f x) 1 p_infty (-2) 0 (-1)).
  replace (-2) with (-f 1).
  apply (is_lim_continuity (fun x => - f x)).
  apply continuity_pt_opp.
  apply derivable_continuous_pt.
  exists (((2 - 2) - 2 * ln 1) / 1 ^ 2) ; apply is_derive_Reals, Dfab.
  by apply Rlt_0_1.
  rewrite /f /fab ln_1 /= ; field.
  evar_last.
  apply is_lim_opp.
  by apply Lim_f_p_infty.
  simpl ; by rewrite Ropp_0.
  move => x H0x Hx1.
  apply continuity_pt_opp.
  apply derivable_continuous_pt.
  exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
  by apply Rlt_trans with (1 := Rlt_0_1).
  by [].
  split ; apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  move => x [H0x [Hx1 Hfx]].
  exists x ; split.
  by apply Rlt_le.
  rewrite -(Ropp_involutive (f x)) Hfx ; ring.
Qed.

(** ** Questions 5 *)
(* 10:08 *)

(** 5.a. *)

(** 5.b. *)

Lemma If : forall x, 0 < x -> is_derive (fun y : R => 2 * ln y + (ln y) ^ 2) x (f x).
Proof.
  move => y Hy.
  evar_last.
  apply @is_derive_plus.
  apply is_derive_Reals.
  apply derivable_pt_lim_scal.
  by apply derivable_pt_lim_ln.
  apply is_derive_pow.
  by apply is_derive_Reals, derivable_pt_lim_ln.
  rewrite /f /fab /plus /= ; field.
  by apply Rgt_not_eq.
Qed.

Lemma RInt_f : is_RInt f ( / exp 1) 1 1.
Proof.
  have Haux1: (0 < /exp 1).
    apply Rinv_0_lt_compat.
    apply exp_pos.
  evar_last.
  apply: is_RInt_derive.
  move => x Hx.
  apply If.
  apply Rlt_le_trans with (2 := proj1 Hx).
  apply Rmin_case.
  by apply Haux1.
  by apply Rlt_0_1.
  move => x Hx.
  apply continuity_pt_filterlim.
  apply derivable_continuous_pt.
  exists (((2 - 2) - 2 * ln x) / x ^ 2) ; apply is_derive_Reals, Dfab.
  apply Rlt_le_trans with (2 := proj1 Hx).
  apply Rmin_case.
  by apply Haux1.
  by apply Rlt_0_1.
  rewrite /minus /= /plus /opp /= -[eq]/(@eq R).
  rewrite ln_Rinv.
  rewrite ln_exp.
  rewrite ln_1.
  ring.
  by apply exp_pos.
Qed.

(** * Exercice 4 *)
(* 10:36 *)

Fixpoint u (n : nat) : R :=
  match n with
    | O => 2
    | S n => 2/3 * u n + 1/3 * (INR n) + 1
  end.

(** ** Questions 1 *)
(** 1.a. *)

(** 1.b. *)

(** ** Questions 2 *)
(* 10:40 *)
(** 2.a *)

Lemma Q2a : forall n, u n <= INR n + 3.
Proof.
  elim => [ | n IH] ; rewrite ?S_INR /=.
  apply Rminus_le_0 ; ring_simplify ; apply Rle_0_1.
  eapply Rle_trans.
  apply Rplus_le_compat_r.
  apply Rplus_le_compat_r.
  apply Rmult_le_compat_l.
  lra.
  by apply IH.
  lra.
Qed.

(** 2.b. *)
Lemma Q2b : forall n, u (S n) - u n = 1/3 * (INR n + 3 - u n).
Proof.
  move => n ; simpl.
  field.
Qed.

(** 2.c. *)

Lemma Q2c : forall n, u n <= u (S n).
Proof.
  move => n.
  apply Rminus_le_0.
  rewrite Q2b.
  apply Rmult_le_pos.
  lra.
  apply (Rminus_le_0 (u n)).
  by apply Q2a.
Qed.

(** ** Question 3 *)
(* 10:49 *)

Definition v (n : nat) : R := u n - INR n.

(** 3.a. *)

Lemma Q3a : forall n, v n = 2 * (2/3) ^ n.
Proof.
  elim => [ | n IH].
  rewrite /v /u /= ; ring.
  replace (2 * (2 / 3) ^ S n) with (v n * (2/3)) by (rewrite IH /= ; ring).
  rewrite /v S_INR /=.
  field.
Qed.

(** 3.b. *)

Lemma Q3b : forall n, u n = 2 * (2/3)^n + INR n.
Proof.
  move => n.
  rewrite -Q3a /v ; ring.
Qed.

Lemma Q3c : is_lim_seq u p_infty.
Proof.
  apply is_lim_seq_ext with (fun n => 2 * (2/3)^n + INR n).
  move => n ; by rewrite Q3b.
  eapply is_lim_seq_plus.
  eapply is_lim_seq_mult.
  by apply is_lim_seq_const.
  apply is_lim_seq_geom.
  rewrite Rabs_pos_eq.
  lra.
  lra.
  by [].
  apply is_lim_seq_INR.
  by [].
Qed.

(** ** Questions 4 *)
(* 11:00 *)

Definition Su (n : nat) : R := sum_f_R0 u n.
Definition Tu (n : nat) : R := Su n / (INR n) ^ 2.

(** 4.a. *)

Lemma Q4a : forall n, Su n = 6 - 4 * (2/3)^n + INR n * (INR n + 1) / 2.
Proof.
  move => n.
  rewrite /Su.
  rewrite -(sum_eq (fun n => (2/3)^n * 2 + INR n)).
  rewrite sum_plus.
  rewrite -scal_sum.
  rewrite tech3.
  rewrite sum_INR.
  simpl ; field.
  apply Rlt_not_eq, Rlt_div_l.
  repeat apply Rplus_lt_0_compat ; apply Rlt_0_1.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  move => i _.
  rewrite Q3b ; ring.
Qed.

(** 4.b. *)

Lemma Q4b : is_lim_seq Tu (1/2).
Proof.
  apply is_lim_seq_ext_loc with (fun n => (6 - 4 * (2/3)^n) / (INR n ^2) + / (2 * INR n) + /2).
    exists 1%nat => n Hn ; rewrite /Tu Q4a.
    simpl ; field.
    apply Rgt_not_eq, (lt_INR O) ; intuition.
  eapply is_lim_seq_plus.
  eapply is_lim_seq_plus.
  eapply is_lim_seq_div.
  eapply is_lim_seq_minus.
  apply is_lim_seq_const.
  eapply is_lim_seq_mult.
  by apply is_lim_seq_const.
  apply is_lim_seq_geom.
  rewrite Rabs_pos_eq.
  lra.
  lra.
  by [].
  rewrite /is_Rbar_minus /is_Rbar_plus /=.
  now ring_simplify (6 + - (4 * 0)).
  repeat eapply is_lim_seq_mult.
  apply is_lim_seq_INR.
  apply is_lim_seq_INR.
  apply is_lim_seq_const.
  apply is_Rbar_mult_p_infty_pos.
  by apply Rlt_0_1.
  by [].
  by [].
  by apply is_Rbar_div_p_infty.
  apply is_lim_seq_inv.
  eapply is_lim_seq_mult.
  by apply is_lim_seq_const.
  by apply is_lim_seq_INR.
  by apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos, Rlt_0_2.
  by [].
  by [].
  apply is_lim_seq_const.
  apply (f_equal (@Some _)), f_equal.
  field.
Qed.
(* 11:33 *)
