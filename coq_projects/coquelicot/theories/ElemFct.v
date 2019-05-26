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

Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.

(** This file describes basic properties (such as limits or
differentiability) about basic functions: absolute value, inverse,
square root, power, exponential and so on.*)

(** * Absolute value *)

(** ** in an [AbsRing] *)

Lemma continuous_abs {K : AbsRing} (x : K) :
  continuous abs x.
Proof.
  apply filterlim_locally => /= eps.
  exists eps => /= y Hy.
  eapply Rle_lt_trans, Hy.
  wlog: x y Hy / (abs x <= abs y) => [Hw | Hxy].
    case: (Rle_lt_dec (abs x) (abs y)) => Hxy.
    by apply Hw.
    rewrite abs_minus (abs_minus y).
    apply Hw, Rlt_le, Hxy.
    by apply ball_sym.
  rewrite {1}/abs /=.
  rewrite Rabs_pos_eq.
  apply Rle_minus_l.
  eapply Rle_trans, abs_triangle.
  apply Req_le, f_equal.
  by rewrite /minus -plus_assoc plus_opp_l plus_zero_r.
  by apply -> Rminus_le_0.
Qed.
Lemma filterlim_abs_0 {K : AbsRing} :
  (forall x : K, abs x = 0 -> x = zero) ->
  filterlim (abs (K := K)) (locally' (zero (G := K))) (at_right 0).
Proof.
intros H P [eps HP].
exists eps.
intros x Hx Hx'.
apply HP.
revert Hx.
rewrite /ball /= /AbsRing_ball !minus_zero_r {2}/abs /= Rabs_pos_eq.
by [].
by apply abs_ge_0.
assert (abs x <> 0).
contradict Hx' ; by apply H.
case: (abs_ge_0 x) => // H1.
by rewrite -H1 in H0.
Qed.

(** ** in [R] *)

Lemma continuous_Rabs (x : R) :
  continuous Rabs x.
Proof.
  by apply @continuous_abs.
Qed.

Lemma filterlim_Rabs (x : Rbar) :
  filterlim Rabs (Rbar_locally' x) (Rbar_locally (Rbar_abs x)).
Proof.
  destruct x as [x| | ] => //=.

  eapply filterlim_filter_le_1, continuous_Rabs.
  intros P [d HP] ; exists d => y Hy _.
  by apply HP.

  eapply filterlim_ext_loc.
  exists 0 => y Hy.
  rewrite Rabs_pos_eq // ; by apply Rlt_le.
  apply is_lim_id.

  eapply filterlim_ext_loc.
  exists 0 => y Hy.
  rewrite -Rabs_Ropp Rabs_pos_eq // -Ropp_0 ;
  by apply Ropp_le_contravar, Rlt_le.
  apply (is_lim_opp id m_infty m_infty), is_lim_id.
Qed.
Lemma is_lim_Rabs (f : R -> R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun x => Rabs (f x)) x (Rbar_abs l).
Proof.
  destruct l as [l| | ] ; simpl ; intros ; first last.
  eapply is_lim_comp.
  2: by apply H.
  by apply filterlim_Rabs.
  destruct x ; by exists (mkposreal _ Rlt_0_1).
  eapply is_lim_comp.
  2: by apply H.
  by apply filterlim_Rabs.
  destruct x ; by exists (mkposreal _ Rlt_0_1).
  apply is_lim_comp_continuous => //.
  by apply continuous_Rabs.
Qed.

Lemma filterlim_Rabs_0 :
  filterlim Rabs (Rbar_locally' 0) (at_right 0).
Proof.
  apply @filterlim_abs_0.
  by apply Rabs_eq_0.
Qed.
Lemma is_lim_Rabs_0 (f : R -> R) (x : Rbar) :
  is_lim f x 0 -> Rbar_locally' x (fun x => f x <> 0)
    -> filterlim (fun x => Rabs (f x)) (Rbar_locally' x) (at_right 0).
Proof.
  intros.
  eapply filterlim_comp, filterlim_Rabs_0.
  intros P HP.
  apply H in HP.
  generalize (filter_and _ _ H0 HP).
  rewrite /filtermap /= ; apply filter_imp.
  intros y Hy.
  apply Hy, Hy.
Qed.

Lemma filterdiff_Rabs (x : R) :
  x <> 0 -> filterdiff Rabs (locally x) (fun y : R => scal y (sign x)).
Proof.
  rewrite -/(is_derive Rabs x (sign x)).
  move => Hx0.
  case: (Rle_lt_dec 0 x) => Hx.
  case: Hx => //= Hx.
  rewrite sign_eq_1 //.
  eapply is_derive_ext_loc.
  apply locally_interval with 0 p_infty.
  by [].
  by [].
  move => /= y Hy _.
  rewrite Rabs_pos_eq //.
  by apply Rlt_le.
  by apply @is_derive_id.
  by apply sym_eq in Hx.
  rewrite sign_eq_m1 //.
  eapply is_derive_ext_loc.
  apply locally_interval with m_infty 0.
  by [].
  by [].
  move => /= y _ Hy.
  rewrite -Rabs_Ropp Rabs_pos_eq //.
  rewrite -Ropp_0 ; by apply Rlt_le, Ropp_lt_contravar.
  apply @is_derive_opp.
  by apply @is_derive_id.
Qed.
Lemma is_derive_Rabs (f : R -> R) (x df : R) :
  is_derive f x df -> f x <> 0
    -> is_derive (fun x => Rabs (f x)) x (sign (f x) * df).
Proof.
  intros Hf Hfx.
  evar_last.
  apply is_derive_comp, Hf.
  by apply filterdiff_Rabs.
  apply Rmult_comm.
Qed.

(** * Inverse function *)

Lemma filterlim_Rinv_0_right :
  filterlim Rinv (at_right 0) (Rbar_locally p_infty).
Proof.
  intros P [M HM].
  have Hd : 0 < / Rmax 1 M.
    apply Rinv_0_lt_compat.
    apply Rlt_le_trans with (2 := Rmax_l _ _).
    by apply Rlt_0_1.
  exists (mkposreal _ Hd) => x /= Hx Hx0.
  apply HM.
  apply Rle_lt_trans with (1 := Rmax_r 1 M).
  replace (Rmax 1 M) with (/ / Rmax 1 M)
  by (field ; apply Rgt_not_eq, Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1).
  apply Rinv_lt_contravar.
  apply Rdiv_lt_0_compat with (1 := Hx0).
  apply Rlt_le_trans with (2 := Rmax_l _ _), Rlt_0_1.
  rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
  rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq // in Hx.
  exact: Rlt_le.
Qed.
Lemma is_lim_Rinv_0_right (f : R -> R) (x : Rbar) :
  is_lim f x 0 -> Rbar_locally' x (fun x => 0 < f x) ->
  is_lim (fun x => / (f x)) x p_infty.
Proof.
  intros.
  eapply filterlim_comp, filterlim_Rinv_0_right.
  intros P HP.
  apply H in HP.
  generalize (filter_and _ _ H0 HP).
  rewrite /filtermap ;
  apply filter_imp => y Hy.
  by apply Hy, Hy.
Qed.

Lemma filterlim_Rinv_0_left :
  filterlim Rinv (at_left 0) (Rbar_locally m_infty).
Proof.
  eapply filterlim_ext_loc.
  exists (mkposreal _ Rlt_0_1) => /= y _ Hy0.
  rewrite -{2}(Ropp_involutive y).
  rewrite -Ropp_inv_permute.
  reflexivity.
  contradict Hy0.
  apply Rle_not_lt, Req_le.
  by rewrite -(Ropp_involutive y) Hy0 Ropp_0.
  eapply filterlim_comp.
  eapply filterlim_comp.
  by apply filterlim_Ropp_left.
  rewrite Ropp_0.
  by apply filterlim_Rinv_0_right.
  apply filterlim_Rbar_opp.
Qed.
Lemma is_lim_Rinv_0_left (f : R -> R) (x : Rbar) :
  is_lim f x 0 -> Rbar_locally' x (fun x => f x < 0) ->
  is_lim (fun x => / (f x)) x m_infty.
Proof.
  intros.
  eapply filterlim_comp, filterlim_Rinv_0_left.
  intros P HP.
  apply H in HP.
  generalize (filter_and _ _ H0 HP).
  rewrite /filtermap ;
  apply filter_imp => y Hy.
  by apply Hy, Hy.
Qed.

(** * Square root function *)

Lemma filterlim_sqrt_p : filterlim sqrt (Rbar_locally' p_infty) (Rbar_locally p_infty).
Proof.
  apply is_lim_spec.
  move => M.
  exists ((Rmax 0 M)²) => x Hx.
  apply Rle_lt_trans with (1 := Rmax_r 0 M).
  rewrite -(sqrt_Rsqr (Rmax 0 M)).
  apply sqrt_lt_1_alt.
  split.
  apply Rle_0_sqr.
  by apply Hx.
  apply Rmax_l.
Qed.
Lemma is_lim_sqrt_p (f : R -> R) (x : Rbar) :
  is_lim f x p_infty
  -> is_lim (fun x => sqrt (f x)) x p_infty.
Proof.
  intros.
  eapply filterlim_comp, filterlim_sqrt_p.
  by apply H.
Qed.

Lemma filterdiff_sqrt (x : R) :
  0 < x -> filterdiff sqrt (locally x) (fun y => scal y (/ (2 * sqrt x))).
Proof.
  intros Hx.
  apply is_derive_Reals.
  by apply derivable_pt_lim_sqrt.
Qed.
Lemma is_derive_sqrt (f : R -> R) (x df : R) :
  is_derive f x df -> 0 < f x
  -> is_derive (fun x => sqrt (f x)) x (df / (2 * sqrt (f x))).
Proof.
  intros Hf Hfx.
  evar_last.
  eapply is_derive_comp.
  by apply filterdiff_sqrt.
  by apply Hf.
  reflexivity.
Qed.

(** * Power function *)
Section nat_to_ring.

Context {K : Ring}.

Definition nat_to_ring (n : nat) : K :=
  sum_n_m (fun _ => one) 1 n.
Lemma nat_to_ring_O :
  nat_to_ring O = zero.
Proof.
  rewrite /nat_to_ring sum_n_m_zero //.
Qed.
Lemma nat_to_ring_Sn (n : nat) :
  nat_to_ring (S n) = plus (nat_to_ring n) one.
Proof.
  case: n => [ | n] ; rewrite /nat_to_ring.
  rewrite sum_n_n sum_n_m_zero //.
  by rewrite plus_zero_l.
  rewrite sum_n_Sm //.
  by apply le_n_S, le_O_n.
Qed.

End nat_to_ring.

Section is_derive_mult.

Context {K : AbsRing}.

Lemma is_derive_mult (f g : K -> K) x (df dg : K) :
  is_derive f x df -> is_derive g x dg
  -> (forall n m : K, mult n m = mult m n)
  -> is_derive (fun x : K => mult (f x) (g x)) x (plus (mult df (g x)) (mult (f x) dg)).
Proof.
  intros Hf Hg Hmult.
  eapply filterdiff_ext_lin.
  eapply filterdiff_comp_2 => /=.
  by apply Hf.
  by apply Hg.
  eapply filterdiff_ext_lin.
  apply (filterdiff_mult (f x,g x)) => /=.
  intros P [d Hd].
  assert (Cf := ex_derive_continuous f x).
  assert (Cg := ex_derive_continuous g x).
  destruct (fun H => proj1 (filterlim_locally _ _) (Cf H) d) as [d1 Hd1].
    eexists ; by apply Hf.
  destruct (fun H => proj1 (filterlim_locally _ _) (Cg H) d) as [d2 Hd2].
    eexists ; by apply Hg.
  exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= y Hy.
  apply Hd ; split => /=.
  eapply (Hd1 y), ball_le, Hy.
  by apply Rmin_l.
  eapply (Hd2 y), ball_le, Hy.
  by apply Rmin_r.
  by apply Hmult.
  simpl => [[y1 y2]] /=.
  reflexivity.
  simpl => y.
  rewrite /scal /=.
  rewrite mult_assoc (Hmult (f x)) -!mult_assoc.
  by rewrite mult_distr_l.
Qed.

End is_derive_mult.

Lemma filterdiff_pow_n {K : AbsRing} (x : K) (n : nat) :
  (forall a b : K, mult a b = mult b a)
  -> filterdiff (fun y : K => pow_n y n) (locally x)
    (fun y : K => scal y (mult (nat_to_ring n) (pow_n x (pred n)))).
Proof.
  intros Hmult.
  rewrite -/(is_derive (fun y : K => pow_n y n) x (mult (nat_to_ring n) (pow_n x (pred n)))).
  elim: n => [ | n IH] /=.
  evar_last.
  apply is_derive_const.
  by rewrite nat_to_ring_O mult_zero_l.
  evar_last.
  eapply is_derive_mult.
  apply is_derive_id.
  apply IH.
  by apply Hmult.
  simpl.
  rewrite nat_to_ring_Sn mult_one_l mult_assoc (Hmult x) -mult_assoc.
  rewrite mult_distr_r mult_one_l plus_comm.
  apply f_equal2 => //.
  clear ; case: n => [ | n] //=.
  by rewrite nat_to_ring_O !mult_zero_l.
Qed.

Lemma is_derive_n_pow_smalli: forall i p x, (i <= p)%nat ->
  is_derive_n (fun x : R => x ^ p) i x
    (INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat).
Proof.
  elim => /= [ | i IH] p x Hip.
  rewrite -minus_n_O ; field.
  by apply INR_fact_neq_0.
  eapply is_derive_ext.
  intros t.
  apply sym_equal, is_derive_n_unique, IH.
  eapply le_trans, Hip ; by apply le_n_Sn.
  evar_last.
  apply is_derive_scal, is_derive_pow, is_derive_id.
  rewrite MyNat.sub_succ_r.
  change one with 1.
  rewrite {1 2} (S_pred (p - i) O) /fact -/fact ?mult_INR.
  field.
  split.
  apply INR_fact_neq_0.
  apply not_0_INR, sym_not_eq, O_S.
  by apply lt_minus_O_lt.
Qed.
Lemma Derive_n_pow_smalli: forall i p x, (i <= p)%nat ->
  Derive_n (fun x : R => x ^ p) i x
    = INR (fact p) / INR (fact (p - i)%nat) * x ^ (p - i)%nat.
Proof.
  intros.
  now apply is_derive_n_unique, is_derive_n_pow_smalli.
Qed.
Lemma is_derive_n_pow_bigi: forall i p x,  (p < i) %nat ->
                         is_derive_n (fun x : R => x ^ p) i x 0.
Proof.
  elim => /=  [ | i IH] p x Hip.
  by apply lt_n_O in Hip.
  apply lt_n_Sm_le, le_lt_eq_dec in Hip.
  case: Hip => [Hip | ->] ;
  eapply is_derive_ext.
  intros t ; by apply sym_equal, is_derive_n_unique, IH.
  apply @is_derive_const.
  intros t ; rewrite Derive_n_pow_smalli.
  by rewrite minus_diag /=.
  by apply le_refl.
  by apply @is_derive_const.
Qed.
Lemma Derive_n_pow_bigi: forall i p x,  (p < i) %nat ->
                         Derive_n (fun x : R => x ^ p) i x = 0.
Proof.
  intros.
  now apply is_derive_n_unique, is_derive_n_pow_bigi.
Qed.

Lemma Derive_n_pow i p x:
  Derive_n (fun x : R => x ^ p) i x =
    match (le_dec i p) with
    | left _ => INR (fact p) / INR (fact (p -i)%nat) * x ^ (p - i)%nat
    | right _ => 0
    end.
Proof.
case: le_dec => H.
by apply Derive_n_pow_smalli.
by apply Derive_n_pow_bigi, not_le.
Qed.

Lemma ex_derive_n_pow i p x: ex_derive_n (fun x : R => x ^ p) i x.
Proof.
  case: i => //= i.
  exists (Derive_n (fun x : R => x ^ p) (S i) x).
  rewrite Derive_n_pow.
  case: le_dec => Hip.
  by apply (is_derive_n_pow_smalli (S i)).
  apply (is_derive_n_pow_bigi (S i)) ; omega.
Qed.

Lemma is_RInt_pow :
  forall a b n,
  is_RInt (fun x => pow x n) a b (pow b (S n) / INR (S n) - pow a (S n) / INR (S n)).
Proof.
intros a b n.
set f := fun x => pow x (S n) / INR (S n).
fold (f a) (f b).
assert (H: forall x : R, is_derive f x (pow x n)).
  intros x.
  evar_last.
  rewrite /f /Rdiv -[Rmult]/(scal (V := R_NormedModule)).
  apply is_derive_scal_l.
  apply is_derive_pow, is_derive_id.
  rewrite /pred.
  set k := INR (S n).
  rewrite /scal /= /mult /one /=.
  field.
  rewrite /k S_INR.
  apply Rgt_not_eq, INRp1_pos.
  apply: is_RInt_derive => x Hx //.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
apply derivable_pt_pow.
Qed.

(** * Exponential function *)

Lemma exp_ge_taylor (x : R) (n : nat) :
  0 <= x -> sum_f_R0 (fun k => x^k / INR (fact k)) n <= exp x.
Proof.
  move => Hx.
  rewrite /exp /exist_exp.
  case: Alembert_C3 => /= y Hy.
  apply Rnot_lt_le => H.
  apply Rminus_lt_0 in H.
  case: (Hy _ H) => N {Hy} Hy.
  move: (Hy _ (le_plus_r n N)) => {Hy}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | N IH].
  rewrite plus_0_r.
  apply Req_le.
  elim: (n) => {n H} [ | n /= <-].
  apply Rmult_comm.
  apply f_equal.
  apply Rmult_comm.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm.
  move: (n + N)%nat => {n H N IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  apply Rminus_le_0 ; ring_simplify.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  by apply pow_le.
Qed.

(** Definition *)

Lemma is_exp_Reals (x : R) :
  is_pseries (fun n => / INR (fact n)) x (exp x).
Proof.
  rewrite /exp.
  case: exist_exp => l /= Hl.
  apply Series.is_series_Reals in Hl.
  move: Hl ;
  apply Series.is_series_ext => n.
  by rewrite Rmult_comm pow_n_pow.
Qed.
Lemma exp_Reals (x : R) :
  exp x = PSeries (fun n => / INR (fact n)) x.
Proof.
  apply sym_eq, is_pseries_unique.
  by apply is_exp_Reals.
Qed.

(** Limits *)

Lemma is_lim_exp_p : is_lim (fun y => exp y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => 1 + y).
  exists 0 => y Hy.
  by apply Rlt_le, exp_ineq1.
  pattern p_infty at 2.
  replace p_infty with (Rbar_plus 1 p_infty) by auto.
  eapply is_lim_plus.
  apply is_lim_const.
  apply is_lim_id.
  by [].
Qed.
Lemma is_lim_exp_m : is_lim (fun y => exp y) m_infty 0.
Proof.
  evar_last.
  apply is_lim_ext with (fun y => /(exp (- y))).
  move => y ; rewrite exp_Ropp ; apply Rinv_involutive.
  apply Rgt_not_eq, exp_pos.
  apply is_lim_inv.
  apply is_lim_comp with p_infty.
  apply is_lim_exp_p.
  replace p_infty with (Rbar_opp m_infty) by auto.
  apply is_lim_opp.
  apply is_lim_id.
  by apply filter_forall.
  by [].
  by [].
Qed.

Lemma ex_lim_exp (x : Rbar) : ex_lim (fun y => exp y) x.
Proof.
  case: x => [x | | ].
  apply ex_finite_lim_correct, ex_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  exists p_infty ; by apply is_lim_exp_p.
  exists 0 ; by apply is_lim_exp_m.
Qed.
Lemma Lim_exp (x : Rbar) :
  Lim (fun y => exp y) x =
    match x with
      | Finite x => exp x
      | p_infty => p_infty
      | m_infty => 0
    end.
Proof.
  apply is_lim_unique.
  case: x => [x | | ].
  apply is_lim_continuity.
  apply derivable_continuous_pt, derivable_pt_exp.
  by apply is_lim_exp_p.
  by apply is_lim_exp_m.
Qed.

Lemma is_lim_div_exp_p : is_lim (fun y => exp y / y) p_infty p_infty.
Proof.
  apply is_lim_le_p_loc with (fun y => (1 + y + y^2 / 2)/y).
  exists 0 => y Hy.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rinv_0_lt_compat.
  rewrite /exp.
  rewrite /exist_exp.
  case: Alembert_C3 => /= x Hx.
  rewrite /Pser /infinite_sum in Hx.
  apply Rnot_lt_le => H.
  case: (Hx _ (proj1 (Rminus_lt_0 _ _) H)) => N {Hx} Hx.
  move: (Hx _ (le_plus_r 2 N)) => {Hx}.
  apply Rle_not_lt.
  apply Rle_trans with (2 := Rle_abs _).
  apply Rplus_le_compat_r.
  elim: N => [ | n IH].
  simpl ; apply Req_le ; field.
  apply Rle_trans with (1 := IH).
  rewrite -plus_n_Sm ; move: (2 + n)%nat => {n IH} n.
  rewrite /sum_f_R0 -/sum_f_R0.
  rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_eq_0.
  apply Rmult_le_pos.
  apply Rlt_le, Rinv_0_lt_compat, INR_fact_lt_0.
  apply pow_le.
  by apply Rlt_le.
  apply is_lim_ext_loc with (fun y => /y + 1 + y / 2).
  exists 0 => y Hy.
  field.
  by apply Rgt_not_eq.
  eapply is_lim_plus.
  eapply is_lim_plus.
  apply is_lim_inv.
  apply is_lim_id.
  by [].
  apply is_lim_const.
  by [].
  apply is_lim_div.
  apply is_lim_id.
  apply is_lim_const.
  apply Rbar_finite_neq, Rgt_not_eq, Rlt_0_2.
  simpl.
  apply Rgt_not_eq, Rinv_0_lt_compat, Rlt_0_2.
  simpl.
  case: Rle_dec (Rlt_le _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
  case: Rle_lt_or_eq_dec (Rlt_not_eq _ _ (Rinv_0_lt_compat 2 (Rlt_0_2))) => //= H _.
Qed.

Lemma is_lim_mul_exp_m : is_lim (fun y => y * exp y) m_infty 0.
Proof.
  evar_last.
  apply is_lim_ext_loc with (fun y => - / (exp (-y) / (- y))).
  exists 0 => y Hy.
  rewrite exp_Ropp.
  field.
  split.
  apply Rgt_not_eq, exp_pos.
  by apply Rlt_not_eq.
  apply is_lim_opp.
  apply is_lim_inv.
  apply (is_lim_comp (fun y => exp y / y)) with p_infty.
  by apply is_lim_div_exp_p.
  evar_last.
  apply is_lim_opp.
  apply is_lim_id.
  by [].
  by apply filter_forall.
  by [].
  simpl ; by rewrite Ropp_0.
Qed.

Lemma is_lim_div_expm1_0 : is_lim (fun y => (exp y - 1) / y) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_exp_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l exp_0.
Qed.

(** Integral *)

Lemma is_RInt_exp :
  forall a b,
  is_RInt exp a b (exp b - exp a).
Proof.
intros a b.
apply: is_RInt_derive.
  intros x _.
  apply is_derive_Reals, derivable_pt_lim_exp.
intros x _.
apply continuity_pt_filterlim.
apply derivable_continuous_pt.
apply derivable_pt_exp.
Qed.

(** * Natural logarithm *)

Lemma is_lim_ln_p : is_lim (fun y => ln y) p_infty p_infty.
Proof.
  apply is_lim_spec.
  move => M.
  exists (exp M) => x Hx.
  rewrite -(ln_exp M).
  apply ln_increasing.
  apply exp_pos.
  by apply Hx.
Qed.

Lemma is_lim_ln_0 :
  filterlim ln (at_right 0) (Rbar_locally m_infty).
Proof.
intros P [M HM].
exists (mkposreal (exp M) (exp_pos _)) => x /= Hx Hx0.
apply HM.
rewrite <- (ln_exp M).
apply ln_increasing.
exact Hx0.
rewrite /ball /= /AbsRing_ball /= /abs /minus /plus /opp /= in Hx.
rewrite -/(Rminus _ _) Rminus_0_r Rabs_pos_eq in Hx.
exact Hx.
now apply Rlt_le.
Qed.

Lemma is_lim_div_ln_p : is_lim (fun y => ln y / y) p_infty 0.
Proof.
  have H : forall x, 0 < x -> ln x < x.
    move => x Hx.
    apply Rminus_lt_0.
    apply Rlt_le_trans with (1 := Rlt_0_1).
    case: (MVT_gen (fun y => y - ln y) 1 x (fun y => (y-1)/y)).
      move => z Hz.
      evar (l : R).
      replace ((z - 1) / z) with l.
      apply is_derive_Reals.
      apply derivable_pt_lim_minus.
      apply derivable_pt_lim_id.
      apply derivable_pt_lim_ln.
      eapply Rlt_trans, Hz.
      apply Rmin_case => //.
      by apply Rlt_0_1.
      rewrite /l ; field.
      apply Rgt_not_eq ; eapply Rlt_trans, Hz.
      apply Rmin_case => //.
      by apply Rlt_0_1.
    move => y Hy.
    apply continuity_pt_minus.
    apply continuity_pt_id.
    apply derivable_continuous_pt ;
    eexists ; apply derivable_pt_lim_ln.
    eapply Rlt_le_trans, Hy.
      apply Rmin_case => //.
      by apply Rlt_0_1.
    move => c [Hc H0].
    replace 1 with (1 - ln 1) by (rewrite ln_1 Rminus_0_r //).
    apply Rminus_le_0.
    rewrite H0.
    move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec => H1 Hc.
    apply Rmult_le_pos.
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Hc.
    apply Rlt_le_trans with (1 := Rlt_0_1).
    by apply Hc.
    apply -> Rminus_le_0 ; apply H1.
    apply Rnot_le_lt in H1.
    replace ((c - 1) / c * (x - 1)) with ((1-c) * (1-x) / c).
    apply Rdiv_le_0_compat.
    apply Rmult_le_pos.
    apply -> Rminus_le_0 ; apply Hc.
    apply -> Rminus_le_0 ; apply Rlt_le, H1.
    apply Rlt_le_trans with (1 := Hx).
    by apply Hc.
    field.
    apply Rgt_not_eq.
    apply Rlt_le_trans with (1 := Hx).
    by apply Hc.
  apply (is_lim_le_le_loc (fun _ => 0) (fun y => 2/sqrt y)).
  exists 1 => x Hx.
  split.
  apply Rdiv_le_0_compat.
  rewrite -ln_1.
  apply ln_le.
  apply Rlt_0_1.
  by apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  replace (ln _) with (2 * ln (sqrt x)).
  rewrite /Rdiv Rmult_assoc.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rle_div_l.
  by apply Rlt_trans with (1 := Rlt_0_1).
  rewrite -{3}(sqrt_sqrt x).
  field_simplify ; rewrite ?Rdiv_1.
  apply Rlt_le, H.
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply Rgt_not_eq.
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  change 2 with (INR 2).
  rewrite -ln_pow.
  rewrite /= Rmult_1_r.
  rewrite sqrt_sqrt.
  by [].
  apply Rlt_le.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply sqrt_lt_R0.
  by apply Rlt_trans with (1 := Rlt_0_1).
  apply is_lim_const.
  evar_last.
  apply is_lim_div.
  apply is_lim_const.
  apply filterlim_sqrt_p.
  by [].
  by [].
  simpl ; by rewrite Rmult_0_r.
Qed.

Lemma is_lim_div_ln1p_0 : is_lim (fun y => ln (1+y) / y) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_ln 1 (Rlt_0_1) eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite ln_1 Rinv_1 Rminus_0_r.
Qed.

(** * Unnormalized sinc *)

Lemma is_lim_sinc_0 : is_lim (fun x => sin x / x) 0 1.
Proof.
  apply is_lim_spec.
  move => eps.
  case: (derivable_pt_lim_sin_0 eps (cond_pos eps)) => delta H.
  exists delta => y Hy Hy0.
  rewrite /ball /= /AbsRing_ball /= /minus /plus /opp /= in Hy.
  rewrite /= -/(Rminus _ _) Rminus_0_r in Hy.
  move: (H y Hy0 Hy).
  by rewrite Rplus_0_l sin_0 Rminus_0_r.
Qed.

(** * ArcTan *)

Lemma CV_radius_atan : CV_radius (fun n => (-1)^n / (INR (S (n + n)))) = 1.
Proof.
  apply eq_trans with (2 := f_equal Finite Rinv_1).
  apply CV_radius_finite_DAlembert.
  intros n.
  apply Rmult_integral_contrapositive_currified.
  apply pow_nonzero.
  apply Rlt_not_eq, Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  rewrite S_INR ; by apply Rgt_not_eq, RinvN_pos.
  by apply Rlt_0_1.
  apply is_lim_seq_ext with (fun n => 1 - 2 / (2 * INR n + 3)).
  intros n.
  rewrite -plus_n_Sm plus_Sn_m !S_INR plus_INR.
  assert (0 < INR n + INR n + 1).
    rewrite -plus_INR -S_INR.
    by apply (lt_INR O), lt_O_Sn.
  assert (0 < INR n + INR n + 1 + 1 + 1).
    rewrite -plus_INR -!S_INR.
    by apply (lt_INR O), lt_O_Sn.
  rewrite !Rabs_div ; try by apply Rgt_not_eq.
  rewrite -!RPow_abs Rabs_m1 !pow1 !Rabs_pos_eq ; try by left.
  field.
  split ; by apply Rgt_not_eq.
  apply Rmult_integral_contrapositive_currified.
  apply pow_nonzero.
  apply Rlt_not_eq, Rminus_lt_0 ; ring_simplify ; apply Rlt_0_1.
  rewrite -plus_INR ; by apply Rgt_not_eq, RinvN_pos.
  evar_last.
  apply is_lim_seq_minus'.
  apply filterlim_const.
  eapply is_lim_seq_div.
  apply is_lim_seq_const.
  eapply is_lim_seq_plus.
  eapply is_lim_seq_mult.
  apply is_lim_seq_const.
  apply is_lim_seq_INR.
  apply is_Rbar_mult_sym, is_Rbar_mult_p_infty_pos.
  by apply Rlt_0_2.
  apply is_lim_seq_const.
  reflexivity ; simpl.
  by [].
  reflexivity.
  simpl ; apply f_equal ; ring.
Qed.
Lemma atan_Reals (x : R) : Rabs x < 1
  -> atan x = x * PSeries (fun n => (-1)^n / (INR (S (n + n)))) (x ^ 2).
Proof.
  wlog: x / (0 <= x) => [Hw | Hx0] Hx.
    case: (Rle_lt_dec 0 x) => Hx0.
    by apply Hw.
    rewrite -{1}(Ropp_involutive x) atan_opp Hw.
    replace ((- x) ^ 2) with (x^2) by ring.
    ring.
    apply Ropp_le_cancel ; rewrite Ropp_involutive Ropp_0 ; by left.
    by rewrite Rabs_Ropp.
  rewrite Rabs_pos_eq // in Hx.
  case: Hx0 => Hx0.
  rewrite atan_eq_ps_atan ; try by split.
  rewrite /ps_atan.
  case: Ratan.in_int => H.
  case: ps_atan_exists_1 => ps Hps.
  apply sym_eq.
  rewrite -Series.Series_scal_l.
  apply Series.is_series_unique.
  apply is_lim_seq_Reals in Hps.
  move: Hps ; apply is_lim_seq_ext => n.
  rewrite -sum_n_Reals.
  apply sum_n_ext => k.
  rewrite /tg_alt /Ratan_seq S_INR !plus_INR.
  rewrite pow_add -pow_mult.
  simpl ; field.
  rewrite -plus_INR -S_INR.
  apply Rgt_not_eq, (lt_INR 0), lt_O_Sn.
  contradict H ; split.
  apply Rle_trans with 0.
  apply Rminus_le_0 ; ring_simplify ; by apply Rle_0_1.
  by left.
  by left.
  by rewrite -Hx0 atan_0 Rmult_0_l.
Qed.
