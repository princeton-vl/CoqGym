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

Require Import Reals Omega Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Hierarchy Continuity Derive.

(** This file describes results about differentiability in [R x
 R]. This includes the [Schwarz] theorem and the 2D Taylor-Lagrange
 inequality. *)

(** * Differentiability *)

Definition differentiable_pt_lim (f : R -> R -> R) (x y : R) (lx ly : R) :=
  forall eps : posreal, locally_2d (fun u v =>
    Rabs (f u v - f x y - (lx * (u - x) + ly * (v - y))) <= eps * Rmax (Rabs (u - x)) (Rabs (v - y))) x y.

Lemma filterdiff_differentiable_pt_lim (f : R -> R -> R) (x y lx ly : R) :
  filterdiff (fun u : R * R => f (fst u) (snd u)) (locally (x,y)) (fun u : R * R => fst u * lx + snd u * ly)
  <-> differentiable_pt_lim f x y lx ly.
Proof.
  split => Df.
  move => eps.
  case: Df => _ Df.
  assert (is_filter_lim (locally (x, y)) (x, y)) by now intro.
  specialize (Df (x,y) H) => {H}.
  apply locally_2d_locally.
  assert (0 < eps / sqrt 2).
    apply Rdiv_lt_0_compat.
    by apply eps.
    by apply Rlt_sqrt2_0.
  move: (Df (mkposreal _ H)).
  apply filter_imp => [[u v] /= Huv].
  rewrite !(Rmult_comm _ (_-_)).
  eapply Rle_trans.
  apply Huv.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  rewrite Rmult_comm Rle_div_l.
  rewrite Rmult_comm.
  eapply Rle_trans.
  apply norm_prod.
  apply Rle_refl.
  by apply Rlt_sqrt2_0.
  
  split.
  apply (is_linear_comp (fun u : R * R => (scal (fst u) lx,scal (snd u) ly))
                          (fun u : R * R => plus (fst u) (snd u))).
  apply is_linear_prod.
  apply (is_linear_comp (@fst _ _) (fun t : R => scal t lx)).
  by apply is_linear_fst.
  by apply @is_linear_scal_l.
  apply (is_linear_comp (@snd _ _) (fun t : R => scal t ly)).
  by apply is_linear_snd.
  by apply @is_linear_scal_l.
  by apply @is_linear_plus.
  simpl => u Hu.
  replace u with (x,y) by now apply is_filter_lim_locally_unique.
  move => {u Hu} eps /=.
  move: (proj1 (locally_2d_locally _ _ _) (Df eps)).
  apply filter_imp => [[u v]] /= Huv.
  rewrite !(Rmult_comm (_-_)).
  eapply Rle_trans.
  apply Huv.
  apply Rmult_le_compat_l.
  by apply Rlt_le, eps.
  apply (norm_prod (u - x) (v - y)).
Qed.

Lemma differentiable_pt_lim_ext : forall f1 f2 x y lx ly,
  locally_2d (fun u v => f1 u v = f2 u v) x y ->
  differentiable_pt_lim f1 x y lx ly -> differentiable_pt_lim f2 x y lx ly.
Proof.
  intros f1 f2 x y lx ly H H1 eps.
  apply: locally_2d_impl (H1 eps) => {H1}.
  rewrite (locally_2d_singleton _ _ _ H).
  apply: locally_2d_impl H.
  apply locally_2d_forall.
  now intros u v ->.
Qed.

Definition differentiable_pt (f : R -> R -> R) (x y : R) :=
  exists lx, exists ly, differentiable_pt_lim f x y lx ly.

Lemma differentiable_continuity_pt : forall f x y,
  differentiable_pt f x y -> continuity_2d_pt f x y.
Proof.
  intros f x y (l1&l2&Df) eps ; simpl in Df.
  assert (0 < eps / 2).
    apply Rdiv_lt_0_compat ; [apply eps|apply Rlt_R0_R2].
    set (eps' := mkposreal _ H).
  elim (Df eps') ; clear Df ; intros d0 Df.
  assert (0 < Rmin (Rmin d0 1) (Rmin (eps/(4*Rmax (Rabs l1) 1)) (eps / (4* Rmax (Rabs l2) 1)))).
    apply Rmin_pos ; apply Rmin_pos.
    apply d0.
    apply Rlt_0_1.
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    apply Rdiv_lt_0_compat.
    apply eps.
    apply Rmult_lt_0_compat.
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (delta := mkposreal _ H0).
  exists delta ; intros x' y' H1 H2.
  rewrite (double_var eps).
  apply (Rle_lt_trans _ (Rabs (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y)))
    + Rabs (l1 * (x' - x) + l2 * (y' - y)))).
    assert (Rabs (f x' y' - f x y) =
      Rabs ((f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y))) +
      (l1 * (x' - x) + l2 * (y' - y)))).
      assert ((f x' y' - f x y) =
        (f x' y' - f x y - (l1 * (x' - x) + l2 * (y' - y)) +
        (l1 * (x' - x) + l2 * (y' - y)))).
        ring.
      rewrite <- H3 ; clear H3 ; reflexivity.
    rewrite H3 ; clear H3 ; apply Rabs_triang.
  apply Rplus_lt_le_compat.
  apply (Rle_lt_trans _ (eps' * Rmax (Rabs (x' - x)) (Rabs (y' - y)))).
  apply Df.
  apply (Rlt_le_trans _ _ _ H1) ; unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
  apply (Rlt_le_trans _ _ _ H2) ; unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
  rewrite <- (Rmult_1_r (eps/2)) ; unfold eps' ; simpl.
  apply Rmult_lt_compat_l.
  apply H.
  apply (Rlt_le_trans _ delta).
  apply (Rmax_lub_lt _ _ _ H1 H2).
  unfold delta ; simpl ;
  apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
  apply (Rle_trans _ (Rabs l1 * Rabs (x'-x) + Rabs l2 * Rabs (y'-y))).
    repeat rewrite <- Rabs_mult.
    apply Rabs_triang.
  rewrite (double_var (eps/2)).
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs l1 * delta)).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, H1.
  apply (Rle_trans _ (Rabs l1 * (Rmin (eps / (4 * Rmax (Rabs l1) 1))
                     (eps / (4 * Rmax (Rabs l2) 1))))).
    apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
  apply (Rle_trans _ (Rabs l1 * (eps / (4 * Rmax (Rabs l1) 1)))).
  apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_l].
  unfold Rmax ; destruct (Rle_dec (Rabs l1) 1).
  rewrite <- (Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rlt_le, Rdiv_lt_0_compat ;
  [apply eps | apply Rmult_lt_0_compat ;
  [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
  apply r.
  apply Req_le ; field.
  apply Req_le ; field.
  apply Rnot_le_lt in n.
  apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).

  apply (Rle_trans _ (Rabs l2 * delta)).
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  apply Rlt_le, H2.
  apply (Rle_trans _ (Rabs l2 * (Rmin (eps / (4 * Rmax (Rabs l1) 1))
                     (eps / (4 * Rmax (Rabs l2) 1))))).
    apply Rmult_le_compat_l ; unfold delta ; simpl ; [apply Rabs_pos| apply Rmin_r].
  apply (Rle_trans _ (Rabs l2 * (eps / (4 * Rmax (Rabs l2) 1)))).
  apply Rmult_le_compat_l ; [apply Rabs_pos | apply Rmin_r].
  unfold Rmax ; destruct (Rle_dec (Rabs l2) 1).
  rewrite <- (Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat.
  apply Rabs_pos.
  apply Rlt_le, Rdiv_lt_0_compat ;
  [apply eps | apply Rmult_lt_0_compat ;
  [apply Rmult_lt_0_compat ; apply Rlt_R0_R2|apply Rlt_0_1]].
  apply r.
  apply Req_le ; field.
  apply Req_le ; field.
  apply Rnot_le_lt in n.
  apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 n).
Qed.

Lemma differentiable_pt_lim_proj1_0 (f : R -> R) (x y l : R) :
  derivable_pt_lim f x l -> differentiable_pt_lim (fun u v => f u) x y l 0.
Proof.
  intros Df eps.
  apply is_derive_Reals in Df ;
  elim (proj2 Df x (fun P H => H) eps) ; clear Df ; intros delta Df.
  exists delta ; simpl ; intros.
  rewrite Rmult_0_l Rplus_0_r.
  apply (Rle_trans _ (eps * Rabs (u - x))).
  rewrite Rmult_comm ; apply (Df _ H).
  apply Rmult_le_compat_l.
  apply Rlt_le, eps.
  apply RmaxLess1.
Qed.

Lemma differentiable_pt_lim_proj1_1 (f : R -> R) (x y l : R) :
  differentiable_pt_lim (fun u v => f u) x y l 0 -> derivable_pt_lim f x l.
Proof.
  intros Df.
  apply is_derive_Reals ; split => [ | z Hz eps].
    by apply @is_linear_scal_l.
  rewrite -(is_filter_lim_locally_unique _ _ Hz) => {z Hz}.
  elim (Df eps) ; clear Df ; intros delta Df.
  exists delta ; simpl in Df ; simpl ; intros.
  rewrite /minus /plus /opp /scal /= /mult /=.
  replace (f y0 + - f x + - ((y0 + - x) * l)) with (f y0 - f x - (l * (y0 - x) + 0 * (y - y))) by ring.
  assert (Rabs (y0 - x) = Rmax (Rabs (y0 - x)) (Rabs (y-y))).
    rewrite Rmax_comm ; apply sym_equal, Rmax_right.
    rewrite Rminus_eq_0 Rabs_R0 ; apply Rabs_pos.
  rewrite /norm /= /abs /=.
  rewrite H0 ; clear H0.
  apply (Df _ _ H).
  rewrite Rminus_eq_0 Rabs_R0 ; apply delta.
Qed.

Lemma differentiable_pt_lim_unique (f : R -> R -> R) (x y : R) (lx ly : R) :
  differentiable_pt_lim f x y lx ly
    -> Derive (fun x => f x y) x = lx /\ Derive (fun y => f x y) y = ly.
Proof.
  move => Df ; split ; apply is_derive_unique, is_derive_Reals => e He ;
  case: (Df (pos_div_2 (mkposreal e He))) => {Df} delta /= Df ;
  exists delta => h Hh0 Hh.

  replace ((f (x + h) y - f x y) / h - lx)
    with ((f (x+h) y - f x y - (lx * ((x+h) - x) + ly * (y - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x + h - x)) (Rabs (y - y))).
  apply (Df (x+h) y).
  by (ring_simplify (x + h - x)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  ring_simplify (x + h - x).
  rewrite Rmax_left.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].

  replace ((f x (y + h) - f x y) / h - ly)
    with ((f x (y + h) - f x y - (lx * (x - x) + ly * ((y + h) - y))) / h)
    by (by field).
  rewrite Rabs_div.
  apply Rlt_div_l.
  by apply Rabs_pos_lt.
  apply Rle_lt_trans with (e / 2 * Rmax (Rabs (x - x)) (Rabs (y + h - y))).
  apply (Df x (y + h)).
  rewrite Rminus_eq_0 Rabs_R0 ; by apply delta.
  by (ring_simplify (y + h - y)).
  ring_simplify (y + h - y).
  rewrite Rmax_right.
  apply Rmult_lt_compat_r.
  by apply Rabs_pos_lt.
  lra.
  rewrite Rminus_eq_0 Rabs_R0 ; by apply Rabs_pos.
  by [].
Qed.

(** * Operations *)

Lemma differentiable_pt_lim_comp : forall f1 f2 f3 x y l1x l1y l2x l2y l3x l3y,
  differentiable_pt_lim f1 (f2 x y) (f3 x y) l1x l1y ->
  differentiable_pt_lim f2 x y l2x l2y -> differentiable_pt_lim f3 x y l3x l3y ->
  differentiable_pt_lim (fun u v => f1 (f2 u v) (f3 u v)) x y
    (l1x * l2x + l1y * l3x) (l1x * l2y + l1y * l3y).
Proof.
  intros f1 f2 f3 x y l1_1 l1_2 l2_1 l2_2 l3_1 l3_2
    Df1 Df2 Df3 eps ; simpl.
  assert (Cf2 : continuity_2d_pt f2 x y).
    apply differentiable_continuity_pt.
    exists l2_1 ; exists l2_2 ; apply Df2.
  assert (Cf3 : continuity_2d_pt f3 x y).
    apply differentiable_continuity_pt.
    exists l3_1 ; exists l3_2 ; apply Df3.
  assert (He2 : 0 < eps / (4 * Rmax (Rabs l1_1) 1)).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat].
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (eps2 := mkposreal _ He2).
  assert (He3 : 0 < eps / (4 * Rmax (Rabs l1_2) 1)).
    apply Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat].
    apply Rmult_lt_0_compat ; apply Rlt_R0_R2.
    apply (Rlt_le_trans _ _ _ Rlt_0_1 (RmaxLess2 _ _)).
    set (eps3 := mkposreal _ He3).
  assert (He1 : 0 < eps / (2 * Rmax (eps2 + Rabs l2_1 + Rabs l2_2)
    (eps3 + Rabs l3_1 + Rabs l3_2))).
    apply Rdiv_lt_0_compat ; [apply eps | apply Rmult_lt_0_compat].
    apply Rlt_R0_R2.
    apply (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
    rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
    apply eps2.
    apply Rplus_le_le_0_compat ; apply Rabs_pos.
    apply RmaxLess1.
    set (eps1 := mkposreal _ He1).
  elim (Df1 eps1) ; clear Df1 ; intros d0 Df1.
    elim (Cf2 d0) ; clear Cf2 ; intros d1 Cf2.
    elim (Cf3 d0) ; clear Cf3 ; intros d'1 Cf3.
  elim (Df2 eps2) ; clear Df2 ; intros d2 Df2.
  elim (Df3 eps3) ; clear Df3 ; intros d3 Df3.
  assert (Hd : 0 < Rmin (Rmin d1 d'1) (Rmin d2 d3)).
    apply Rmin_pos ; apply Rmin_pos ;
    [apply d1 | apply d'1 | apply d2 | apply d3].
    set (delta := mkposreal _ Hd).
  exists delta ; intros x' y' ; intros.
  apply (Rle_trans _ (Rabs (f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
    (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y)))
    + Rabs (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
    ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) + (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))))).
    replace ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) with
      ((f1 (f2 x' y') (f3 x' y') - f1 (f2 x y) (f3 x y) -
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y))) +
      (l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y)))) by ring.
    apply Rabs_triang.
  rewrite (double_var eps) (Rmult_plus_distr_r (eps/2)).
  apply Rplus_le_compat.
  apply (Rle_trans _ (eps1 * Rmax (Rabs (f2 x' y' - f2 x y)) (Rabs (f3 x' y' - f3 x y)))).
    apply Df1.
    apply Cf2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_l _ _)).
    apply Cf3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_l _ _) (Rmin_r _ _)).
  apply (Rle_trans _ (eps1 * (Rmax (eps2 + Rabs l2_1 + Rabs l2_2)
    (eps3 + Rabs l3_1 + Rabs l3_2) * Rmax (Rabs (x'-x)) (Rabs (y'-y))))).
    apply Rmult_le_compat_l.
    apply Rlt_le, eps1.
    rewrite Rmax_mult.
    apply Rmax_le_compat.
    rewrite Rplus_assoc Rmult_plus_distr_r.
    apply (Rle_trans _ (Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))
      + Rabs (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      assert (Rabs (f2 x' y' - f2 x y) =
      Rabs ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) +
      (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      assert ((f2 x' y' - f2 x y) =
      ((f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y))) +
      (l2_1 * (x' - x) + l2_2 * (y' - y)))).
      ring.
      rewrite <- H1 ; clear H1 ; reflexivity.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
    apply Rplus_le_compat.
    apply Df2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rle_trans _ (Rabs l2_1 * Rabs (x'-x) + Rabs l2_2 * Rabs (y'-y))).
      repeat rewrite <- Rabs_mult ; apply Rabs_triang.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat ; apply Rmult_le_compat_l.
      apply Rabs_pos.
      apply RmaxLess1.
      apply Rabs_pos.
      apply RmaxLess2.
  rewrite Rplus_assoc Rmult_plus_distr_r.
  apply (Rle_trans _ (Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y)))
      + Rabs (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      assert (Rabs (f3 x' y' - f3 x y) =
      Rabs ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) +
      (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      assert ((f3 x' y' - f3 x y) =
      ((f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))) +
      (l3_1 * (x' - x) + l3_2 * (y' - y)))).
      ring.
      rewrite <- H1 ; clear H1 ; reflexivity.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
    apply Rplus_le_compat.
    apply Df3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rle_trans _ (Rabs l3_1 * Rabs (x'-x) + Rabs l3_2 * Rabs (y'-y))).
      repeat rewrite <- Rabs_mult ; apply Rabs_triang.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat ; apply Rmult_le_compat_l.
      apply Rabs_pos.
      apply RmaxLess1.
      apply Rabs_pos.
      apply RmaxLess2.
  apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
  simpl ; apply Req_le ; field.
  apply sym_not_eq, Rlt_not_eq, (Rlt_le_trans _ (eps2 + Rabs l2_1 + Rabs l2_2)).
  rewrite Rplus_assoc ; apply Rplus_lt_le_0_compat.
  apply eps2.
  apply Rplus_le_le_0_compat ; apply Rabs_pos.
  apply RmaxLess1.
  rewrite (double_var (eps/2)) (Rmult_plus_distr_r (eps/2/2)).
  apply (Rle_trans _ (Rabs l1_1 * Rabs (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))
    + Rabs l1_2 * Rabs (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
    repeat rewrite <- Rabs_mult.
    assert ((l1_1 * (f2 x' y' - f2 x y) + l1_2 * (f3 x' y' - f3 x y) -
      ((l1_1 * l2_1 + l1_2 * l3_1) * (x' - x) +
      (l1_1 * l2_2 + l1_2 * l3_2) * (y' - y))) =
      (l1_1 * (f2 x' y' - f2 x y - (l2_1 * (x' - x) + l2_2 * (y' - y)))) +
      (l1_2 * (f3 x' y' - f3 x y - (l3_1 * (x' - x) + l3_2 * (y' - y))))).
      ring.
    rewrite H1 ; clear H1 ; apply Rabs_triang.
  apply Rplus_le_compat.
  apply (Rle_trans _ (Rabs l1_1 * (eps2 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Df2.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_l _ _)).
    rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
    apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
    unfold eps2, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_1) 1).
    rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
    apply Rabs_pos.
    rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
    apply r.
    apply Req_le ; field.
    apply Req_le ; field.
    apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
  apply (Rle_trans _ (Rabs l1_2 * (eps3 * Rmax (Rabs (x' - x)) (Rabs (y' - y))))).
    apply Rmult_le_compat_l.
    apply Rabs_pos.
    apply Df3.
    apply (Rlt_le_trans _ _ _ H) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    apply (Rlt_le_trans _ _ _ H0) ; simpl ;
    apply (Rle_trans _ _ _ (Rmin_r _ _) (Rmin_r _ _)).
    rewrite <- Rmult_assoc ; apply Rmult_le_compat_r.
    apply (Rle_trans _ _ _ (Rabs_pos _) (RmaxLess1 _ _)).
    unfold eps3, Rmax ; simpl ; destruct (Rle_dec (Rabs l1_2) 1).
    rewrite <- (Rmult_1_l (eps/2/2)) ; apply Rmult_le_compat.
    apply Rabs_pos.
    rewrite Rmult_1_r ; apply Rlt_le, Rdiv_lt_0_compat ;
    [apply eps | apply Rmult_lt_0_compat ; apply Rlt_R0_R2].
    apply r.
    apply Req_le ; field.
    apply Req_le ; field.
    apply sym_not_eq, Rlt_not_eq, (Rlt_trans _ _ _ Rlt_0_1 (Rnot_le_lt _ _ n)).
Qed.

Lemma derivable_pt_lim_comp_2d : forall f1 f2 f3 x l1x l1y l2 l3,
  differentiable_pt_lim f1 (f2 x) (f3 x) l1x l1y ->
  derivable_pt_lim f2 x l2 -> derivable_pt_lim f3 x l3 ->
  derivable_pt_lim (fun t => f1 (f2 t) (f3 t)) x (l1x * l2 + l1y * l3).
Proof.
  intros.
  apply (differentiable_pt_lim_proj1_1 _ x 0 (l1x * l2 + l1y * l3)).
  pattern 0 at 2 ; replace 0 with (l1x * 0 + l1y * 0) by ring.
  apply differentiable_pt_lim_comp.
  apply H.
  apply: differentiable_pt_lim_proj1_0 H0.
  apply: differentiable_pt_lim_proj1_0 H1.
Qed.

(** * Partial derivatives *)

Definition partial_derive (m k : nat) (f : R -> R -> R) : R -> R -> R :=
  fun x y => Derive_n (fun t => Derive_n (fun z => f t z) k y) m x.

Definition differential (p : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0
    (fun m =>
      C p m *
      partial_derive m (p - m)%nat f x y *
      dx ^ m * dy ^ (p - m)%nat)
    p.

Definition DL_pol (n : nat) (f : R -> R -> R) (x y dx dy : R) : R :=
  sum_f_R0
    (fun p =>
      differential p f x y dx dy / INR (fact p))
    n.

Lemma partial_derive_ext_loc :
  forall f g p q x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  partial_derive p q f x y = partial_derive p q g x y.
Proof.
intros f g p q x y H.
unfold partial_derive.
apply Derive_n_ext_loc.
destruct H as (e,He).
exists e.
intros u Hu.
apply Derive_n_ext_loc.
exists e.
intros v Hv.
now apply He.
Qed.

(** * Schwarz theorem *)

Lemma Schwarz_aux :
  forall f x y (eps : posreal),
  ( forall u v, Rabs (u - x) < eps -> Rabs (v - y) < eps ->
    ex_derive (fun z : R => f z v) u /\
    ex_derive (fun z : R => Derive (fun t => f t z) u) v ) ->
  forall h k, Rabs h < eps -> Rabs k < eps ->
  let phi k x := f x (y + k) - f x y in
  exists u, exists v,
  Rabs (u - x) <= Rabs h /\ Rabs (v - y) <= Rabs k /\
  phi k (x + h) - phi k x = h * k * (Derive (fun z => Derive (fun t => f t z) u) v).
Proof.
intros f x y eps HD h k Hh Hk phi.
assert (Hx: x + h - x = h) by ring.
assert (Hy: y + k - y = k) by ring.
(* . *)
destruct (MVT_cor4 (phi k) (Derive (phi k)) x (Rabs h)) with (b := x + h) as (u&Hu1&Hu2).
intros c Hc.
apply Derive_correct.
apply: ex_derive_minus.
apply (HD c).
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply (HD c).
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
rewrite Hx.
apply Rle_refl.
rewrite Hx in Hu1, Hu2.
exists u.
(* . *)
destruct (MVT_cor4 (fun v => Derive (fun t => f t v) u) (Derive (fun v => Derive (fun t => f t v) u)) y (Rabs k)) with (b := y + k) as (v&Hv1&Hv2).
intros c Hc.
apply Derive_correct, HD.
now apply Rle_lt_trans with (Rabs h).
now apply Rle_lt_trans with (1 := Hc).
rewrite Hy.
apply Rle_refl.
rewrite Hy in Hv1, Hv2.
exists v.
(* . *)
refine (conj Hu2 (conj Hv2 _)).
rewrite Hu1 /phi Derive_minus.
rewrite Hv1.
ring.
apply (HD u).
now apply Rle_lt_trans with (Rabs h).
now rewrite Hy.
apply (HD u).
now apply Rle_lt_trans with (Rabs h).
rewrite /Rminus Rplus_opp_r Rabs_R0.
apply cond_pos.
Qed.

Lemma Schwarz :
  forall (f : R -> R -> R) x y,
  locally_2d (fun u v =>
    ex_derive (fun z : R => f z v) u /\
    ex_derive (fun z : R => f u z) v /\
    ex_derive (fun z : R => Derive (fun t => f z t) v) u /\
    ex_derive (fun z : R => Derive (fun t => f t z) u) v) x y ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => f z t) v) u) x y ->
  continuity_2d_pt (fun u v => Derive (fun z => Derive (fun t => f t z) u) v) x y ->
  Derive (fun z => Derive (fun t => f z t) y) x = Derive (fun z => Derive (fun t => f t z) x) y.
Proof.
intros f x y (eps, HD) HC2 HC1.
refine ((fun H1 => _) (Schwarz_aux f x y eps _)).
2: intros u v Hu Hv ; split ; now apply (HD u v).
refine ((fun H2 => _ )(Schwarz_aux (fun x y => f y x) y x eps _)).
2: intros u v Hu Hv ; split ; now apply (HD v u).
simpl in H1, H2.
apply Req_lt_aux.
intros e.
destruct (HC1 (pos_div_2 e)) as (d1,Hc1).
destruct (HC2 (pos_div_2 e)) as (d2,Hc2).
set (d := Rmin (Rmin (pos_div_2 d1) (pos_div_2 d2)) (pos_div_2 eps)).
assert (Hd: d > 0).
apply Rmin_glb_lt.
apply Rmin_stable_in_posreal.
apply cond_pos.
assert (K: Rabs d < eps).
rewrite Rabs_right.
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps eps).
apply cond_pos.
now apply Rgt_ge.
specialize (H1 d d K K).
specialize (H2 d d K K).
destruct H1 as (u1&v1&Hu1&Hv1&H1).
destruct H2 as (v2&u2&Hv2&Hu2&H2).
clear K.
rewrite (Rabs_right d (Rgt_ge _ _ Hd)) in Hu1 Hv1 Hu2 Hv2.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d1).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply (Rlt_eps2_eps d1).
apply cond_pos.
specialize (Hc1 u1 v1 (K _ _ Hu1) (K _ _ Hv1)).
clear K.
assert (K: forall a b, Rabs (a - b) <= d -> Rabs (a - b) < d2).
intros a b H.
apply Rle_lt_trans with (1 := H).
apply Rle_lt_trans with (1 := Rmin_l _ _).
apply Rle_lt_trans with (1 := Rmin_r _ _).
apply (Rlt_eps2_eps d2).
apply cond_pos.
specialize (Hc2 u2 v2 (K _ _ Hu2) (K _ _ Hv2)).
clear -Hd H1 H2 Hc1 Hc2.
assert (H: forall a b c, b - c = -(a - b) + (a - c)) by (intros ; ring).
rewrite (H (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2)).
clear H.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite Rabs_Ropp (double_var e).
apply Rplus_lt_compat.
exact Hc2.
replace (Derive (fun z : R => Derive (fun t : R => f z t) v2) u2) with
  (Derive (fun z : R => Derive (fun t : R => f t z) u1) v1).
exact Hc1.
apply Rmult_eq_reg_l with (d * d).
rewrite -H1 -H2.
ring.
apply Rgt_not_eq.
now apply Rmult_gt_0_compat.
Qed.

Lemma partial_derive_add_zero: forall f p q r s x y,
  (q=0)%nat \/ (r=0)%nat ->
  partial_derive p q (partial_derive r s f) x y
   = partial_derive (p+r) (q+s) f x y.
intros f p q r s x y H.
destruct H; rewrite H.
rewrite plus_0_l.
unfold partial_derive.
simpl.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
rewrite plus_0_r.
unfold partial_derive.
simpl.
apply Derive_n_ext.
intros y0.
rewrite -Derive_n_comp.
now apply Derive_n_ext.
Qed.


(** * Iterated differential *)

Fixpoint ex_diff_n f n x y :=
  continuity_2d_pt f x y /\
  match n with
  | O => True
  | S n =>
    ex_derive (fun z => f z y) x /\
    ex_derive (fun z => f x z) y /\
    ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y /\
    ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y
  end.

Lemma ex_diff_n_ext_loc: forall f g n x y,
    locally_2d (fun u v =>  f u v = g u v) x y
      -> ex_diff_n f n x y -> ex_diff_n g n x y.
Proof.
intros f g n; revert f g.
induction n.
intros f g x y H; simpl.
intros (H1,_); split.
apply (continuity_2d_pt_ext_loc _ _ _ _ H H1).
easy.
simpl.
intros f g x y H (H1&H2&H3&H4&H5).
split.
apply (continuity_2d_pt_ext_loc _ _ _ _ H H1).
split.
apply: ex_derive_ext_loc H2.
apply locally_2d_1d_const_y with (1:=H).
split.
apply: ex_derive_ext_loc H3.
apply locally_2d_1d_const_x with (1:=H).
split.
apply IHn with (2:=H4).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_y with (1:=H6).
apply IHn with (2:=H5).
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H6.
apply Derive_ext_loc.
apply locally_2d_1d_const_x with (1:=H6).
Qed.

Lemma ex_diff_n_m :
  forall n m, (m <= n)%nat -> forall f x y, ex_diff_n f n x y -> ex_diff_n f m x y.
Proof.
assert (forall n f x y, ex_diff_n f (S n) x y -> ex_diff_n f n x y).
induction n.
simpl.
intros f x y H; split; try apply H.
intros f x y H.
repeat (split; try apply H).
apply IHn.
apply H.
apply IHn.
apply H.
intros n m H1 f x y Hn.
induction n.
replace m with 0%nat.
exact Hn.
now apply le_n_0_eq.
case (le_lt_or_eq _ _ H1).
intros H2; apply IHn.
now apply gt_S_le.
apply (H _ _ _ _ Hn).
intros H2; now rewrite H2.
Qed.

Lemma ex_diff_n_deriv_aux1: forall f n x y,
  ex_diff_n f (S n) x y -> ex_diff_n (fun u v => Derive (fun z => f z v) u) n x y.
Proof.
intros f n x y.
case n.
simpl.
intros H; split; apply H.
clear n;intros n H.
simpl in H.
repeat split; apply H.
Qed.

Lemma ex_diff_n_deriv_aux2: forall f n x y,
  ex_diff_n f (S n) x y -> ex_diff_n (fun u v => Derive (fun z => f u z) v) n x y.
Proof.
intros f n x y.
case n.
simpl.
intros H; split; apply H.
clear n;intros n H.
simpl in H.
repeat split; apply H.
Qed.

Lemma ex_diff_n_deriv: forall n p q, (p+q <= n)%nat -> forall f x y,
    ex_diff_n f n x y-> ex_diff_n (partial_derive p q f) (n -(p+q)) x y.
induction p.
(* . *)
intros q; rewrite plus_0_l.
induction q.
intros H f x y H1.
unfold partial_derive.
simpl.
rewrite - minus_n_O.
apply: (ex_diff_n_ext_loc _ _ _ _ _ _ H1).
now apply locally_2d_forall.
intros H f x y H1.
apply (ex_diff_n_ext_loc (fun u v => Derive (fun z => (partial_derive 0 q f) u z) v)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux2.
replace ((S (n - S q))) with (n-q)%nat by omega.
apply IHq.
now apply lt_le_weak.
exact H1.
(* . *)
intros q H f x y H1.
apply (ex_diff_n_ext_loc (fun u v => Derive (fun z => (partial_derive p q f) z v) u)).
apply locally_2d_forall.
intros u v; unfold partial_derive.
reflexivity.
apply ex_diff_n_deriv_aux1.
replace ((S (n - (S p +q)))) with (n-(p+q))%nat by omega.
apply IHp.
now apply lt_le_weak.
exact H1.
Qed.

Lemma ex_diff_n_ex_deriv_inf_1 : forall n p k, (p+k < n)%nat -> forall f x y,
    ex_diff_n f n x y ->
    ex_derive  (fun z : R => partial_derive p k f z y) x.
Proof.
intros n p; case p; clear p.
(* . *)
intros k; case k; clear k.
case n; clear n.
intros Hn; contradict Hn; apply lt_n_O.
intros n _ f x y H.
unfold partial_derive; simpl.
apply H.
intros n0 H f x y Hf.
assert (ex_diff_n (partial_derive 0 n0 f) (n -(0+n0)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
revert H0; rewrite plus_0_l.
case_eq (n-n0)%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1 H2.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive 0 n0 f z) t) y).
intros y0; unfold partial_derive; simpl.
reflexivity.
simpl in H2.
destruct H2 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T5.
apply T5.
(* . *)
intros p q H f x y Hf.
assert (ex_diff_n (partial_derive p q f) (n -(p+q)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
case_eq (n-(p+q))%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive p q f t) y) z).
intros x0; unfold partial_derive; simpl.
reflexivity.
rewrite H1 in H0; simpl in H0.
destruct H0 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T4.
apply T4.
Qed.

Lemma ex_diff_n_ex_deriv_inf_2 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y ->
  ex_derive (fun z => partial_derive p k f x z) y.
Proof.
intros n p; case p; clear p.
(* . *)
intros k; case k; clear k.
case n; clear n.
intros Hn; contradict Hn; apply lt_n_O.
intros n _ f x y H.
unfold partial_derive; simpl.
apply H.
intros n0 H f x y Hf.
assert (ex_diff_n (partial_derive 0 n0 f) (n -(0+n0)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
revert H0; rewrite plus_0_l.
case_eq (n-n0)%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1 H2.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive 0 n0 f x) t) z).
intros y0; unfold partial_derive; simpl.
reflexivity.
simpl in H2.
destruct H2 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T5.
apply T5.
(* . *)
intros p q H f x y Hf.
assert (ex_diff_n (partial_derive p q f) (n -(p+q)) x y).
apply ex_diff_n_deriv.
auto with zarith.
exact Hf.
case_eq (n-(p+q))%nat.
intros H1; contradict H; auto with zarith.
intros n1 H1.
apply ex_derive_ext with (fun z => Derive (fun t => (partial_derive p q f t) z) x).
intros x0; unfold partial_derive; simpl.
reflexivity.
rewrite H1 in H0; simpl in H0.
destruct H0 as (T1&T2&T3&T4&T5).
case_eq n1.
intros H2; rewrite H2 in H1.
clear -H H1; contradict H; auto with zarith.
intros n2 Hn2; rewrite Hn2 in T4.
apply T4.
Qed.

Lemma ex_diff_n_continuity_inf_1 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y ->
  continuity_2d_pt (fun u v => Derive (fun z : R => partial_derive p k f z v) u) x y.
Proof.
intros n p k Hn f x y Hf.
assert (ex_diff_n (partial_derive (S p) k f) (n -(S p+k)) x y).
now apply ex_diff_n_deriv.
apply continuity_2d_pt_ext_loc with (partial_derive (S p) k f).
apply locally_2d_forall.
intros u v; unfold partial_derive; simpl.
reflexivity.
revert H; case (n - (S p + k))%nat.
simpl; intros H; apply H.
intros n0; simpl; intros H; apply H.
Qed.

Lemma Derive_partial_derive_aux1: forall p f x y,
  locally_2d (ex_diff_n f (S p)) x y ->
   partial_derive  1 p f x y = partial_derive 0 p (partial_derive  1 0 f) x y.
Proof.
intros p; induction p.
intros f x y H.
unfold partial_derive; now simpl.
intros f x y H.
apply trans_eq with  (partial_derive 1 p (partial_derive 0 1 f) x y).
unfold partial_derive.
simpl.
apply Derive_ext.
intros t.
apply trans_eq with (Derive_n (Derive_n (fun z : R => f t z) p) 1 y).
reflexivity.
rewrite Derive_n_comp.
rewrite Arith.Plus.plus_comm.
rewrite -Derive_n_comp.
reflexivity.
rewrite IHp.
apply trans_eq with
  (partial_derive 0 p (partial_derive 0 1 (partial_derive 1 0 f)) x y).
unfold partial_derive.
simpl.
apply Derive_n_ext_loc.
cut (locally_2d (fun u v =>
         Derive (fun x0 : R => Derive (fun x1 : R => f x0 x1) v) u =
         Derive (fun x0 : R => Derive (fun x1 : R => f x1 x0) u) v) x y).
apply locally_2d_1d_const_x.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u v H1.
apply Schwarz.
apply locally_2d_impl with (2:=H1).
apply locally_2d_forall.
intros u' v' H2.
split.
apply H2.
split.
apply H2.
simpl in H2; destruct H2 as (T1&T2&T3&T4&T5).
split.
apply T5.
apply T4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T5 as (Y1&Y2&Y3&Y4&Y5).
clear - Y4.
case p in Y4; simpl in Y4; apply Y4.
apply locally_2d_singleton in H1.
simpl in H1; destruct H1 as (T1&T2&T3&T4&T5).
destruct T4 as (Y1&Y2&Y3&Y4&Y5).
clear - Y5.
case p in Y5; simpl in Y5; apply Y5.
unfold partial_derive.
simpl.
apply trans_eq with (Derive_n (Derive_n (fun z => Derive (fun x0 => f x0 z) x) p) 1 y).
rewrite Derive_n_comp.
rewrite Arith.Plus.plus_comm.
rewrite -Derive_n_comp.
reflexivity.
reflexivity.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u v.
pattern (S p) at 2; replace (S p) with (S (S p) -(0+1))%nat.
apply ex_diff_n_deriv.
rewrite plus_0_l.
apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_l.
omega.
Qed.

Lemma Derive_partial_derive_aux2: forall p k f x y,
  locally_2d (ex_diff_n f (p+S k)) x y ->
  partial_derive 0 1 (partial_derive p k f) x y =
     partial_derive p (S k) f x y.
Proof.
intros p; induction p.
intros; easy.
intros k f x y Y.
apply sym_eq.
apply trans_eq with
  (partial_derive p 0 (partial_derive 1 (S k) f) x y).
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply Arith.Plus.plus_comm.
easy.
now left.
apply trans_eq with
  (partial_derive p 0 (partial_derive 0 (S k) (partial_derive 1 0 f)) x y).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply Derive_partial_derive_aux1.
apply locally_2d_impl with (2:=H).
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
omega.
apply trans_eq with (partial_derive p (S k) (partial_derive 1 0 f) x y).
rewrite partial_derive_add_zero.
now rewrite plus_0_l plus_0_r.
now right.
rewrite - IHp.
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=Y).
apply locally_2d_forall.
intros u v H.
apply trans_eq with
 (partial_derive p 0 (partial_derive 0 k (partial_derive 1 0 f)) u v).
rewrite (partial_derive_add_zero _ _ 0%nat).
now rewrite plus_0_l plus_0_r.
now right.
apply trans_eq with
 (partial_derive p 0 (partial_derive 1 k f) u v).
apply partial_derive_ext_loc.
apply locally_2d_impl_strong with (2:=H).
apply locally_2d_forall.
intros u' v' H'.
apply sym_eq.
apply Derive_partial_derive_aux1.
apply locally_2d_impl with (2:=H').
apply locally_2d_forall.
intros u'' v''.
apply ex_diff_n_m.
apply le_plus_r.
rewrite partial_derive_add_zero.
rewrite plus_0_l.
replace (S p) with (p+1)%nat by apply Arith.Plus.plus_comm.
easy.
now left.
apply locally_2d_impl with (2:=Y).
apply locally_2d_forall.
intros u'' v''.
replace (p+ S k)%nat with ((S p+S k)-(1+0))%nat.
apply ex_diff_n_deriv.
rewrite plus_0_r.
apply le_plus_trans; apply lt_le_S; apply lt_0_Sn.
rewrite plus_0_r.
omega.
Qed.

Lemma Derive_partial_derive: forall p k f x y,
  locally_2d (ex_diff_n f (p+S k)) x y ->
  Derive (fun v : R => partial_derive p k f x v) y =
     partial_derive p (S k) f x y.
Proof.
intros p k f x y H.
generalize (Derive_partial_derive_aux2 p k f x y H).
easy.
Qed.

Lemma ex_diff_n_continuity_inf_2 : forall n p k, (p+k < n)%nat -> forall f x y,
  ex_diff_n f n x y ->
  continuity_2d_pt (fun u v => Derive (fun z : R => partial_derive p k f u z) v) x y.
Proof.
intros n p k Hn f x y Hf.
assert (ex_diff_n (partial_derive p k f) (n -(p+k)) x y).
apply ex_diff_n_deriv.
now apply lt_le_weak.
exact Hf.
revert H; case_eq (n-(p+k))%nat.
intros H; contradict Hn.
omega.
intros n0 Hn0; simpl; intros (T1&T2&T3&T4&T5).
revert T5; case n0.
intros Y; apply Y.
intros n1 Y; apply Y.
Qed.

(** * 2D Taylor-Lagrange inequality *)

Definition DL_regular_n f m x y :=
  exists D, locally_2d (fun u v =>
    Rabs (f u v - DL_pol m f x y (u-x) (v-y)) <= D * (Rmax (Rabs (u-x)) (Rabs (v-y))) ^ (S m)) x y.

Theorem Taylor_Lagrange_2d : forall f n x y,
  locally_2d (fun u v => ex_diff_n f (S n) u v) x y -> DL_regular_n f n x y.
Proof.
intros f n x y Df.
(* *)
assert (exists D, locally_2d (fun u v => forall p, (p <= S n)%nat ->
  Rabs (partial_derive p (S n - p) f u v) <= D) x y).
(* . *)
assert (forall p, (p <= S n)%nat -> exists D, locally_2d (fun u v => Rabs (partial_derive p (S n - p) f u v) <= D) x y).
intros p Hp.
(* .. *)
assert (continuity_2d_pt (partial_derive p (S n - p) f) x y).
apply locally_2d_singleton in Df.
refine (proj1 (_: ex_diff_n (partial_derive p (S n - p) f) 0 x y)).
replace O with (S n - (p + (S n - p)))%nat by rewrite le_plus_minus_r // minus_diag //.
cut (p + (S n - p) <= S n)%nat.
2: now rewrite le_plus_minus_r.
generalize (S n - p)%nat.
clear Hp.
revert f Df p.
generalize (S n).
clear n.
induction n.
intros f (H,_) [|p] [|q] H' ; try inversion H'.
done.
intros f H [|p] q H'.
destruct q as [|q].
exact H.
now apply ex_diff_n_deriv.
now apply ex_diff_n_deriv.
(* .. *)
exists (Rabs (partial_derive p (S n - p) f x y) + 1).
specialize (H (mkposreal 1 Rlt_0_1)).
apply: locally_2d_impl H.
apply: locally_2d_forall => u v H.
replace (partial_derive p (S n - p) f u v) with (partial_derive p (S n - p) f x y + (partial_derive p (S n - p) f u v - partial_derive p (S n - p) f x y)) by ring.
apply Rle_trans with (1 := Rabs_triang _ _).
apply Rplus_le_compat_l.
now apply Rlt_le.
(* . *)
clear -H.
generalize (le_refl (S n)).
generalize (S n) at 1 3.
intros p Hp.
induction p.
move: (H _ Hp) => {H} [D H].
exists D.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H [|p] Hp' //.
inversion Hp'.
move: (IHp (le_S _ _ (le_S_n _ _ Hp))) => {IHp} [D1 H1].
move: (H _ Hp) => {H} [D2 H2].
exists (Rmax D1 D2).
move: (locally_2d_and _ _ x y H1 H2) => {H1 H2} H.
apply: locally_2d_impl H.
apply locally_2d_forall => u v H p' Hp'.
destruct (le_lt_or_eq _ _ Hp').
apply Rle_trans with (2 := Rmax_l _ _).
apply H.
now apply gt_S_le.
apply Rle_trans with (2 := Rmax_r _ _).
now rewrite H0.
(* *)
destruct H as (D,H).
exists  (/ INR (fact (S n)) * D * sum_f_R0 (fun i : nat => Rabs (C (S n) i)) (S n)).
move: (locally_2d_and _ _ _ _ Df H) => {Df H} HH.
apply locally_2d_1d_strong in HH.
apply: locally_2d_impl HH.
apply locally_2d_forall => u v HH.
set (g t := f (x + t * (u - x)) (y + t * (v - y))).
replace (f u v) with (g 1) by (rewrite /g 2!Rmult_1_l ; apply f_equal2 ; ring).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 ->
  is_derive_n g k t (sum_f_R0 (fun m => C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) *
         (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t Hk Ht.
specialize (HH t Ht).
revert HH.
pattern t ; apply locally_singleton.
induction k.
rewrite /C /partial_derive /g /=.
apply filter_forall.
intros ; field.
specialize (IHk (le_S _ _ (le_S_n _ _ Hk))).
rewrite /is_derive_n.
apply locally_locally in IHk.
move: IHk ; apply filter_imp => {t Ht} z IHk HH.
apply is_derive_ext_loc with (fun t => sum_n (fun m => C k m *
  partial_derive m (k - m) f (x + t * (u - x)) (y + t * (v - y)) * (u - x) ^ m * (v - y) ^ (k - m)) k).
  apply locally_locally in HH.
  generalize (filter_and _ _ HH IHk).
  apply filter_imp => {z HH IHk} z [Hz HH].
  specialize (HH Hz).
  apply sym_eq.
  rewrite sum_n_Reals.
  now apply is_derive_n_unique.
replace (sum_f_R0 (fun m : nat => C (S k) m *
    partial_derive m (S k - m) f (x + z * (u - x)) (y + z * (v - y)) * (u - x) ^ m * (v - y) ^ (S k - m)) (S k)) with
  (sum_n (fun m : nat => C k m * (u - x) ^ m  * (v - y) ^ (k - m) *
    ((u - x) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) +
     (v - y) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))) k).
apply: is_derive_sum_n => p Hp.
apply is_derive_ext with (fun u0 => C k p * (u - x) ^ p * (v - y) ^ (k - p) * partial_derive p (k - p) f (x + u0 * (u - x)) (y + u0 * (v - y))).
intros w.
simpl ; ring.
apply is_derive_Reals, derivable_pt_lim_scal.
rewrite (Rmult_comm (u - x)) (Rmult_comm (v - y)).
apply derivable_pt_lim_comp_2d.
apply locally_singleton in HH.
replace (partial_derive (S p) (k - p) f (x + z * (u - x)) (y + z * (v - y)))
  with (Derive (fun u : R => partial_derive p (k - p) f u (y + z * (v - y))) (x + z * (u - x))).
2: reflexivity.
replace (partial_derive p (S (k - p)) f (x + z * (u - x)) (y + z * (v - y))) with
  (Derive (fun v : R => partial_derive p (k - p) f  (x + z * (u - x)) v) (y + z * (v - y))).
apply filterdiff_differentiable_pt_lim.
eapply filterdiff_ext_lin.
apply is_derive_filterdiff.
apply locally_2d_locally in HH.
apply filter_imp with (2:=HH).
clear - Hk Hp ; intros [u' v'] (H1,H2).
evar_last.
apply Derive_correct.
apply ex_diff_n_ex_deriv_inf_1 with (S n).
now rewrite - le_plus_minus.
exact H1.
simpl ; reflexivity.
apply locally_2d_singleton in HH.
apply Derive_correct.
apply ex_diff_n_ex_deriv_inf_2 with (S n).
now rewrite - le_plus_minus.
apply HH.
apply locally_2d_singleton in HH.
apply continuity_2d_pt_filterlim.
apply ex_diff_n_continuity_inf_1 with (S n).
now rewrite - le_plus_minus.
apply HH.
case => /= u' v'.
reflexivity.
apply Derive_partial_derive_aux2.
apply locally_2d_impl with (2:=HH).
apply locally_2d_forall.
intros u' v' (Y,_).
apply ex_diff_n_m with (2:=Y).
omega.
apply is_derive_Reals ; eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_l ; try apply locally_filter.
simpl => y0 ; apply plus_zero_l.
apply is_derive_Reals ; eapply filterdiff_ext_lin.
apply @filterdiff_plus_fct ; try apply locally_filter.
apply filterdiff_const.
apply @filterdiff_scal_l ; try apply locally_filter.
simpl => y0 ; apply plus_zero_l.
rewrite sum_n_Reals -(sum_eq (fun m =>
  C k m * (u - x) ^ (S m) * (v - y) ^ (k - m) * partial_derive (S m) (k - m) f (x + z * (u - x)) (y + z * (v - y)) +
  C k m * (u - x) ^ m * (v - y) ^ (S (k - m)) * partial_derive m (S (k - m)) f (x + z * (u - x)) (y + z * (v - y)))).
2: intros ; simpl ; ring.
case k; clear Hk IHk k.
unfold C; simpl.
simpl ; field.
intros k.
apply sym_eq.
rewrite (decomp_sum _ (S (S k))).
2: apply lt_0_Sn.
rewrite - pred_Sn.
rewrite tech5.
rewrite (sum_eq _ (fun i : nat =>
     (C (S k) i*
    partial_derive (S i) (S (S k) - S i) f (x + z * (u - x))
      (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i))
     + (C (S k) (S i) *
       partial_derive (S i) (S (S k) - S i) f (x + z * (u - x))
      (y + z * (v - y)) * (u - x) ^ S i * (v - y) ^ (S (S k) - S i)))).
rewrite sum_plus.
apply sym_eq.
rewrite sum_plus.
rewrite tech5.
rewrite (tech2 _ 0 (S k)).
2: apply lt_0_Sn.
replace
 (sum_f_R0
   (fun l : nat =>
    C (S k) l * (u - x) ^ l * (v - y) ^ S (S k - l) *
    partial_derive l (S (S k - l)) f (x + z * (u - x)) (y + z * (v - y))) 0)
with  (C (S (S k)) 0 *
partial_derive 0 (S (S k) - 0) f (x + z * (u - x)) (y + z * (v - y)) *
(u - x) ^ 0 * (v - y) ^ (S (S k) - 0)).
replace (C (S k) (S k) * (u - x) ^ S (S k) * (v - y) ^ (S k - S k) *
   partial_derive (S (S k)) (S k - S k) f (x + z * (u - x)) (y + z * (v - y))) with
 (C (S (S k)) (S (S k)) *
 partial_derive (S (S k)) (S (S k) - S (S k)) f (x + z * (u - x))
   (y + z * (v - y)) * (u - x) ^ S (S k) * (v - y) ^ (S (S k) - S (S k))).
replace (sum_f_R0
  (fun l : nat =>
   C (S k) l *
   partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) *
   (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k)
  with (sum_f_R0
  (fun l : nat =>
   C (S k) l * (u - x) ^ S l * (v - y) ^ (S k - l) *
   partial_derive (S l) (S k - l) f (x + z * (u - x)) (y + z * (v - y))) k).
replace (sum_f_R0
  (fun l : nat =>
   C (S k) (S l) *
   partial_derive (S l) (S (S k) - S l) f (x + z * (u - x)) (y + z * (v - y)) *
   (u - x) ^ S l * (v - y) ^ (S (S k) - S l)) k)
 with (sum_f_R0
  (fun i : nat =>
   C (S k) (1 + i) * (u - x) ^ (1 + i) * (v - y) ^ S (S k - (1 + i)) *
   partial_derive (1 + i) (S (S k - (1 + i))) f (x + z * (u - x))
     (y + z * (v - y))) (S k - 1)).
simpl ; ring.
replace (S k - 1)%nat with k. 2: now apply plus_minus.
apply sum_eq.
intros i Hi.
replace (1+i)%nat with (S i) by reflexivity.
replace (S (S k - S i))%nat with (S (S k) - S i)%nat.
ring.
now (rewrite minus_Sn_m; try apply le_n_S).
apply sum_eq.
intros i Hi.
replace (S k - i)%nat with (S (S k) - S i)%nat by reflexivity.
ring.
rewrite 2!C_n_n 2!minus_diag.
ring.
simpl.
rewrite 2!C_n_0.
ring.
intros.
rewrite - (pascal (S k) i).
ring.
now apply le_lt_n_Sm.
(* *)
destruct (Taylor_Lagrange g n 0 1 Rlt_0_1) as (t&Ht&Hg).
intros t Ht.
intros [|k] Hk.
easy.
eexists.
now apply (H (S k)).
(* *)
rewrite Hg /DL_pol.
replace (1 - 0) with 1 by ring.
rewrite pow1 {1}/Rminus Rplus_assoc [_*_+_]Rplus_comm -Rplus_assoc -/(Rminus _ _).
assert (forall k t, (k <= S n)%nat -> 0 <= t <= 1 -> Derive_n g k t =
      (sum_f_R0 (fun m =>  C k m * partial_derive m (k - m)%nat f (x+t*(u-x)) (y+t*(v-y)) *
         (u-x) ^ m * (v-y) ^ (k - m)%nat) k)).
intros k t0 Hk Ht0.
apply is_derive_n_unique.
now apply H.
rewrite -minus_sum sum_eq_R0.
rewrite H0.
rewrite Rplus_0_l.
unfold differential.
rewrite Rabs_mult.
eapply Rle_trans.
apply Rmult_le_compat_l.
apply Rabs_pos.
eapply Rle_trans.
apply Rsum_abs.
apply sum_Rle.
intros n0 Hn0.
rewrite Rmult_assoc 3!Rabs_mult.
rewrite Rmult_assoc.
apply Rmult_le_compat_l.
apply Rabs_pos.
apply Rmult_le_compat.
apply Rabs_pos.
apply Rmult_le_pos; apply Rabs_pos.
specialize (HH t (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))).
apply locally_singleton in HH.
apply locally_2d_singleton in HH.
now apply HH.
rewrite - 2!RPow_abs.
instantiate (1:=(Rmax (Rabs (u - x)) (Rabs (v - y)) ^ S n)).
apply Rle_trans with ((Rmax (Rabs (u - x)) (Rabs (v - y)) ^ n0) * (Rmax (Rabs (u - x)) (Rabs (v - y)) ^ (S n - n0))).
apply Rmult_le_compat.
apply pow_le ; apply Rabs_pos.
apply pow_le ; apply Rabs_pos.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_l.
apply pow_incr.
split.
apply Rabs_pos.
apply Rmax_r.
rewrite -pow_add.
rewrite -le_plus_minus.
apply Rle_refl.
exact Hn0.
rewrite - scal_sum.
rewrite /Rdiv Rmult_1_l Rabs_right .
right; ring.
apply Rle_ge; apply Rlt_le; apply Rinv_0_lt_compat.
apply INR_fact_lt_0.
apply le_refl.
split; apply Rlt_le, Ht.
intros n0 hn0.
rewrite H0.
rewrite 2!Rmult_0_l 2!Rplus_0_r pow1.
unfold differential, Rdiv; ring.
now apply le_S.
split; [apply Rle_refl | apply Rle_0_1].
Qed.
