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

Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Hierarchy.
Require Import Compactness Lim_seq.

(** This file describes defineitions and properties of continuity on
[R] and on uniform spaces. It also contains many results about the
limit of a real function (predicates [is_lim] and [ex_lim] and total
function [Lim]). This limit may be either a real or an extended
real. *)

(** * Limit of fonctions *)

(** ** Definition *)

Definition is_lim (f : R -> R) (x l : Rbar) :=
  filterlim f (Rbar_locally' x) (Rbar_locally l).

Definition is_lim' (f : R -> R) (x l : Rbar) :=
  match l with
    | Finite l =>
      forall eps : posreal, Rbar_locally' x (fun y => Rabs (f y - l) < eps)
    | p_infty => forall M : R, Rbar_locally' x (fun y => M < f y)
    | m_infty => forall M : R, Rbar_locally' x (fun y => f y < M)
  end.
Definition ex_lim (f : R -> R) (x : Rbar) := exists l : Rbar, is_lim f x l.
Definition ex_finite_lim (f : R -> R) (x : Rbar) := exists l : R, is_lim f x l.
Definition Lim (f : R -> R) (x : Rbar) := Lim_seq (fun n => f (Rbar_loc_seq x n)).

Lemma is_lim_spec :
  forall f x l,
  is_lim' f x l <-> is_lim f x l.
Proof.
destruct l as [l| |] ; split.
- intros H P [eps LP].
  unfold filtermap.
  generalize (H eps).
  apply filter_imp.
  intros u.
  apply LP.
- intros H eps.
  apply (H (fun y => Rabs (y - l) < eps)).
  now exists eps.
- intros H P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros H M.
  apply (H (fun y => M < y)).
  now exists M.
- intros H P [M LP].
  unfold filtermap.
  generalize (H M).
  apply filter_imp.
  intros u.
  apply LP.
- intros H M.
  apply (H (fun y => y < M)).
  now exists M.
Qed.

(** Equivalence with standard library Reals *)

Lemma is_lim_Reals_0 (f : R -> R) (x l : R) :
  is_lim f x l -> limit1_in f (fun y => y <> x) l x.
Proof.
  intros H e He.
  apply is_lim_spec in H.
  destruct (H (mkposreal e He)) as [d Hd].
  exists d ; split.
  apply cond_pos.
  intros y [H1 H2].
  now apply (Hd y).
Qed.
Lemma is_lim_Reals_1 (f : R -> R) (x l : R) :
  limit1_in f (fun y => y <> x) l x -> is_lim f x l.
Proof.
  intros H.
  apply is_lim_spec.
  intros [e He].
  destruct (H e He) as [d [Hd H']].
  exists (mkposreal d Hd).
  intros y Hy Hxy.
  apply (H' y).
  now split.
Qed.
Lemma is_lim_Reals (f : R -> R) (x l : R) :
  is_lim f x l <-> limit1_in f (fun y => y <> x) l x.
Proof.
  split ; [apply is_lim_Reals_0|apply is_lim_Reals_1].
Qed.

(** Composition *)

Lemma is_lim_comp' :
  forall {T} {F} {FF : @Filter T F} (f : T -> R) (g : R -> R) (x l : Rbar),
  filterlim f F (Rbar_locally x) -> is_lim g x l ->
  F (fun y => Finite (f y) <> x) ->
  filterlim (fun y => g (f y)) F (Rbar_locally l).
Proof.
intros T F FF f g x l Lf Lg Hf.
revert Lg.
apply filterlim_comp.
intros P HP.
destruct x as [x| |] ; try now apply Lf.
specialize (Lf _ HP).
unfold filtermap in Lf |- *.
generalize (filter_and _ _ Hf Lf).
apply filter_imp.
intros y [H Hi].
apply Hi.
contradict H.
now apply f_equal.
Qed.

Lemma is_lim_comp_seq (f : R -> R) (u : nat -> R) (x l : Rbar) :
  is_lim f x l ->
  eventually (fun n => Finite (u n) <> x) ->
  is_lim_seq u x -> is_lim_seq (fun n => f (u n)) l.
Proof.
intros Lf Hu Lu.
exact (is_lim_comp' u f x l Lu Lf Hu).
Qed.

(** Uniqueness *)

Lemma is_lim_unique (f : R -> R) (x l : Rbar) :
  is_lim f x l -> Lim f x = l.
Proof.
  intros.
  unfold Lim.
  rewrite (is_lim_seq_unique _ l) //.
  apply (is_lim_comp_seq f _ x l H).
  exists 1%nat => n Hn.
  case: x {H} => [x | | ] //=.
  apply Rbar_finite_neq, Rgt_not_eq, Rminus_lt_0.
  ring_simplify.
  by apply RinvN_pos.
  by apply is_lim_seq_Rbar_loc_seq.
Qed.
Lemma Lim_correct (f : R -> R) (x : Rbar) :
  ex_lim f x -> is_lim f x (Lim f x).
Proof.
  intros (l,H).
  replace (Lim f x) with l.
    apply H.
  apply sym_eq, is_lim_unique, H.
Qed.

Lemma ex_finite_lim_correct (f : R -> R) (x : Rbar) :
  ex_finite_lim f x <-> ex_lim f x /\ is_finite (Lim f x).
Proof.
  split.
  case => l Hf.
  move: (is_lim_unique f x l Hf) => Hf0.
  split.
  by exists l.
  by rewrite Hf0.
  case ; case => l Hf Hf0.
  exists (real l).
  rewrite -(is_lim_unique _ _ _ Hf).
  rewrite Hf0.
  by rewrite (is_lim_unique _ _ _ Hf).
Qed.
Lemma Lim_correct' (f : R -> R) (x : Rbar) :
  ex_finite_lim f x -> is_lim f x (real (Lim f x)).
Proof.
  intro Hf.
  apply ex_finite_lim_correct in Hf.
  rewrite (proj2 Hf).
  by apply Lim_correct, Hf.
Qed.

(** ** Operations and order *)

(** Extensionality *)

Lemma is_lim_ext_loc (f g : R -> R) (x l : Rbar) :
  Rbar_locally' x (fun y => f y = g y)
  -> is_lim f x l -> is_lim g x l.
Proof.
apply filterlim_ext_loc.
Qed.
Lemma ex_lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally' x (fun y => f y = g y)
  -> ex_lim f x -> ex_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_lim_ext_loc with f.
Qed.
Lemma Lim_ext_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally' x (fun y => f y = g y)
  -> Lim g x = Lim f x.
Proof.
  move => H.
  apply sym_eq.
  apply Lim_seq_ext_loc.
  apply: filterlim_Rbar_loc_seq H.
Qed.

Lemma is_lim_ext (f g : R -> R) (x l : Rbar) :
  (forall y, f y = g y)
  -> is_lim f x l -> is_lim g x l.
Proof.
  move => H.
  apply is_lim_ext_loc.
  by apply filter_forall.
Qed.
Lemma ex_lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> ex_lim f x -> ex_lim g x.
Proof.
  move => H [l Hf].
  exists l.
  by apply is_lim_ext with f.
Qed.
Lemma Lim_ext (f g : R -> R) (x : Rbar) :
  (forall y, f y = g y)
  -> Lim g x = Lim f x.
Proof.
  move => H.
  apply Lim_ext_loc.
  by apply filter_forall.
Qed.

(** Composition *)

Lemma is_lim_comp (f g : R -> R) (x k l : Rbar) :
  is_lim f l k -> is_lim g x l -> Rbar_locally' x (fun y => Finite (g y) <> l)
    -> is_lim (fun x => f (g x)) x k.
Proof.
intros Lf Lg Hg.
by apply (is_lim_comp' g f l k Lg Lf Hg).
Qed.
Lemma ex_lim_comp (f g : R -> R) (x : Rbar) :
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally' x (fun y => Finite (g y) <> Lim g x)
    -> ex_lim (fun x => f (g x)) x.
Proof.
  intros.
  exists (Lim f (Lim g x)).
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.
Lemma Lim_comp (f g : R -> R) (x : Rbar) :
  ex_lim f (Lim g x) -> ex_lim g x -> Rbar_locally' x (fun y => Finite (g y) <> Lim g x)
    -> Lim (fun x => f (g x)) x = Lim f (Lim g x).
Proof.
  intros.
  apply is_lim_unique.
  apply is_lim_comp with (Lim g x).
  by apply Lim_correct.
  by apply Lim_correct.
  by apply H1.
Qed.

(** Identity *)

Lemma is_lim_id (x : Rbar) :
  is_lim (fun y => y) x x.
Proof.
intros P HP.
apply filterlim_id.
now apply Rbar_locally'_le.
Qed.
Lemma ex_lim_id (x : Rbar) :
  ex_lim (fun y => y) x.
Proof.
  exists x.
  by apply is_lim_id.
Qed.
Lemma Lim_id (x : Rbar) :
  Lim (fun y => y) x = x.
Proof.
  apply is_lim_unique.
  by apply is_lim_id.
Qed.

(** Constant *)

Lemma is_lim_const (a : R) (x : Rbar) :
  is_lim (fun _ => a) x a.
Proof.
intros P HP.
now apply filterlim_const.
Qed.
Lemma ex_lim_const (a : R) (x : Rbar) :
  ex_lim (fun _ => a) x.
Proof.
  exists a.
  by apply is_lim_const.
Qed.
Lemma Lim_const (a : R) (x : Rbar) :
  Lim (fun _ => a) x = a.
Proof.
  apply is_lim_unique.
  by apply is_lim_const.
Qed.

(** *** Additive operators *)

(** Opposite *)

Lemma is_lim_opp (f : R -> R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => - f y) x (Rbar_opp l).
Proof.
intros Cf.
eapply filterlim_comp.
apply Cf.
apply filterlim_Rbar_opp.
Qed.
Lemma ex_lim_opp (f : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => - f y) x.
Proof.
  case => l Hf.
  exists (Rbar_opp l).
  by apply is_lim_opp.
Qed.
Lemma Lim_opp (f : R -> R) (x : Rbar) :
  Lim (fun y => - f y) x = Rbar_opp (Lim f x).
Proof.
  rewrite -Lim_seq_opp.
  by apply Lim_seq_ext.
Qed.

(** Addition *)

Lemma is_lim_plus (f g : R -> R) (x lf lg l : Rbar) :
  is_lim f x lf -> is_lim g x lg ->
  is_Rbar_plus lf lg l ->
  is_lim (fun y => f y + g y) x l.
Proof.
intros Cf Cg Hp.
eapply filterlim_comp_2 ; try eassumption.
by apply filterlim_Rbar_plus.
Qed.
Lemma is_lim_plus' (f g : R -> R) (x : Rbar) (lf lg : R) :
  is_lim f x lf -> is_lim g x lg ->
  is_lim (fun y => f y + g y) x (lf + lg).
Proof.
  intros Hf Hg.
  eapply is_lim_plus.
  by apply Hf.
  by apply Hg.
  by [].
Qed.
Lemma ex_lim_plus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_plus (Lim f x) (Lim g x) ->
  ex_lim (fun y => f y + g y) x.
Proof.
  move => /Lim_correct Hf /Lim_correct Hg Hl.
  exists (Rbar_plus (Lim f x) (Lim g x)).
  eapply is_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.
Lemma Lim_plus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_plus (Lim f x) (Lim g x) ->
  Lim (fun y => f y + g y) x = Rbar_plus (Lim f x) (Lim g x).
Proof.
  move => /Lim_correct Hf /Lim_correct Hg Hl.
  apply is_lim_unique.
  eapply is_lim_plus ; try eassumption.
  by apply Rbar_plus_correct.
Qed.

(** Subtraction *)

Lemma is_lim_minus (f g : R -> R) (x lf lg l : Rbar) :
  is_lim f x lf -> is_lim g x lg ->
  is_Rbar_minus lf lg l ->
  is_lim (fun y => f y - g y) x l.
Proof.
  move => Hf Hg Hl.
  eapply is_lim_plus ; try eassumption.
  now apply is_lim_opp.
Qed.
Lemma is_lim_minus' (f g : R -> R) (x : Rbar) (lf lg : R) :
  is_lim f x lf -> is_lim g x lg ->
  is_lim (fun y => f y - g y) x (lf - lg).
Proof.
  intros Hf Hg.
  eapply is_lim_minus ; try eassumption.
  by [].
Qed.
Lemma ex_lim_minus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_minus (Lim f x) (Lim g x) ->
  ex_lim (fun y => f y - g y) x.
Proof.
  move => Hf Hg Hl.
  apply ex_lim_plus.
  by apply Hf.
  apply ex_lim_opp.
  by apply Hg.
  rewrite Lim_opp.
  by apply Hl.
Qed.
Lemma Lim_minus (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_minus (Lim f x) (Lim g x) ->
  Lim (fun y => f y - g y) x = Rbar_minus (Lim f x) (Lim g x).
Proof.
  move => Hf Hg Hl.
  rewrite Lim_plus.
  by rewrite Lim_opp.
  by apply Hf.
  apply ex_lim_opp.
  by apply Hg.
  rewrite Lim_opp.
  by apply Hl.
Qed.

(** ** Multiplicative operators *)
(** Multiplicative inverse *)

Lemma is_lim_inv (f : R -> R) (x l : Rbar) :
  is_lim f x l -> l <> 0 -> is_lim (fun y => / f y) x (Rbar_inv l).
Proof.
  intros Hf Hl.
  apply filterlim_comp with (1 := Hf).
  now apply filterlim_Rbar_inv.
Qed.
Lemma ex_lim_inv (f : R -> R) (x : Rbar) :
  ex_lim f x -> Lim f x <> 0 -> ex_lim (fun y => / f y) x.
Proof.
  move => /Lim_correct Hf Hlf.
  exists (Rbar_inv (Lim f x)).
  by apply is_lim_inv.
Qed.
Lemma Lim_inv (f : R -> R) (x : Rbar) :
  ex_lim f x -> Lim f x <> 0 -> Lim (fun y => / f y) x = Rbar_inv (Lim f x).
Proof.
  move => /Lim_correct Hf Hlf.
  apply is_lim_unique.
  by apply is_lim_inv.
Qed.

(** Multiplication *)

Lemma is_lim_mult (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg ->
  ex_Rbar_mult lf lg ->
  is_lim (fun y => f y * g y) x (Rbar_mult lf lg).
Proof.
intros Cf Cg Hp.
eapply filterlim_comp_2 ; try eassumption.
by apply filterlim_Rbar_mult, Rbar_mult_correct.
Qed.
Lemma ex_lim_mult (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_mult (Lim f x) (Lim g x) ->
  ex_lim (fun y => f y * g y) x.
Proof.
  move => /Lim_correct Hf /Lim_correct Hg Hl.
  exists (Rbar_mult (Lim f x) (Lim g x)).
  now apply is_lim_mult.
Qed.
Lemma Lim_mult (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x ->
  ex_Rbar_mult (Lim f x) (Lim g x) ->
  Lim (fun y => f y * g y) x = Rbar_mult (Lim f x) (Lim g x).
Proof.
  move => /Lim_correct Hf /Lim_correct Hg Hl.
  apply is_lim_unique.
  now apply is_lim_mult.
Qed.

(** Scalar multiplication *)

Lemma is_lim_scal_l (f : R -> R) (a : R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => a * f y) x (Rbar_mult a l).
Proof.
  move => Hf.
  case: (Req_dec 0 a) => [<- {a} | Ha].
  rewrite Rbar_mult_0_l.
  apply is_lim_ext with (fun _ => 0).
  move => y ; by rewrite Rmult_0_l.
  by apply is_lim_const.

  apply is_lim_mult.
  by apply is_lim_const.
  by apply Hf.
  apply sym_not_eq in Ha.
  case: l {Hf} => [l | | ] //=.
Qed.
Lemma ex_lim_scal_l (f : R -> R) (a : R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => a * f y) x.
Proof.
  case => l Hf.
  exists (Rbar_mult a l).
  by apply is_lim_scal_l.
Qed.
Lemma Lim_scal_l (f : R -> R) (a : R) (x : Rbar) :
  Lim (fun y => a * f y) x = Rbar_mult a (Lim f x).
Proof.
  apply Lim_seq_scal_l.
Qed.

Lemma is_lim_scal_r (f : R -> R) (a : R) (x l : Rbar) :
  is_lim f x l -> is_lim (fun y => f y * a) x (Rbar_mult l a).
Proof.
  move => Hf.
  rewrite Rbar_mult_comm.
  apply is_lim_ext with (fun y => a * f y).
  move => y ; by apply Rmult_comm.
  by apply is_lim_scal_l.
Qed.
Lemma ex_lim_scal_r (f : R -> R) (a : R) (x : Rbar) :
  ex_lim f x -> ex_lim (fun y => f y * a) x.
Proof.
  case => l Hf.
  exists (Rbar_mult l a).
  by apply is_lim_scal_r.
Qed.
Lemma Lim_scal_r (f : R -> R) (a : R) (x : Rbar) :
  Lim (fun y => f y * a) x = Rbar_mult (Lim f x) a.
Proof.
  rewrite Rbar_mult_comm -Lim_seq_scal_l.
  apply Lim_seq_ext.
  move => y ; by apply Rmult_comm.
Qed.

(** Division *)

Lemma is_lim_div (f g : R -> R) (x lf lg : Rbar) :
  is_lim f x lf -> is_lim g x lg -> lg <> 0 ->
  ex_Rbar_div lf lg ->
  is_lim (fun y => f y / g y) x (Rbar_div lf lg).
Proof.
  move => Hf Hg Hlg Hl.
  apply is_lim_mult ; try assumption.
  now apply is_lim_inv.
Qed.
Lemma ex_lim_div (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x -> Lim g x <> 0 ->
  ex_Rbar_div (Lim f x) (Lim g x) ->
  ex_lim (fun y => f y / g y) x.
Proof.
  move => Hf Hg Hlg Hl.
  apply ex_lim_mult ; try assumption.
  now apply ex_lim_inv.
  now rewrite Lim_inv.
Qed.
Lemma Lim_div (f g : R -> R) (x : Rbar) :
  ex_lim f x -> ex_lim g x -> Lim g x <> 0 ->
  ex_Rbar_div (Lim f x) (Lim g x) ->
  Lim (fun y => f y / g y) x = Rbar_div (Lim f x) (Lim g x).
Proof.
  move => Hf Hg Hlg Hl.
  apply is_lim_unique.
  apply is_lim_div ; try apply Lim_correct ; assumption.
Qed.

(** Composition by linear functions *)

Lemma is_lim_comp_lin (f : R -> R) (a b : R) (x l : Rbar) :
  is_lim f (Rbar_plus (Rbar_mult a x) b) l -> a <> 0
  -> is_lim (fun y => f (a * y + b)) x l.
Proof.
  move => Hf Ha.
  apply is_lim_comp with (Rbar_plus (Rbar_mult a x) b).
  by apply Hf.
  eapply is_lim_plus.
  apply is_lim_scal_l.
  apply is_lim_id.
  apply is_lim_const.
  apply Rbar_plus_correct.
  case: (Rbar_mult a x) => //.
  case: x {Hf} => [x | | ] //=.
  exists (mkposreal _ Rlt_0_1) => y _ Hy.
  apply Rbar_finite_neq, Rminus_not_eq ; ring_simplify (a * y + b - (a * x + b)).
  rewrite -Rmult_minus_distr_l.
  apply Rmult_integral_contrapositive ; split.
  by [].
  by apply Rminus_eq_contra.
  exists 0 => x Hx.
  apply sym_not_eq in Ha.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
  exists 0 => x Hx.
  apply sym_not_eq in Ha.
  case: Rle_dec => // H.
  case: Rle_lt_or_eq_dec => //.
Qed.
Lemma ex_lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) :
  ex_lim f (Rbar_plus (Rbar_mult a x) b)
  -> ex_lim (fun y => f (a * y + b)) x.
Proof.
  case => l Hf.
  case: (Req_dec a 0) => [-> {a Hf} | Ha].
  apply ex_lim_ext with (fun _ => f b).
  move => y ; by rewrite Rmult_0_l Rplus_0_l.
  by apply ex_lim_const.
  exists l ; by apply is_lim_comp_lin.
Qed.
Lemma Lim_comp_lin (f : R -> R) (a b : R) (x : Rbar) :
  ex_lim f (Rbar_plus (Rbar_mult a x) b) -> a <> 0 ->
  Lim (fun y => f (a * y + b)) x = Lim f (Rbar_plus (Rbar_mult a x) b).
Proof.
  move => Hf Ha.
  apply is_lim_unique.
  apply is_lim_comp_lin.
  by apply Lim_correct.
  exact: Ha.
Qed.

(** Continuity and limit *)

Lemma is_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> is_lim f x (f x).
Proof.
intros cf.
now apply continuity_pt_filterlim'.
Qed.
Lemma ex_lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> ex_finite_lim f x.
Proof.
  move => Hf.
  exists (f x).
  by apply is_lim_continuity.
Qed.
Lemma Lim_continuity (f : R -> R) (x : R) :
  continuity_pt f x -> Lim f x = f x.
Proof.
  move => Hf.
  apply is_lim_unique.
  by apply is_lim_continuity.
Qed.

Lemma C0_extension_right {T : UniformSpace} (f : R -> T) lb (a b : R) :
   a < b ->
   (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) ->
   (filterlim f (at_left b) (locally lb)) ->
   {g : R -> T | (forall c, a < c -> filterlim g (locally c) (locally (g c)))
     /\ (forall c : R, c < b -> g c = f c) /\ g b = lb}.
Proof.
  intros Hab ; intros.

  set g := fun x => match Rlt_dec x b with
                    | left _ => f x
                    | right _ => lb
                    end.
  assert (Gab : forall c : R, c < b -> g c = f c).
    intros c Hcb.
    unfold g.
    by (case: Rlt_dec).
  assert (Gb : forall c : R, b <= c -> g c = lb).
    intros c Hbc.
    unfold g.
    case: Rlt_dec (Rle_not_lt _ _ Hbc) => //.

  exists g ; split.
  intros c Hac.
  case: (Rlt_le_dec c b) ; (try case) => Hbc.
  - apply filterlim_ext_loc with f.
    apply locally_interval with m_infty b => //= y _ Hyb.
    by apply sym_eq, Gab.
    rewrite Gab //.
    apply H ; by split.
  - rewrite Gb.
    2: by apply Rlt_le.
    eapply filterlim_ext_loc.
    2: by apply filterlim_const.
    apply locally_interval with b p_infty => //= y Hby _.
    apply sym_eq, Gb.
    by apply Rlt_le.
  - rewrite -Hbc => {c Hbc Hac}.
    rewrite Gb.
    2: by apply Rle_refl.
    apply filterlim_locally => eps /= {H}.
    destruct (proj1 (filterlim_locally _ _) H0 eps) as [d Hd].
    simpl in Hd.
    exists d => x Hx.
    case: (Rlt_le_dec x b) => Hxb.
    rewrite Gab //.
    by apply Hd.
    rewrite Gb //.
    by apply ball_center.
  - split.
    by apply Gab.
    apply Gb ; by apply Rle_refl.
Qed.
Lemma filterlim_Ropp_left (x : R) :
  filterlim Ropp (at_left x) (at_right (- x)).
Proof.
  move => P [d /= Hd].
  exists d => y /= Hy Hy'.
  apply Hd.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  rewrite -Ropp_plus_distr Rabs_Ropp.
  by apply Hy.
  by apply Ropp_lt_contravar.
Qed.
Lemma filterlim_Ropp_right (x : R) :
  filterlim Ropp (at_right x) (at_left (- x)).
Proof.
  move => P [d /= Hd].
  exists d => y /= Hy Hy'.
  apply Hd.
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  rewrite -Ropp_plus_distr Rabs_Ropp.
  by apply Hy.
  by apply Ropp_lt_contravar.
Qed.

Lemma C0_extension_left {T : UniformSpace} (f : R -> T) la (a b : R) :
   a < b ->
   (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) ->
   (filterlim f (at_right a) (locally la)) ->
   {g : R -> T | (forall c, c < b -> filterlim g (locally c) (locally (g c)))
     /\ (forall c : R, a < c -> g c = f c) /\ g a = la}.
Proof.
  intros.
  destruct (C0_extension_right (fun x => f (- x)) la (-b) (-a)) as [g Hg].
  by apply Ropp_lt_contravar.
  intros.
  eapply filterlim_comp.
  apply (filterlim_opp c).
  apply H0.
  split ; apply Ropp_lt_cancel ; rewrite Ropp_involutive ; by apply H2.
  eapply filterlim_comp.
  apply filterlim_Ropp_left.
  by rewrite Ropp_involutive.
  exists (fun x => g (- x)) ; split.
  intros c Hc.
  eapply filterlim_comp.
  apply (filterlim_opp c).
  by apply Hg, Ropp_lt_contravar.
  split.
  intros c Hc.
  rewrite (proj1 (proj2 Hg)).
  by rewrite Ropp_involutive.
  by apply Ropp_lt_contravar.
  by apply Hg.
Qed.

Lemma C0_extension_lt {T : UniformSpace} (f : R -> T) la lb (a b : R) :
  a < b ->
   (forall c : R, a < c < b -> filterlim f (locally c) (locally (f c))) ->
   (filterlim f (at_right a) (locally la)) ->
   (filterlim f (at_left b) (locally lb)) ->
   {g : R -> T | (forall c, filterlim g (locally c) (locally (g c)))
     /\ (forall c : R, a < c < b -> g c = f c) /\ g a = la /\ g b = lb}.
Proof.
  intros.
  destruct (C0_extension_left f la a b) as [g [Cg [Gab Ga]]] => //.
  destruct (C0_extension_right g lb a b) as [h [Ch [Hab Hb]]] => //.
  intros.
  apply Cg, H3.
  eapply filterlim_ext_loc.
  2: by apply H2.
  apply Rminus_lt_0 in H.
  exists (mkposreal _ H) => y /= Hy Hy'.
  apply sym_eq, Gab.
  apply Ropp_lt_cancel, (Rplus_lt_reg_l b).
  eapply Rle_lt_trans, Hy.
  rewrite -abs_opp opp_minus.
  apply Rle_abs.
  exists h ; repeat split.
  intros c.
  case: (Rlt_le_dec a c) => Hac.
  by apply Ch.
  rewrite Hab.
  eapply filterlim_ext_loc.
  2: apply Cg.
  apply locally_interval with m_infty b => //.
  by eapply Rle_lt_trans, H.
  intros y _ Hy ; by apply sym_eq, Hab.
  by eapply Rle_lt_trans, H.
  by eapply Rle_lt_trans, H.
  intros c [Hac Hcb].
  rewrite Hab => //.
  by apply Gab.
  by rewrite Hab.
  by [].
Qed.

Lemma C0_extension_le {T : UniformSpace} (f : R -> T) (a b : R) :
   (forall c : R, a <= c <= b -> filterlim f (locally c) (locally (f c))) ->
   {g : R -> T | (forall c, filterlim g (locally c) (locally (g c)))
     /\ (forall c : R, a <= c <= b -> g c = f c)}.
Proof.
  intros.
  case: (Rlt_le_dec a b) => Hab.

  destruct (C0_extension_lt f (f a) (f b) a b Hab) as [g [Cg [Gab [Ga Gb]]]].
  intros c Hc.
  apply H ; split ; apply Rlt_le, Hc.
  eapply filterlim_filter_le_1, H.
  by apply filter_le_within.
  intuition.
  eapply filterlim_filter_le_1, H.
  by apply filter_le_within.
  intuition.
  exists g ; repeat split => //.
  intros c [Hac Hcb].
  case: Hac => [ Hac | <-] //.
  case: Hcb => [ Hcb | ->] //.
  apply Gab ; by split.

  exists (fun _ => f a) ; split ; simpl.
  move => c.
  by apply filterlim_const.
  intros c [Hac Hca].
  case: Hab => Hab.
  contradict Hab ; apply Rle_not_lt.
  by apply Rle_trans with c.
  rewrite Hab in Hca.
  by apply f_equal, Rle_antisym.
Qed.

Lemma bounded_continuity {K : AbsRing} {V : NormedModule K}
  (f : R -> V) a b :
  (forall x, a <= x <= b -> filterlim f (locally x) (locally (f x)))
  -> {M : R | forall x, a <= x <= b -> norm (f x) < M}.
Proof.
  destruct (Rle_dec b a) as [Hab|Hab].
    exists (norm (f a) + 1).
    intros x [Hax Hxb].
    replace x with a.
    rewrite -{1}(Rplus_0_r (norm (f a))).
    apply Rplus_lt_compat_l, Rlt_0_1.
    apply Rle_antisym with (1 := Hax).
    now apply Rle_trans with b.
  apply Rnot_le_lt in Hab.

  wlog: f / (forall x, filterlim f (locally x) (locally (f x))) => [ Hw Cf | Cf _ ].
    destruct (C0_extension_le f a b) as [g [Cg Hg]].
    by apply Cf.
    destruct (Hw g) as [M HM] => //.
    exists M ; intros.
    rewrite -Hg //.
    by apply HM.

  assert (forall x : R, locally x (fun y : R => Rabs (norm (f y) - norm (f x)) < 1)).
    intro x.
    generalize (proj1 (filterlim_locally_ball_norm _ _) (Cf x)) => {Cf} Cf.
    apply: filter_imp (Cf (mkposreal _ Rlt_0_1)) => y Hy.
    apply Rle_lt_trans with (2 := Hy).
    apply norm_triangle_inv.
  assert (forall x y : R, Rabs (norm (f y) - norm (f x)) < 1 \/ ~ Rabs (norm (f y) - norm (f x)) < 1).
    intros x y ; edestruct Rlt_dec.
    left ; by apply r.
    by right.

  set delta := (fun (x : R) => proj1_sig (locally_ex_dec x _ (H0 x) (H x))).
  destruct (compactness_value_1d a b delta) as [d Hd].
  destruct (nfloor_ex ((b - a) / d)) as [N HN].
    apply Rdiv_le_0_compat.
    now apply Rlt_le, Rlt_Rminus.
    apply cond_pos.
  set (M := (fix g n := match n with O => 0 | S n => Rmax (norm (f (a + INR n * d)) + 3) (g n) end) (S N)).
  exists M => x Hx.
  apply Rnot_le_lt => H2.
  apply (Hd x Hx) ; case => t.
  unfold delta.
  case: locally_ex_dec => e /= He [Ht [Hxt Hde]].
  contradict H2 ; apply Rlt_not_le.
  move: (fun (y : R) Hy => He y (norm_compat1 _ _ _ Hy)) => {He} He.
  apply He in Hxt.
  rewrite -(Rabs_pos_eq (norm _) (norm_ge_0 _)).
  replace (norm (f x)) with ((norm (f x) - norm (f t)) + norm (f t))%R by ring.
  eapply Rle_lt_trans.
  apply Rabs_triang.
  eapply Rlt_trans.
  apply Rplus_lt_compat_r.
  by apply Hxt.
  rewrite Rplus_comm ; apply Rlt_minus_r.
  clear x Hx Hxt.
  destruct (nfloor_ex ((t - a) / d)) as [n Hn].
    apply Rdiv_le_0_compat.
    apply Rplus_le_reg_r with a.
    now ring_simplify.
    apply cond_pos.
  set (y := a + INR n * d).
  replace (norm (f t)) with (-(norm (f y) - norm (f t)) + norm (f y))%R by ring.
  eapply Rle_lt_trans.

  apply Rabs_triang.
  eapply Rlt_trans.
  apply Rplus_lt_compat_r.
  rewrite Rabs_Ropp.
  apply He.
  change (Rabs (a + INR n * d - t) < e).
  replace (a + INR n * d - t) with (-((t - a) / d - INR n) * d).
  rewrite Rabs_mult (Rabs_pos_eq d).
  2: apply Rlt_le, cond_pos.
  apply Rlt_le_trans with (1 * d).
  apply Rmult_lt_compat_r with (1 := cond_pos d).
  rewrite Rabs_Ropp Rabs_pos_eq.
  apply Rplus_lt_reg_r with (INR n).
  now rewrite /Rminus Rplus_assoc Rplus_opp_l Rplus_0_r (Rplus_comm 1).
  apply Rplus_le_reg_r with (INR n).
  now ring_simplify.
  now rewrite Rmult_1_l.
  field.
  apply Rgt_not_eq, cond_pos.

  apply Rplus_lt_reg_l with 1.
  ring_simplify.
  rewrite -> Rabs_pos_eq by apply norm_ge_0.
  assert (n < S N)%nat.
  apply INR_lt.
  apply Rle_lt_trans with (1 := proj1 Hn).
  rewrite S_INR.
  apply Rle_lt_trans with (2 := proj2 HN).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, cond_pos.
  now apply Rplus_le_compat_r.
  unfold M, y.
  clear -H1.
  induction N.
  apply Rlt_le_trans with (2 := Rmax_l _ _).
  destruct n.
  apply Rplus_lt_compat_l, Rplus_lt_compat_l.
  now apply (IZR_lt 1 2).
  now apply lt_S_n in H1.
  destruct (le_lt_eq_dec _ _ (lt_n_Sm_le _ _ H1)) as [H2|H2].
  apply Rlt_le_trans with (2 := Rmax_r _ _).
  now apply IHN.
  apply Rlt_le_trans with (2 := Rmax_l _ _).
  rewrite H2.
  apply Rplus_lt_compat_l, Rplus_lt_compat_l.
  now apply (IZR_lt 1 2).
Qed.

(** *** Order *)

Lemma is_lim_le_loc (f g : R -> R) (x lf lg : Rbar) :
  Rbar_locally' x (fun y => f y <= g y) ->
  is_lim f x lf -> is_lim g x lg ->
  Rbar_le lf lg.
Proof.
  apply filterlim_le.
Qed.

Lemma is_lim_le_p_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally' x (fun y => f y <= g y) ->
  is_lim f x p_infty ->
  is_lim g x p_infty.
Proof.
  apply filterlim_ge_p_infty.
Qed.

Lemma is_lim_le_m_loc (f g : R -> R) (x : Rbar) :
  Rbar_locally' x (fun y => g y <= f y) ->
  is_lim f x m_infty ->
  is_lim g x m_infty.
Proof.
  apply filterlim_le_m_infty.
Qed.

Lemma is_lim_le_le_loc (f g h : R -> R) (x : Rbar) (l : Rbar) :
  Rbar_locally' x (fun y => f y <= h y <= g y) ->
  is_lim f x l -> is_lim g x l ->
  is_lim h x l.
Proof.
  apply filterlim_le_le.
Qed.

(** ** Generalized intermediate value theorem *)

Lemma IVT_gen (f : R -> R) (a b y : R) :
  Ranalysis1.continuity f
  -> Rmin (f a) (f b) <= y <= Rmax (f a) (f b)
  -> { x : R | Rmin a b <= x <= Rmax a b /\ f x = y }.
Proof.
  case: (Req_EM_T a b) => [ <- {b} | Hab].
    rewrite /Rmin /Rmax ; case: Rle_dec (Rle_refl a) (Rle_refl (f a)) ;
    case: Rle_dec => // _ _ _ _ Cf Hy.
    exists a ; split.
    split ; by apply Rle_refl.
    apply Rle_antisym ; by apply Hy.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: (Rle_lt_or_eq_dec _ _ Hab') => {Hab'} // Hab'.
    by apply Hw.
    rewrite (Rmin_comm (f a)) (Rmin_comm a) (Rmax_comm (f a)) (Rmax_comm a) ;
    apply Hw => //.
    by apply Rlt_not_eq.
  rewrite /(Rmin a) /(Rmax a) ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  wlog: f y / (f a <= f b) => [Hw |].
    case: (Rle_lt_dec (f a) (f b)) => Hf' Hf Hy.
    by apply Hw.
    case: (Hw (fun y => - f y) (- y)).
    by apply Ropp_le_contravar, Rlt_le.
    by apply Ranalysis1.continuity_opp.
    rewrite Rmin_opp_Rmax Rmax_opp_Rmin ;
    split ; apply Ropp_le_contravar, Hy.
    move => x [Hx Hfx].
    exists x ; intuition.
    by rewrite -(Ropp_involutive y) -Hfx Ropp_involutive.
  rewrite /Rmin /Rmax ; case: Rle_dec =>  // _ _.
  wlog: y / (f a < y < f b) => [Hw Hf Hy | Hy Hf _].
    case: Hy => Hay Hyb.
    case: (Rle_lt_or_eq_dec _ _ Hay) => {Hay} [Hay | <- ].
    case: (Rle_lt_or_eq_dec _ _ Hyb) => {Hyb} [Hyb | -> ].
    apply Hw ; intuition.
    exists b ; intuition.
    exists a ; intuition.

  case (IVT (fun x => f x - y) a b).
  apply Ranalysis1.continuity_minus.
  exact Hf.
  apply continuity_const.
  intros _ _ ; reflexivity.
  exact Hab.
  apply Rlt_minus_l ; rewrite Rplus_0_l ; apply Hy.
  apply Rlt_minus_r ; rewrite Rplus_0_l ; apply Hy.
  intros x [Hx Hfx].
  apply Rminus_diag_uniq in Hfx.
  by exists x.
Qed.

Lemma IVT_Rbar_incr (f : R -> R) (a b la lb : Rbar) (y : R) :
  is_lim f a la -> is_lim f b lb
  -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x)
  -> Rbar_lt a b
  -> Rbar_lt la y /\ Rbar_lt y lb
  -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
intros Hfa Hfb Cf Hab Hy.
assert (Hb' : exists b' : R, Rbar_lt b' b /\
        is_upper_bound (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y) b').
{ assert (Hfb' : Rbar_locally' b (fun x => y < f x)).
    apply Hfb.
    now apply (open_Rbar_gt' _ y).
  clear -Hab Hfb'.
  destruct b as [b| |].
  - destruct Hfb' as [eps He].
    exists (b - eps).
    split.
    apply Rminus_lt_0.
    replace (b - (b - eps)) with (pos eps) by ring.
    apply cond_pos.
    intros u [_ [H1 H2]].
    apply Rnot_lt_le.
    intros Hu.
    apply Rle_not_lt with (1 := H2).
    apply He.
    apply Rabs_lt_between'.
    split.
    exact Hu.
    apply Rlt_le_trans with (1 := H1).
    apply Rlt_le.
    apply Rminus_lt_0.
    replace (b + eps - b) with (pos eps) by ring.
    apply cond_pos.
    now apply Rlt_not_eq.
  - destruct Hfb' as [M HM].
    exists M.
    repeat split.
    intros u [_ [H1 H2]].
    apply Rnot_lt_le.
    intros Hu.
    apply Rle_not_lt with (1 := H2).
    now apply HM.
  - now destruct a. }
assert (Hex : exists x : R, Rbar_lt a x /\ Rbar_lt x b /\ f x <= y).
{ assert (Hfa' : Rbar_locally' a (fun x => Rbar_lt x b /\ f x < y)).
    apply filter_and.
    apply Rbar_locally'_le.
    now apply open_Rbar_lt'.
    apply (Hfa (fun u => u < y)).
    now apply (open_Rbar_lt' _ y).
  clear -Hab Hfa'.
  destruct a as [a| |].
  - destruct Hfa' as [eps He].
    exists (a + eps / 2).
    assert (Ha : a < a + eps / 2).
      apply Rminus_lt_0.
      replace (a + eps / 2 - a) with (eps / 2) by ring.
      apply is_pos_div_2.
    split.
    exact Ha.
    assert (H : Rbar_lt (a + eps / 2) b /\ (f (a + eps / 2) < y)).
      apply He.
      rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
      replace (a + eps / 2 + - a) with (eps / 2) by ring.
      rewrite Rabs_pos_eq.
      apply Rlt_eps2_eps.
      apply cond_pos.
      apply Rlt_le.
      apply is_pos_div_2.
      now apply Rgt_not_eq.
    destruct H as [H1 H2].
    split.
    exact H1.
    now apply Rlt_le.
  - easy.
  - destruct Hfa' as [M HM].
    exists (M - 1).
    assert (H : Rbar_lt (M - 1) b /\ f (M - 1) < y).
      apply HM.
      apply Rminus_lt_0.
      replace (M - (M - 1)) with 1 by ring.
      apply Rlt_0_1.
    destruct H as [H1 H2].
    repeat split.
    exact H1.
    now apply Rlt_le. }
destruct (completeness (fun x => Rbar_lt a x /\ Rbar_lt x b /\ f x <= y)) as [x [Hub Hlub]].
destruct Hb' as [b' Hb'].
now exists b'.
exact Hex.
exists x.
destruct Hb' as [b' [Hb Hb']].
destruct Hex as [x' Hx'].
assert (Hax : Rbar_lt a x).
  apply Rbar_lt_le_trans with x'.
  apply Hx'.
  now apply Hub.
assert (Hxb : Rbar_lt x b).
  apply Rbar_le_lt_trans with b'.
  now apply Hlub.
  exact Hb.
repeat split ; try assumption.
specialize (Cf _ Hax Hxb).
apply continuity_pt_filterlim in Cf.
destruct (total_order_T (f x) y) as [[H|H]|H].
- assert (H': locally x (fun u => (Rbar_lt a u /\ Rbar_lt u b) /\ f u < y)).
    apply filter_and.
    apply filter_and.
    now apply open_Rbar_gt.
    now apply open_Rbar_lt.
    apply (Cf (fun u => u < y)).
    now apply open_lt.
  destruct H' as [eps H'].
  elim Rle_not_lt with x (x + eps / 2).
  apply Hub.
  destruct (H' (x + eps / 2)) as [[H1 H2] H3].
  rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
  replace (x + eps / 2 + - x) with (eps / 2) by ring.
  rewrite Rabs_pos_eq.
  apply Rlt_eps2_eps.
  apply cond_pos.
  apply Rlt_le.
  apply is_pos_div_2.
  split.
  exact H1.
  split.
  exact H2.
  now apply Rlt_le.
  apply Rminus_lt_0.
  replace (x + eps / 2 - x) with (eps / 2) by ring.
  apply is_pos_div_2.
- exact H.
- assert (H': locally x (fun u => y < f u)).
    apply (Cf (fun u => y < u)).
    now apply open_gt.
  destruct H' as [eps H'].
  elim Rle_not_lt with (x - eps) x.
  apply Hlub.
  intros u Hfu.
  apply Rnot_lt_le.
  intros Hu.
  apply Rle_not_lt with (1 := proj2 (proj2 Hfu)).
  apply H'.
  apply Rabs_lt_between'.
  split.
  exact Hu.
  apply Rle_lt_trans with (1 := Hub u Hfu).
  apply Rminus_lt_0.
  replace (x + eps - x) with (pos eps) by ring.
  apply cond_pos.
  apply Rminus_lt_0.
  replace (x - (x - eps)) with (pos eps) by ring.
  apply cond_pos.
Qed.

Lemma IVT_Rbar_decr (f : R -> R) (a b la lb : Rbar) (y : R) :
  is_lim f a la -> is_lim f b lb
  -> (forall (x : R), Rbar_lt a x -> Rbar_lt x b -> continuity_pt f x)
  -> Rbar_lt a b
  -> Rbar_lt lb y /\ Rbar_lt y la
  -> {x : R | Rbar_lt a x /\ Rbar_lt x b /\ f x = y}.
Proof.
  move => Hla Hlb Cf Hab Hy.
  case: (IVT_Rbar_incr (fun x => - f x) a b (Rbar_opp la) (Rbar_opp lb) (-y)).
  by apply is_lim_opp.
  by apply is_lim_opp.
  move => x Hax Hxb.
  by apply continuity_pt_opp, Cf.
  by apply Hab.
  split ; apply Rbar_opp_lt ;
  rewrite Rbar_opp_involutive /Rbar_opp Ropp_involutive ;
  by apply Hy.
  move => x Hx ; exists x ; intuition.
  by rewrite -(Ropp_involutive y) -H4 Ropp_involutive.
Qed.

(** * 2D-continuity *)

(** ** Definitions *)

Definition continuity_2d_pt f x y :=
  forall eps : posreal, locally_2d (fun u v => Rabs (f u v - f x y) < eps) x y.

Lemma continuity_2d_pt_filterlim :
  forall f x y,
  continuity_2d_pt f x y <->
  filterlim (fun z : R * R => f (fst z) (snd z)) (locally (x,y)) (locally (f x y)).
Proof.
split.
- intros Cf P [eps He].
  specialize (Cf eps).
  apply locally_2d_locally in Cf.
  apply filter_imp with (2 := Cf).
  intros [u v].
  apply He.
- intros Cf eps.
  apply locally_2d_locally.
  specialize (Cf (fun z => Rabs (z - f x y) < eps)).
  unfold filtermap in Cf.
  apply Cf.
  now exists eps.
Qed.

Lemma uniform_continuity_2d :
  forall f a b c d,
  (forall x y, a <= x <= b -> c <= y <= d -> continuity_2d_pt f x y) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c <= y <= d ->
  a <= u <= b -> c <= v <= d ->
  Rabs (u - x) < delta -> Rabs (v - y) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c d Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x y Hx Hy => locally_2d_ex_dec (P x y) x y _ (Cf x y Hx Hy _))).
intros delta1.
set (delta2 x y := match Rle_dec a x, Rle_dec x b, Rle_dec c y, Rle_dec y d with
  left Ha, left Hb, left Hc, left Hd => pos_div_2 (proj1_sig (delta1 x y (conj Ha Hb) (conj Hc Hd))) |
  _, _, _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_2d a b c d delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux Hvy.
specialize (Hdelta x y Hx Hy).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&q&(Hap,Hpb)&(Hcq,Hqd)&Hxp&Hyq&Hd).
replace (f u v - f x y) with (f u v - f p q + (f p q - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hyq Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
case Rle_dec => Hcq' ; try easy.
case Rle_dec => Hqd' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hyq Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
replace (v - q) with (v - y + (y - q)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hyq).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hvy).
apply: Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rlt_trans with (1 := Hyq).
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
destruct (Rlt_dec (Rabs (f u v - f x y)) (pos_div_2 eps)) ; [left|right]; assumption.
Qed.

Lemma uniform_continuity_2d_1d :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f x c) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f u v - f x y) < eps.
Proof.
intros f a b c Cf eps.
set (P x y u v := Rabs (f u v - f x y) < pos_div_2 eps).
refine (_ (fun x Hx => locally_2d_ex_dec (P x c) x c _ (Cf x Hx _))).
intros delta1.
set (delta2 x := match Rle_dec a x, Rle_dec x b with
  left Ha, left Hb => pos_div_2 (proj1_sig (delta1 x (conj Ha Hb))) |
  _, _ => mkposreal _ Rlt_0_1 end).
destruct (compactness_value_1d a b delta2) as (delta,Hdelta).
exists (pos_div_2 delta) => x y u v Hx Hy Hu Hv Hux.
specialize (Hdelta x Hx).
apply Rnot_le_lt.
apply: false_not_not Hdelta => Hdelta.
apply Rlt_not_le.
destruct Hdelta as (p&(Hap,Hpb)&Hxp&Hd).
replace (f u v - f x y) with (f u v - f p c + (f p c - f x y)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var eps).
revert Hxp Hd.
unfold delta2.
case Rle_dec => Hap' ; try easy.
case Rle_dec => Hpb' ; try easy.
clear delta2.
case delta1 => /= r Hr Hxp Hd.
apply Rplus_lt_compat.
apply Hr.
replace (u - p) with (u - x + (x - p)) by ring.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
rewrite (double_var r).
apply Rplus_lt_compat with (2 := Hxp).
apply Rlt_le_trans with (2 := Hd).
apply Rlt_trans with (1 := Hux).
apply: Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
rewrite Rabs_minus_sym.
apply Hr.
apply Rlt_trans with (1 := Hxp).
apply Rlt_eps2_eps.
apply cond_pos.
apply Rle_lt_trans with (pos_div_2 delta).
now apply Rabs_le_between'.
apply Rlt_le_trans with(1 := Rlt_eps2_eps _ (cond_pos delta)).
apply Rle_trans with (1 := Hd).
apply Rlt_le.
apply Rlt_eps2_eps.
apply cond_pos.
intros u v.
unfold P.
destruct (Rlt_dec (Rabs (f u v - f x c)) (pos_div_2 eps)); [left|right] ; assumption.
Qed.

Lemma uniform_continuity_2d_1d' :
  forall f a b c,
  (forall x, a <= x <= b -> continuity_2d_pt f c x) ->
  forall eps : posreal, exists delta : posreal,
  forall x y u v,
  a <= x <= b -> c - delta <= y <= c + delta ->
  a <= u <= b -> c - delta <= v <= c + delta ->
  Rabs (u - x) < delta ->
  Rabs (f v u - f y x) < eps.
Proof.
intros f a b c Cf eps.
assert (T:(forall x : R, a <= x <= b -> continuity_2d_pt (fun x0 y : R => f y x0) x c) ).
intros x Hx e.
destruct (Cf x Hx e) as (d,Hd).
exists d.
intros; now apply Hd.
destruct (uniform_continuity_2d_1d (fun x y => f y x) a b c T eps) as (d,Hd).
exists d; intros.
now apply Hd.
Qed.

Lemma continuity_2d_pt_neq_0 :
  forall f x y,
  continuity_2d_pt f x y -> f x y <> 0 ->
  locally_2d (fun u v => f u v <> 0) x y.
Proof.
intros f x y Cf H.
apply continuity_2d_pt_filterlim in Cf.
apply locally_2d_locally.
apply (Cf (fun y => y <> 0)).
now apply open_neq.
Qed.

(** ** Operations *)

(** Identity *)

Lemma continuity_pt_id :
  forall x, continuity_pt (fun x => x) x.
Proof.
intros x.
apply continuity_pt_filterlim.
now intros P.
Qed.

Lemma continuity_2d_pt_id1 :
  forall x y, continuity_2d_pt (fun u v => u) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

Lemma continuity_2d_pt_id2 :
  forall x y, continuity_2d_pt (fun u v => v) x y.
Proof.
  intros x y eps; exists eps; tauto.
Qed.

(** Constant functions *)

Lemma continuity_2d_pt_const :
  forall x y c, continuity_2d_pt (fun u v => c) x y.
Proof.
  intros x y c eps; exists eps; rewrite Rminus_eq_0 Rabs_R0.
  intros; apply cond_pos.
Qed.

(** *** Extensionality *)

Lemma continuity_pt_ext_loc :
  forall f g x,
  locally x (fun x => f x = g x) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq Cf.
apply continuity_pt_filterlim in Cf.
apply continuity_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
by apply filterlim_ext_loc with f.
Qed.

Lemma continuity_pt_ext :
  forall f g x,
  (forall x, f x = g x) ->
  continuity_pt f x -> continuity_pt g x.
Proof.
intros f g x Heq.
apply continuity_pt_ext_loc.
by apply filter_forall.
Qed.

Lemma continuity_2d_pt_ext_loc :
  forall f g x y,
  locally_2d (fun u v => f u v = g u v) x y ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq Cf.
apply locally_2d_locally in Heq.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
rewrite -(locally_singleton _ _ Heq).
apply filterlim_ext_loc with (2 := Cf).
by apply Heq.
Qed.

Lemma continuity_2d_pt_ext :
  forall f g x y,
  (forall x y, f x y = g x y) ->
  continuity_2d_pt f x y -> continuity_2d_pt g x y.
Proof.
intros f g x y Heq.
apply continuity_2d_pt_ext_loc.
apply locally_2d_locally.
apply filter_forall.
now intros [u v].
Qed.

(** *** Composition *)

Lemma continuity_1d_2d_pt_comp :
  forall f g x y,
  continuity_pt f (g x y) ->
  continuity_2d_pt g x y ->
  continuity_2d_pt (fun x y => f (g x y)) x y.
Proof.
intros f g x y Cf Cg.
apply continuity_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
apply: filterlim_comp Cg Cf.
Qed.

(** *** Additive operators *)

Lemma continuity_2d_pt_opp (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  continuity_2d_pt (fun u v => - f u v) x y.
Proof.
apply continuity_1d_2d_pt_comp.
apply continuity_pt_opp.
apply continuity_pt_id.
Qed.

Lemma continuity_2d_pt_plus (f g : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  continuity_2d_pt g x y ->
  continuity_2d_pt (fun u v => f u v + g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
apply: filterlim_plus.
Qed.

Lemma continuity_2d_pt_minus (f g : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  continuity_2d_pt g x y ->
  continuity_2d_pt (fun u v => f u v - g u v) x y.
Proof.
  move => Cf Cg.
  apply continuity_2d_pt_plus.
  exact: Cf.
  by apply continuity_2d_pt_opp.
Qed.

(** *** Multiplicative operators *)

Lemma continuity_2d_pt_inv (f : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  f x y <> 0 ->
  continuity_2d_pt (fun u v => / f u v) x y.
Proof.
intros Cf Df.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim.
apply filterlim_comp with (1 := Cf).
apply (filterlim_Rbar_inv (f x y)).
contradict Df.
now injection Df.
Qed.

Lemma continuity_2d_pt_mult (f g : R -> R -> R) (x y : R) :
  continuity_2d_pt f x y ->
  continuity_2d_pt g x y ->
  continuity_2d_pt (fun u v => f u v * g u v) x y.
Proof.
intros Cf Cg.
apply continuity_2d_pt_filterlim in Cf.
apply continuity_2d_pt_filterlim in Cg.
apply continuity_2d_pt_filterlim.
eapply filterlim_comp_2.
apply Cf.
apply Cg.
by apply (filterlim_Rbar_mult (f x y) (g x y) (f x y * g x y)).
Qed.

(** * Continuity in Uniform Spaces *)

(** ** Continuity *)

Section Continuity.

Context {T U : UniformSpace}.

Definition continuous_on (D : T -> Prop) (f : T -> U) :=
  forall x, D x -> filterlim f (within D (locally x)) (locally (f x)).

Definition continuous (f : T -> U) (x : T) :=
  filterlim f (locally x) (locally (f x)).

Lemma continuous_continuous_on :
  forall (D : T -> Prop) (f : T -> U) (x : T),
  locally x D ->
  continuous_on D f ->
  continuous f x.
Proof.
intros D f x Dx CD P Pfx.
assert (Dx' := locally_singleton _ _ Dx).
generalize (filter_and _ _ Dx (CD x Dx' P Pfx)).
unfold filtermap, within.
apply filter_imp.
intros t [H1 H2].
now apply H2.
Qed.

Lemma continuous_on_subset :
  forall (D E : T -> Prop) (f : T -> U),
  (forall x, E x -> D x) ->
  continuous_on D f ->
  continuous_on E f.
Proof.
intros D E f H CD x Ex P Pfx.
generalize (CD x (H x Ex) P Pfx).
unfold filtermap, within.
apply filter_imp.
intros t H' Et.
now apply H', H.
Qed.

Lemma continuous_on_forall :
  forall (D : T -> Prop) (f : T -> U),
  (forall x, D x -> continuous f x) ->
  continuous_on D f.
Proof.
intros D f H x Dx P Pfx.
generalize (H x Dx P Pfx).
unfold filtermap, within.
now apply filter_imp.
Qed.

Lemma continuous_ext_loc (f g : T -> U) (x : T) :
  locally x (fun y : T => g y = f y)
  -> continuous g x -> continuous f x.
Proof.
  intros.
  eapply filterlim_ext_loc.
  by apply H.
  by rewrite -(locally_singleton _ _ H).
Qed.
Lemma continuous_ext :
  forall (f g : T -> U) (x : T),
  (forall x, f x = g x) ->
  continuous f x ->
  continuous g x.
Proof.
intros f g x H Cf.
apply filterlim_ext with (1 := H).
now rewrite <- H.
Qed.

Lemma continuous_on_ext :
  forall (D : T -> Prop) (f g : T -> U),
  (forall x, D x -> f x = g x) ->
  continuous_on D f ->
  continuous_on D g.
Proof.
intros D f g H Cf x Dx.
apply filterlim_within_ext with (1 := H).
rewrite <- H with (1 := Dx).
now apply Cf.
Qed.

End Continuity.

Lemma continuous_comp {U V W : UniformSpace} (f : U -> V) (g : V -> W) (x : U) :
  continuous f x -> continuous g (f x)
  -> continuous (fun x => g (f x)) x.
Proof.
  by apply filterlim_comp.
Qed.
Lemma continuous_comp_2 {U V W X : UniformSpace}
  (f : U -> V) (g : U -> W) (h : V -> W -> X) (x : U) :
  continuous f x -> continuous g x
  -> continuous (fun (x : V * W) => h (fst x) (snd x)) (f x,g x)
  -> continuous (fun x => h (f x) (g x)) x.
Proof.
  intros Cf Cg Ch.
  eapply filterlim_comp_2.
  by apply Cf.
  by apply Cg.
  apply filterlim_locally => eps.
  case: (proj1 (filterlim_locally _ _) Ch eps) => /= del Hdel.
  rewrite {1}/ball /= /prod_ball /= in Hdel.
  exists (fun y => ball (f x) (pos del) y) (fun y => ball (g x) (pos del) y).
  apply locally_ball.
  apply locally_ball.
  move => y z /= Hy Hz.
  apply (Hdel (y,z)).
  by split.
Qed.

Lemma is_lim_comp_continuous (f g : R -> R) (x : Rbar) (l : R) :
  is_lim f x l -> continuous g l
    -> is_lim (fun x => g (f x)) x (g l).
Proof.
  intros Hf Hg.
  apply filterlim_locally => eps.
  destruct (proj1 (filterlim_locally _ _) Hg eps) as [e He] ; clear Hg.
  eapply filter_imp.
  intros y Hy.
  apply He, Hy.
  by apply Hf, locally_ball.
Qed.

Lemma continuous_fst {U V : UniformSpace} (x : U) (y : V) :
  continuous (fst (B:=V)) (x, y).
Proof.
  intros P [d Hd].
  exists d => z [/= Hz1 Hz2].
  by apply Hd => /=.
Qed.
Lemma continuous_snd {U V : UniformSpace} (x : U) (y : V) :
  continuous (snd (B:=V)) (x, y).
Proof.
  intros P [d Hd].
  exists d => z [/= Hz1 Hz2].
  by apply Hd => /=.
Qed.

Lemma continuous_const {U V : UniformSpace} (c : V) (x : U) :
  continuous (fun _ => c) x.
Proof.
  apply filterlim_const.
Qed.

Lemma continuous_id {U : UniformSpace} (x : U) :
  continuous (fun y => y) x.
Proof.
  apply filterlim_id.
Qed.

Section Continuity_op.

Context {U : UniformSpace} {K : AbsRing} {V : NormedModule K}.

Lemma continuous_opp (f : U -> V) (x : U) :
  continuous f x ->
  continuous (fun x : U => opp (f x)) x.
Proof.
  intros.
  eapply filterlim_comp.
  by apply H.
  apply (filterlim_opp (f x)).
Qed.

Lemma continuous_plus (f g : U -> V) (x : U) :
  continuous f x -> continuous g x ->
  continuous (fun x : U => plus (f x) (g x)) x.
Proof.
  intros.
  eapply filterlim_comp_2.
  by apply H.
  by apply H0.
  apply (filterlim_plus (f x) (g x)).
Qed.

Lemma continuous_minus (f g : U -> V) (x : U) :
  continuous f x -> continuous g x ->
  continuous (fun x : U => minus (f x) (g x)) x.
Proof.
  intros.
  apply continuous_plus.
  apply H.
  by apply continuous_opp.
Qed.

Lemma continuous_scal (k : U -> K) (f : U -> V) (x : U) :
  continuous k x -> continuous f x -> continuous (fun y => scal (k y) (f y)) x.
Proof.
  intros.
  by eapply filterlim_comp_2, filterlim_scal.
Qed.
Lemma continuous_scal_r (k : K) (f : U -> V) (x : U) :
  continuous f x -> continuous (fun y => scal k (f y)) x.
Proof.
  intros.
  by apply continuous_comp, filterlim_scal_r.
Qed.
Lemma continuous_scal_l (f : U -> K) (k : V) (x : U) :
  continuous f x -> continuous (fun y => scal (f y) k) x.
Proof.
  intros.
  apply (continuous_comp f (fun y => scal y k)) => //.
  apply filterlim_scal_l.
Qed.

End Continuity_op.

Lemma continuous_mult {U : UniformSpace} {K : AbsRing}
  (f g : U -> K) (x : U) :
  continuous f x -> continuous g x
  -> continuous (fun y => mult (f y) (g y)) x.
Proof.
  intros.
  by eapply filterlim_comp_2, filterlim_mult.
Qed.

Section UnifCont.

Context {V : UniformSpace}.

Lemma unifcont_1d (f : R -> V) a b :
  (forall x, a <= x <= b -> continuous f x) ->
  forall eps : posreal, {delta : posreal | forall x y,
    a <= x <= b -> a <= y <= b -> ball x delta y -> ~~ ball (f x) eps (f y)}.
Proof.
  intros Cf eps.
  wlog: f Cf / (forall z : R, continuous f z) => [ Hw | {Cf} Cf ].
    destruct (C0_extension_le f a b) as [g [Cg Hg]].
    by apply Cf.
    destruct (Hw g) as [d Hd].
    intros x Hx ; apply Cg.
    apply Cg.
    exists d => x y Hx Hy Hxy.
    rewrite -!Hg //.
    by apply Hd.

  assert (forall (x : R), {delta : posreal | forall y : R,
    ball x delta y -> ~~ ball (f x) (pos_div_2 eps) (f y)}).
    move: (pos_div_2 eps) => {eps} eps x.
    assert (Rbar_lt 0 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
      case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
      move: (Lub.Lub_Rbar _) => l H1 H2.
      case: (proj1 (filterlim_locally _ _) (Cf x) eps) => d Hd.
      eapply Rbar_lt_le_trans, H1.
      by apply d.
      by apply Hd.
    assert (0 < Rbar_min 1 (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y)))).
      move: H ; case: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) => [l | | ] //= H0.
      apply Rmin_case => //.
      by apply Rlt_0_1.
      by apply Rlt_0_1.
    set d := mkposreal _ H0.
    exists d.
    unfold d ; clear d ; simpl.
    case: (Lub.Lub_Rbar_correct (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))).
    move: (Lub.Lub_Rbar (fun d => forall y : R, ball x d y -> ball (f x) eps (f y))) H => {H0} l H0 H1 H2 y Hy.
    contradict Hy.
    apply Rle_not_lt.
    apply (Rbar_le_trans (Finite _) l (Finite _)).
    case: (l) H0 => [r | | ] //= H0.
    apply Rmin_r.
    apply H2 => d /= Hd.
    apply Rnot_lt_le ; contradict Hy.
    by apply Hd.
  destruct (compactness_value_1d a b (fun x => pos_div_2 (proj1_sig (H x)))) as [d Hd].
  exists d => x y Hx Hy Hxy Hf.
  apply (Hd x Hx).
  case => {Hd} t [Ht].
  case: H => /= delta Hdelta [Htx Hdt].
  apply (Hdelta x).
    eapply ball_le, Htx.
    rewrite {2}(double_var delta).
    apply Rminus_le_0 ; ring_simplify.
    apply Rlt_le, is_pos_div_2.
  intro Hftx.
  apply (Hdelta y).
    rewrite (double_var delta).
    apply ball_triangle with x.
    apply Htx.
    by eapply ball_le, Hxy.
  contradict Hf.
  rewrite (double_var eps).
  eapply ball_triangle, Hf.
  by apply ball_sym.
Qed.

End UnifCont.

Section UnifCont_N.

Context {K : AbsRing} {V : NormedModule K}.

Lemma unifcont_normed_1d (f : R -> V) a b :
  (forall x, a <= x <= b -> continuous f x) ->
  forall eps : posreal, {delta : posreal | forall x y,
    a <= x <= b -> a <= y <= b -> ball x delta y -> ball_norm (f x) eps (f y)}.
Proof.
  intros H eps.
  assert (0 < eps / (@norm_factor _ V)).
    apply Rdiv_lt_0_compat.
    apply cond_pos.
    exact norm_factor_gt_0.
  destruct (unifcont_1d f a b H (mkposreal _ H0)) as [d Hd].
  exists d => x y Hx Hy Hxy.
  specialize (Hd x y Hx Hy Hxy).
  apply Rnot_le_lt.
  contradict Hd ; contradict Hd.
  apply Rlt_not_le.
  evar_last.
  apply norm_compat2, Hd.
  simpl ; field.
  apply Rgt_not_eq, norm_factor_gt_0.
Qed.

End UnifCont_N.
