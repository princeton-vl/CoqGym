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
Require Import Rbar Rcomplements Markov.

(** This file gives properties of (least) upper and (greatest) lower
bounds, especially in [Rbar].
- There are links between our bounds on [Rbar] and those of the
standard library on [R]: for example Lemma [Rbar_ub_R_ub] between our
[Rbar_is_upper_bound] and the standard library [is_upper_bound].
- From [Markov]'s principle, we deduce the construction of a lub (and
of a glb) in [Rbar] from any non-empty set of reals: see Lemma
[ex_lub_Rbar_ne].  *)

Open Scope R_scope.

(** * Bounds for sets in [R] *)
(** ** Upper and Lower bounds *)

Definition is_ub_Rbar (E : R -> Prop) (l : Rbar) :=
  forall (x : R), E x -> Rbar_le x l.
Definition is_lb_Rbar (E : R -> Prop) (l : Rbar) :=
  forall (x : R), E x -> Rbar_le l x.

Lemma is_ub_Rbar_opp (E : R -> Prop) (l : Rbar) :
  is_lb_Rbar E l <-> is_ub_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
  split ; intros Hl x Hx ; apply Rbar_opp_le.
  now rewrite Rbar_opp_involutive ; apply Hl.
  now apply Hl ; rewrite Ropp_involutive.
Qed.
Lemma is_lb_Rbar_opp (E : R -> Prop) (l : Rbar) :
  is_ub_Rbar E l <-> is_lb_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
  split ; intros Hl x Hx ; apply Rbar_opp_le.
  now rewrite Rbar_opp_involutive ; apply Hl.
  now apply Hl ; rewrite Ropp_involutive.
Qed.

(** Decidability *)

Lemma is_ub_Rbar_dec (E : R -> Prop) :
  {l : R | is_ub_Rbar E l} + {(forall l : R, ~is_ub_Rbar E l)}.
Proof.
  set (F (n : nat) (x : R) := x = 0 \/ (E x /\ x <= INR n)).
  assert (F_b : forall n, bound (F n)).
    intros ; exists (INR n) => x ; case => [-> | Hx].
    by apply pos_INR.
    by apply Hx.
  assert (F_ex : forall n, (exists x : R, F n x)).
    intros ; exists 0 ; by left.
  set (u (n : nat) := proj1_sig (completeness (F n) (F_b n) (F_ex n))).
  destruct (LPO_ub_dec u) as [ [M HM] | HM].
  + left ; exists M => x Hx.
    destruct (nfloor_ex (Rmax 0 x)) as [n Hn].
    by apply Rmax_l.
    eapply Rle_trans, (HM (S n)).
    rewrite /u ; case: completeness => l Hl /=.
    apply Hl ; right ; split => //.
    rewrite S_INR ; eapply Rle_trans, Rlt_le, Hn.
    by apply Rmax_r.
  + right => l Hl.
    case: (HM (Rmax 0 l)) => n {HM}.
    apply Rle_not_lt.
    rewrite /u ; case: completeness => M HM /=.
    apply HM => x ; case => [ -> | Hx].
    by apply Rmax_l.
    eapply Rle_trans, Rmax_r.
    apply Hl, Hx.
Qed.

Lemma is_lb_Rbar_dec (E : R -> Prop) :
  {l : R | is_lb_Rbar E l} + {(forall l : R, ~is_lb_Rbar E l)}.
Proof.
  destruct (is_ub_Rbar_dec (fun x => E (- x))) as [ [l Hl] | Hl ].
  left ; exists (Rbar_opp l).
  by apply is_ub_Rbar_opp ; rewrite (Rbar_opp_involutive l).
  right => l.
  specialize (Hl (Rbar_opp l)).
  contradict Hl.
  by apply (is_ub_Rbar_opp E l).
Qed.

(** Order *)

Lemma is_ub_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_ub_Rbar E1 l -> is_ub_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.
Lemma is_lb_Rbar_subset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lb_Rbar E1 l -> is_lb_Rbar E2 l.
Proof.
  move => H ub1 x Hx.
  apply: ub1 ; by apply: H.
Qed.

(** ** Least upper bound and Greatest Lower Bound *)

Definition is_lub_Rbar (E : R -> Prop) (l : Rbar) :=
  is_ub_Rbar E l /\ (forall b, is_ub_Rbar E b -> Rbar_le l b).
Definition is_glb_Rbar (E : R -> Prop) (l : Rbar) :=
  is_lb_Rbar E l /\ (forall b, is_lb_Rbar E b -> Rbar_le b l).

Lemma is_lub_Rbar_opp (E : R -> Prop) (l : Rbar) :
  is_glb_Rbar E l <-> is_lub_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
  split => [[lb glb] | [ub lub] ] ; split.
  by apply is_ub_Rbar_opp.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
  apply glb, is_ub_Rbar_opp ; by rewrite Rbar_opp_involutive.
  by apply is_ub_Rbar_opp.
  intros b Hb.
  apply Rbar_opp_le.
  by apply lub, is_ub_Rbar_opp.
Qed.
Lemma is_glb_Rbar_opp (E : R -> Prop) (l : Rbar) :
  is_lub_Rbar E l <-> is_glb_Rbar (fun x => E (- x)) (Rbar_opp l).
Proof.
  split => [[lb glb] | [ub lub] ] ; split.
  by apply is_lb_Rbar_opp.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive.
  apply glb, is_lb_Rbar_opp ; by rewrite Rbar_opp_involutive.
  by apply is_lb_Rbar_opp.
  intros b Hb.
  apply Rbar_opp_le.
  by apply lub, is_lb_Rbar_opp.
Qed.

(** Existence *)

Lemma ex_lub_Rbar (E : R -> Prop) : {l : Rbar | is_lub_Rbar E l}.
Proof.
  destruct (is_ub_Rbar_dec E)  as [[M HM] | HM] ; first last.
(* sup = p_infty *)
  exists p_infty ; split.
  by [].
  case => [l | | ] // Hl.
  by specialize (HM l).
  specialize (HM 0).
  contradict HM => x Hx.
  by specialize (Hl x Hx).

rename E into F.
  assert (F_b : bound F).
    exists M => x Hx.
    by apply HM.
    clear -F_b.

  set (E (m : nat) (x : R) := x = - INR m \/ F x).
  assert (E_b : forall m, bound (E m)).
    intros m.
    case: F_b => l Hl.
    exists (Rmax l (- INR m)) => x ; case => [ -> | Hx].
    by apply Rmax_r.
    eapply Rle_trans, Rmax_l.
    by apply Hl.
  assert (E_ex : forall m, exists x : R, E m x).
    intros m ; exists (- INR m) ; by left.
  set (u m := proj1_sig (completeness (E m) (E_b m) (E_ex m))).

  destruct (LPO (fun n => u n <> - INR n)) as [ [n Hn] | Hn].
    intros n.
    case: (Req_EM_T (u n) (- INR n)) => H.
    by right.
    by left.
  exists (u n).
  move: Hn ; rewrite /u ; case: completeness => l Hl /= H.
  split.
  intros x Hx.
  apply Hl ; by right.
  assert (- INR n < l).
  case: Hl => Hl _.
  case: (Hl (-INR n)) => //=.
  by left.
  intros H0 ; contradict H.
  by rewrite -H0.
  case => [b | | ] //= Hb.
  + apply Hl => x Hx.
    case: Hx => Hx ; first last.
    by apply Hb.
    rewrite Hx.
    apply Rnot_lt_le ; contradict H0.
    apply Rle_not_lt.
    apply Hl => y Hy.
    case: Hy => Hy.
    rewrite Hy ; apply Rle_refl.
    eapply Rle_trans, Rlt_le, H0.
    by apply Hb.
  + contradict H.
    apply Rle_antisym ; apply Hl.
    intros x Hx.
    case: Hx => [-> | Hx] //.
    by apply Rle_refl.
    by apply Hb in Hx.
    by left.
  assert (forall n, u n = - INR n).
    intros n.
    specialize (Hn n).
    case: (Req_dec (u n) (- INR n)) => // H.
    clear Hn.
  exists m_infty ; split => // x Hx.
  destruct (nfloor_ex (Rmax 0 (- x))) as [n Hn].
  by apply Rmax_l.
  specialize (H (S n)).
  contradict H.
  apply Rgt_not_eq.
  rewrite /u S_INR ; case: completeness => l Hl /=.
  eapply Rlt_le_trans with x.
  apply Ropp_lt_cancel ; rewrite Ropp_involutive.
  eapply Rle_lt_trans, Hn.
  by apply Rmax_r.
  apply Hl.
  by right.
Qed.
Lemma ex_glb_Rbar (E : R -> Prop) : {l : Rbar | is_glb_Rbar E l}.
Proof.
  case: (ex_lub_Rbar (fun x => E (- x))) => l Hl.
  exists (Rbar_opp l).
  apply is_lub_Rbar_opp ; by rewrite Rbar_opp_involutive.
Qed.

(** Functions *)

Definition Lub_Rbar (E : R -> Prop) := proj1_sig (ex_lub_Rbar E).
Definition Glb_Rbar (E : R -> Prop) := proj1_sig (ex_glb_Rbar E).

Lemma is_lub_Rbar_unique (E : R -> Prop) (l : Rbar) :
  is_lub_Rbar E l -> Lub_Rbar E = l.
Proof.
  move => Hl ; rewrite /Lub_Rbar ; case: ex_lub_Rbar => l' /= Hl'.
  apply Rbar_le_antisym.
  by apply Hl', Hl.
  by apply Hl, Hl'.
Qed.
Lemma is_glb_Rbar_unique (E : R -> Prop) (l : Rbar) :
  is_glb_Rbar E l -> Glb_Rbar E = l.
Proof.
  move => Hl ; rewrite /Glb_Rbar ; case: ex_glb_Rbar => l' /= Hl'.
  apply Rbar_le_antisym.
  by apply Hl, Hl'.
  by apply Hl', Hl.
Qed.

Lemma Lub_Rbar_correct (E : R -> Prop) :
  is_lub_Rbar E (Lub_Rbar E).
Proof.
  rewrite /Lub_Rbar ; by case: ex_lub_Rbar => l /= Hl.
Qed.
Lemma Glb_Rbar_correct (E : R -> Prop) :
  is_glb_Rbar E (Glb_Rbar E).
Proof.
  rewrite /Glb_Rbar ; by case: ex_glb_Rbar => l /= Hl.
Qed.

(** Order *)

Lemma is_lub_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_lub_Rbar E1 l1 -> is_lub_Rbar E2 l2
    -> Rbar_le l2 l1.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_ub_Rbar_subset E1), ub1.
Qed.
Lemma is_glb_Rbar_subset (E1 E2 : R -> Prop) (l1 l2 : Rbar) :
  (forall x : R, E2 x -> E1 x) -> is_glb_Rbar E1 l1 -> is_glb_Rbar E2 l2
    -> Rbar_le l1 l2.
Proof.
  move => H [ub1 _] [_ lub2].
  apply: lub2 ; by apply (is_lb_Rbar_subset E1), ub1.
Qed.

Lemma is_lub_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_lub_Rbar E1 l -> is_lub_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_ub_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_ub_Rbar_subset E2) ; [apply H | apply Hb].
Qed.
Lemma is_glb_Rbar_eqset (E1 E2 : R -> Prop) (l : Rbar) :
  (forall x : R, E2 x <-> E1 x) -> is_glb_Rbar E1 l -> is_glb_Rbar E2 l.
Proof.
  move => H [ub1 lub1] ; split.
  apply (is_lb_Rbar_subset E1) ; [apply H | apply ub1].
  move => b Hb ; apply: lub1 ; apply (is_lb_Rbar_subset E2) ; [apply H | apply Hb].
Qed.

Lemma Lub_Rbar_eqset (E1 E2 : R -> Prop) :
  (forall x, E1 x <-> E2 x) -> Lub_Rbar E1 = Lub_Rbar E2.
Proof.
  move => H ; rewrite {2}/Lub_Rbar ;
  case: ex_lub_Rbar => l /= Hl.
  apply is_lub_Rbar_unique.
  move: Hl ; by apply is_lub_Rbar_eqset.
Qed.
Lemma Glb_Rbar_eqset (E1 E2 : R -> Prop) :
  (forall x, E1 x <-> E2 x) -> Glb_Rbar E1 = Glb_Rbar E2.
Proof.
  move => H ; rewrite {2}/Glb_Rbar ;
  case: (ex_glb_Rbar E2) => l2 H2 /=.
  apply is_glb_Rbar_unique.
  move: H2 ; by apply is_glb_Rbar_eqset.
Qed.

(** * Bounds for sets in [Rbar] *)
(** ** Upper and Lower bounds *)

Definition Rbar_is_upper_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le x l.

Definition Rbar_is_lower_bound (E : Rbar -> Prop) (l : Rbar) :=
  forall x, E x -> Rbar_le l x.

Lemma Rbar_ub_lb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_upper_bound (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_lower_bound E l.
Proof.
  split => Hl x Hx.
  apply Rbar_opp_le.
  apply Hl.
  by rewrite Rbar_opp_involutive.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  by apply Hl.
Qed.
Lemma Rbar_lb_ub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lower_bound (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_upper_bound E l.
Proof.
  split => Hl x Hx.
  apply Rbar_opp_le.
  apply Hl.
  by rewrite Rbar_opp_involutive.
  apply Rbar_opp_le.
  rewrite Rbar_opp_involutive.
  by apply Hl.
Qed.

Lemma is_ub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_ub_Rbar E l <-> Rbar_is_upper_bound (fun x => is_finite x /\ E x) l.
Proof.
  split => [H x [<- Hx] | H x Hx] ; apply H => // ;
  by exists x.
Qed.
Lemma is_lb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lb_Rbar E l <-> Rbar_is_lower_bound (fun x => is_finite x /\ E x) l.
Proof.
  split => [H x [<- Hx] | H x Hx] ; apply H => // ;
  by exists x.
Qed.

(** Basic properties *)

Lemma Rbar_ub_p_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E p_infty.
Proof.
  now intros [x| |] Hx.
Qed.
Lemma Rbar_lb_m_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E m_infty.
Proof.
  easy.
Qed.

Lemma Rbar_ub_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_upper_bound E l ->
    is_upper_bound (fun (x : R) => E x) l.
Proof.
  intros H x Ex.
  now apply (H (Finite x)).
Qed.
Lemma Rbar_lb_Finite (E : Rbar -> Prop) (l : R) :
  Rbar_is_lower_bound E (Finite l) ->
    is_upper_bound (fun x => E (Finite (- x))) (- l).
Proof.
  intros H x Ex.
  apply Ropp_le_cancel ; rewrite Ropp_involutive ;
  now apply (H (Finite (-x))).
Qed.

Lemma Rbar_ub_m_infty (E : Rbar -> Prop) :
  Rbar_is_upper_bound E m_infty -> forall x, E x -> x = m_infty.
Proof.
  intros H [x| |] Hx ;
  now specialize (H _ Hx).
Qed.
Lemma Rbar_lb_p_infty (E : Rbar -> Prop) :
  Rbar_is_lower_bound E p_infty -> (forall x, E x -> x = p_infty).
Proof.
  intros H x ;
  case x ; auto ; clear x ; [intros x| ] ; intros Hx.
  case (H _ Hx) ; simpl ; intuition.
  case (H _ Hx) ; simpl ; intuition.
Qed.

Lemma Rbar_lb_le_ub (E : Rbar -> Prop) (l1 l2 : Rbar) : (exists x, E x) ->
  Rbar_is_lower_bound E l1 -> Rbar_is_upper_bound E l2 -> Rbar_le l1 l2.
Proof.
  intros (x, Hex) Hl Hu ;
  apply Rbar_le_trans with (y := x) ; [apply Hl | apply Hu] ; auto.
Qed.
Lemma Rbar_lb_eq_ub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lower_bound E l -> Rbar_is_upper_bound E l -> forall x, E x -> x = l.
Proof.
  intros Hl Hu x Hx.
  apply Rbar_le_antisym ; [apply Hu | apply Hl] ; auto.
Qed.

(** Decidability *)

Lemma Rbar_ub_dec (E : Rbar -> Prop) (Hp : ~ E p_infty) :
  {M : R | Rbar_is_upper_bound E M}
    + {(forall (M : R), ~Rbar_is_upper_bound E M)}.
Proof.
  destruct (is_ub_Rbar_dec E) as [ [M HM] | HM ].
  left ; exists M ; case => [x | | ] //= Hx.
  by apply HM.
  right => M.
  specialize (HM M).
  contradict HM => x Hx.
  by apply HM.
Qed.
Lemma Rbar_lb_dec (E : Rbar -> Prop) (Hm : ~ E m_infty) :
  {M : R | Rbar_is_lower_bound E (Finite M)}
    + {(forall M, ~Rbar_is_lower_bound E (Finite M))}.
Proof.
  destruct (Rbar_ub_dec (fun x => E (Rbar_opp x)) Hm) as [(M, H)|H].
  left ; exists (-M).
  apply Rbar_ub_lb ; simpl ; rewrite (Ropp_involutive M) ; auto.
  right ; intro M ; generalize (H (-M)) ; clear H ; intro H ; contradict H ;
  apply (Rbar_ub_lb E (Finite M)) ; auto.
Qed.

(** Order *)

Lemma Rbar_is_ub_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_upper_bound E2 l) -> (Rbar_is_upper_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.
Lemma Rbar_is_lb_subset (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lower_bound E2 l) -> (Rbar_is_lower_bound E1 l).
Proof.
  intros Hs Hl x Ex ; apply Hl, Hs ; auto.
Qed.

(** ** Least upper bound and Greatest Lower Bound *)

Definition Rbar_is_lub (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_upper_bound E l /\
    (forall b : Rbar, Rbar_is_upper_bound E b -> Rbar_le l b).
Definition Rbar_is_glb (E : Rbar -> Prop) (l : Rbar) :=
  Rbar_is_lower_bound E l /\
    (forall b : Rbar, Rbar_is_lower_bound E b -> Rbar_le b l).

Lemma Rbar_lub_glb (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lub (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_glb E l.
Proof.
  split ; [intros (ub, lub) | intros (lb, glb)] ; split.
  apply Rbar_ub_lb ; auto.
  intros b Hb ; generalize (lub _ (proj2 (Rbar_ub_lb _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_lb_ub ; intros x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply lb.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply glb, Rbar_ub_lb ;
  rewrite Rbar_opp_involutive ; auto.
Qed.
Lemma Rbar_glb_lub (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_glb (fun x => E (Rbar_opp x)) (Rbar_opp l)
    <-> Rbar_is_lub E l.
Proof.
  split ; [ intros (lb, glb) | intros (ub, lub)] ; split.
  apply Rbar_lb_ub ; auto.
  intros b Hb ; generalize (glb _ (proj2 (Rbar_lb_ub _ _) Hb)) ; apply Rbar_opp_le.
  apply Rbar_ub_lb ; intro x ; simpl ; repeat rewrite Rbar_opp_involutive ; apply ub.
  intros b Hb.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply lub, Rbar_lb_ub ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

Lemma is_lub_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_lub_Rbar E l <-> Rbar_is_lub (fun x => is_finite x /\ E x) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_ub_Rbar_correct.
Qed.
Lemma is_glb_Rbar_correct (E : R -> Prop) (l : Rbar) :
  is_glb_Rbar E l <-> Rbar_is_glb (fun x => is_finite x /\ E x) l.
Proof.
  split => [[Hub Hlub]|[Hub Hlub]].
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
  split ; [ | move => b Hb ; apply Hlub ] ; by apply is_lb_Rbar_correct.
Qed.

Lemma Rbar_ex_lub (E : Rbar -> Prop) :
  {l : Rbar | Rbar_is_lub E l}.
Proof.
  destruct (EM_dec (E p_infty)) as [Hp|Hp].
  exists p_infty ; split.
  by case.
  intros b Hb.
  apply Rbar_not_lt_le.
  contradict Hp => H.
  apply: Rbar_le_not_lt Hp.
  by apply Hb.
  destruct (ex_lub_Rbar E) as [l Hl].
  exists l ; split.
  case => [x | | ] // Hx.
  by apply Hl.
  intros b Hb.
  apply Hl => x Hx.
  by apply Hb.
Qed.

Lemma Rbar_ex_glb (E : Rbar -> Prop) :
  {l : Rbar | Rbar_is_glb E l}.
Proof.
  destruct (Rbar_ex_lub (fun x => E (Rbar_opp x))) as [l Hl].
  exists (Rbar_opp l).
  now apply Rbar_lub_glb ; rewrite Rbar_opp_involutive.
Qed.

(** Functions *)

Definition Rbar_lub (E : Rbar -> Prop)
  := proj1_sig (Rbar_ex_lub E).
Definition Rbar_glb (E : Rbar -> Prop)
  := proj1_sig (Rbar_ex_glb E).

Lemma Rbar_opp_glb_lub (E : Rbar -> Prop) :
  Rbar_glb (fun x => E (Rbar_opp x)) = Rbar_opp (Rbar_lub E).
Proof.
  unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g [Hg Hg'] ;
  unfold Rbar_lub ; case (Rbar_ex_lub _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hl', Rbar_lb_ub ;
  rewrite Rbar_opp_involutive ; auto.
  apply Hg', Rbar_lb_ub ; auto.
Qed.
Lemma Rbar_opp_lub_glb (E : Rbar -> Prop) :
  Rbar_lub (fun x => E (Rbar_opp x)) = Rbar_opp (Rbar_glb E).
Proof.
  unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g (Hg, Hg') ;
  unfold Rbar_lub ; case (Rbar_ex_lub _) ; simpl ; intros l [Hl Hl'] ;
  apply Rbar_le_antisym.
  apply Hl', Rbar_lb_ub ; rewrite Rbar_opp_involutive ;
  apply (Rbar_is_lb_subset _ E) ; auto ; intros x ; rewrite Rbar_opp_involutive ; auto.
  apply Rbar_opp_le ; rewrite Rbar_opp_involutive ; apply Hg', Rbar_ub_lb ;
  rewrite Rbar_opp_involutive ; auto.
Qed.

Lemma Rbar_is_lub_unique (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_lub E l -> Rbar_lub E = l.
Proof.
  move => H.
  rewrite /Rbar_lub.
  case: Rbar_ex_lub => l0 H0 /=.
  apply Rbar_le_antisym.
  apply H0, H.
  apply H, H0.
Qed.
Lemma Rbar_is_glb_unique (E : Rbar -> Prop) (l : Rbar) :
  Rbar_is_glb E l -> Rbar_glb E = l.
Proof.
  move => H.
  rewrite /Rbar_glb.
  case: Rbar_ex_glb => l0 H0 /=.
  apply Rbar_le_antisym.
  apply H, H0.
  apply H0, H.
Qed.

(** Order *)

Lemma Rbar_glb_le_lub (E : Rbar -> Prop) :
  (exists x, E x) -> Rbar_le (Rbar_glb E) (Rbar_lub E).
Proof.
  case => x Hex.
  apply Rbar_le_trans with x.
  unfold Rbar_glb ; case (Rbar_ex_glb _) ; simpl ; intros g (Hg, _) ; apply Hg ; auto.
  unfold Rbar_lub ; case (Rbar_ex_lub _) ; simpl ; intros l (Hl, _) ; apply Hl ; auto.
Qed.

Lemma Rbar_is_lub_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x -> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (_,H1) (H2, _).
  apply H1 ; intros x Hx ; apply H2, Hs, Hx.
Qed.
Lemma Rbar_is_glb_subset (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E2 x -> E1 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> Rbar_le l1 l2.
Proof.
  intros Hs (H1, _) (_, H2).
  apply H2 ; intros x Hx ; apply H1, Hs, Hx.
Qed.

Lemma Rbar_is_lub_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l1) -> (Rbar_is_lub E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ;
  [apply (Rbar_is_lub_subset E1 E2) | apply (Rbar_is_lub_subset E2 E1) ] ; auto ; intros x H ;
  apply Hs ; auto.
Qed.
Lemma Rbar_is_glb_eq (E1 E2 : Rbar -> Prop) (l1 l2 : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l1) -> (Rbar_is_glb E2 l2)
  -> l1 = l2.
Proof.
  intros Hs H1 H2 ; apply Rbar_le_antisym ;
  [apply (Rbar_is_glb_subset E1 E2) | apply (Rbar_is_glb_subset E2 E1) ] ; auto ; intros x H ;
  apply Hs ; auto.
Qed.

Lemma Rbar_is_lub_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_lub E1 l) -> (Rbar_is_lub E2 l).
Proof.
  intros Heq (H1,H2) ; split.
  apply (Rbar_is_ub_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_ub_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.
Lemma Rbar_is_glb_ext (E1 E2 : Rbar -> Prop) (l : Rbar) :
  (forall x, E1 x <-> E2 x) -> (Rbar_is_glb E1 l) -> (Rbar_is_glb E2 l).
Proof.
  intros Heq (H1, H2) ; split.
  apply (Rbar_is_lb_subset _ E1) ; auto ; intros x Hx ; apply Heq ; auto.
  intros b Hb ; apply H2 ; apply (Rbar_is_lb_subset _ E2) ; auto ; intros x Hx ; apply Heq ; auto.
Qed.

Lemma Rbar_lub_subset (E1 E2 : Rbar -> Prop) :
  (forall x, E1 x -> E2 x) -> Rbar_le (Rbar_lub E1) (Rbar_lub E2).
Proof.
  intros Hs ; unfold Rbar_lub ; case (Rbar_ex_lub E1) ; intros l1 Hl1 ;
  case (Rbar_ex_lub E2) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_lub_subset E1 E2) ; auto.
Qed.
Lemma Rbar_glb_subset (E1 E2 : Rbar -> Prop) :
  (forall x, E2 x -> E1 x) -> Rbar_le (Rbar_glb E1) (Rbar_glb E2).
Proof.
  intro Hs ; unfold Rbar_glb ; case (Rbar_ex_glb E1) ; intros l1 Hl1 ;
  case (Rbar_ex_glb E2) ; simpl ; intros l2 Hl2 ; apply (Rbar_is_glb_subset E1 E2) ; auto.
Qed.

Lemma Rbar_lub_rw (E1 E2 : Rbar -> Prop) :
  (forall x, E1 x <-> E2 x) -> Rbar_lub E1 = Rbar_lub E2.
Proof.
  intro Hs ; apply Rbar_le_antisym ; apply Rbar_lub_subset ; intros x H ; apply Hs ; auto.
Qed.
Lemma Rbar_glb_rw (E1 E2 : Rbar -> Prop) :
  (forall x, E1 x <-> E2 x) -> Rbar_glb E1 = Rbar_glb E2.
Proof.
  intros Hs ; apply Rbar_le_antisym ; apply Rbar_glb_subset ; intros x H ; apply Hs ; auto.
Qed.

(** * Emptiness is decidable *)

Definition Empty (E : R -> Prop) :=
  Lub_Rbar (fun x => x = 0 \/ E x) = Glb_Rbar (fun x => x = 0 \/ E x)
  /\ Lub_Rbar (fun x => x = 1 \/ E x) = Glb_Rbar (fun x => x = 1 \/ E x).

Lemma Empty_correct_1 (E : R -> Prop) :
  Empty E -> forall x, ~ E x.
Proof.
  case => E0 E1 x Ex.
  rewrite /Lub_Rbar /Glb_Rbar in E0 ;
  case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) E0 => /= s0 Hs0 ;
  case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /= E0.
  have : (x = 0) ; last move => {s0 Hs0 i0 Hi0 E0}.
  apply Rle_antisym.
  apply (Rbar_le_trans x s0 0).
  apply Hs0 ; by right.
  rewrite E0 ; apply Hi0 ; by left.
  apply (Rbar_le_trans 0 s0 x).
  apply Hs0 ; by left.
  rewrite E0 ; apply Hi0 ; by right.
  rewrite /Lub_Rbar /Glb_Rbar in E1 ;
  case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) E1 => /= s1 Hs1 ;
  case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /= E1.
  have : (x = 1) ; last move => {s1 Hs1 i1 Hi1 E1}.
  apply Rle_antisym.
  apply (Rbar_le_trans x s1 1).
  apply Hs1 ; by right.
  rewrite E1 ; apply Hi1 ; by left.
  apply (Rbar_le_trans 1 s1 x).
  apply Hs1 ; by left.
  rewrite E1 ; apply Hi1 ; by right.
  move => -> ; apply R1_neq_R0.
Qed.

Lemma Empty_correct_2 (E : R -> Prop) :
  (forall x, ~ E x) -> Empty E.
Proof.
  move => H ; split ;
  rewrite /Glb_Rbar /Lub_Rbar ;
  [ case : (ex_lub_Rbar (fun x : R => x = 0 \/ E x)) => s0 Hs0 ;
  case : (ex_glb_Rbar (fun x : R => x = 0 \/ E x)) => i0 Hi0 /=
  | case : (ex_lub_Rbar (fun x : R => x = 1 \/ E x)) => s1 Hs1 ;
  case : (ex_glb_Rbar (fun x : R => x = 1 \/ E x)) => i1 Hi1 /=].
  have : (i0 = Finite 0) ; last move => -> ;
  apply: Rbar_le_antisym.
  apply Hi0 ; by left.
  apply Hi0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 => y ; case => H0.
  rewrite H0 ; by right.
  contradict H0 ; apply H.
  apply Hs0 ; by left.
  have : (i1 = Finite 1) ; last move => -> ;
  apply: Rbar_le_antisym.
  apply Hi1 ; by left.
  apply Hi1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 => y ; case => H1.
  rewrite H1 ; by right.
  contradict H1 ; apply H.
  apply Hs1 ; by left.
Qed.

Lemma Empty_dec (E : R -> Prop) :
  {~Empty E}+{Empty E}.
Proof.
  case: (Rbar_eq_dec (Lub_Rbar (fun x => x = 0 \/ E x)) (Glb_Rbar (fun x => x = 0 \/ E x))) => H0 ;
    [ | left].
  case: (Rbar_eq_dec (Lub_Rbar (fun x => x = 1 \/ E x)) (Glb_Rbar (fun x => x = 1 \/ E x))) => H1 ;
    [by right | left].
  contradict H1 ; apply H1.
  contradict H0 ; apply H0.
Qed.
Lemma not_Empty_dec (E : R -> Prop) : (Decidable.decidable (exists x, E x)) ->
  {(exists x, E x)} + {(forall x, ~ E x)}.
Proof.
  move => He ;
  case: (Empty_dec E) => Hx ;
  [left|right].
  case: He => // He.
  contradict Hx ;
  apply: Empty_correct_2 => x ; contradict He ; by exists x.
  by apply: Empty_correct_1.
Qed.

Lemma uniqueness_dec P : (exists ! x : R, P x) -> {x : R | P x}.
Proof.
  move => H.
  exists (Lub_Rbar P).
  case: H => x Hx.
  replace (real (Lub_Rbar P)) with (real (Finite x)).
  by apply Hx.
  apply f_equal, sym_eq, is_lub_Rbar_unique.
  split.
  move => y Hy.
  right ; by apply sym_eq, Hx.
  move => b Hb.
  by apply Hb, Hx.
Qed.
