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
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq SF_seq.
Require Import Continuity Hierarchy.

(** This file contains the definition and properties of the Riemann
integral, defined on a normed module on [R]. For real functions, a
total function [RInt] is available. *)

Section is_RInt.

(** * Definition of Riemann integral *)

Context {V : NormedModule R_AbsRing}.

Definition is_RInt (f : R -> V) (a b : R) (If : V) :=
  filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (Riemann_fine a b) (locally If).

Definition ex_RInt (f : R -> V) (a b : R) :=
  exists If : V, is_RInt f a b If.

(** ** Usual properties *)
(** The integral between a and a is null *)

Lemma is_RInt_point :
  forall (f : R -> V) (a : R),
  is_RInt f a a zero.
Proof.
intros f a.
apply filterlim_locally.
move => eps ; exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
rewrite Riemann_sum_zero.
rewrite scal_zero_r.
by apply ball_center.
by apply ptd_sort.
move: Hl Hh ; rewrite /Rmin /Rmax ;
by case: Rle_dec (Rle_refl a) => _ _ ->.
Qed.

Lemma ex_RInt_point :
  forall (f : R -> V) a,
  ex_RInt f a a.
Proof.
intros f a.
exists zero ; by apply is_RInt_point.
Qed.

(** Swapping bounds *)

Lemma is_RInt_swap :
  forall (f : R -> V) (a b : R) (If : V),
  is_RInt f b a If -> is_RInt f a b (opp If).
Proof.
  unfold is_RInt.
  intros f a b If HIf.
  rewrite -scal_opp_one /=.
  apply filterlim_ext with
    (fun ptd => scal (opp (one : R)) (scal (sign (a - b)) (Riemann_sum f ptd))).
  intros x.
  rewrite scal_assoc.
  apply (f_equal (fun s => scal s _)).
  rewrite /mult /opp /one /=.
  by rewrite -(Ropp_minus_distr' b a) sign_opp /= Ropp_mult_distr_l_reverse Rmult_1_l.
  unfold Riemann_fine.
  rewrite Rmin_comm Rmax_comm.
  apply filterlim_comp with (1 := HIf).
  apply: filterlim_scal_r.
Qed.

Lemma ex_RInt_swap :
  forall (f : R -> V) (a b : R),
  ex_RInt f a b -> ex_RInt f b a.
Proof.
  intros f a b.
  case => If HIf.
  exists (opp If).
  now apply is_RInt_swap.
Qed.

(** Integrable implies bounded *)

Lemma ex_RInt_ub (f : R -> V) (a b : R) :
  ex_RInt f a b -> exists M : R, forall t : R,
    Rmin a b <= t <= Rmax a b -> norm (f t) <= M.
Proof.
  wlog: a b / (a < b) => [ Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite /Rmin /Rmax ; case: Rle_dec (Req_le _ _ Hab) => // _ _ ;
    rewrite -Hab.
    exists (norm (f a)) => t Ht ; replace t with a.
    exact: Rle_refl.
    apply Rle_antisym ; by case: Ht.
    rewrite Rmin_comm Rmax_comm ;
    apply ex_RInt_swap in Hex ; by apply Hw.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.

  case: Hex => If Hex.
  generalize (proj1 (filterlim_locally_ball_norm _ If) Hex) => {Hex} /= Hex.
  case: (Hex (mkposreal _ Rlt_0_1)) => {Hex} alpha Hex.
  have Hn : 0 <= ((b-a)/alpha).
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set n := (nfloor _ Hn).
  set ptd := fun (g : R -> R -> R) =>
    SF_seq_f2 g (unif_part a b n).

  assert (forall g, pointed_subdiv (ptd g) ->
    norm (minus (Riemann_sum f (ptd g)) If) < 1).
    move => g Hg ; replace (Riemann_sum f (ptd g))
      with (scal (sign (b - a)) (Riemann_sum f (ptd g))).
  apply Hex.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  clearbody n ; rewrite SF_lx_f2.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  suff : forall i, (S i < size (unif_part a b n))%nat ->
    nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b-a)/(INR n + 1).
  elim: (unif_part a b n) => [ /= _ | x0].
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  case => /= [ | x1 s] IH Hnth.
  apply Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  replace (seq_step _)
    with (Rmax (Rabs (x1 - x0)) (seq_step (x1 :: s))) by auto.
  apply Rmax_case_strong => _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  exact: Rle_refl.
  apply Rle_ge, Rdiv_le_0_compat ; [ by apply Rlt_le, Rgt_minus | by intuition ].
  apply IH => i Hi ; exact: (Hnth (S i) (lt_n_S _ _ Hi)).
  rewrite size_mkseq => i Hi.
  rewrite ?nth_mkseq ?S_INR ; try apply SSR_leq.
  field ; apply Rgt_not_eq ; by intuition.
  exact: lt_le_weak.
  exact: Hi.
  by apply lt_O_Sn.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
  by apply Hn'.
  split.
  apply Hg.
  rewrite -> Rmin_left, Rmax_right by now apply Rlt_le.
  split.
  apply head_unif_part.
  clearbody n ; rewrite /Rmax -nth_last SF_lx_f2.
  rewrite size_mkseq nth_mkseq ?S_INR //.
  field ; apply Rgt_not_eq ;
  by intuition.
  by apply lt_O_Sn.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  exact: scal_one.
  move: H => {Hex} Hex.

  assert (exists M, forall g : R -> R -> R,
    pointed_subdiv (ptd g) -> norm (Riemann_sum f (ptd g)) <= M).
    exists (norm If + 1) ; move => g Hg.
    replace (Riemann_sum f (ptd g))
      with (plus (minus (Riemann_sum f (ptd g)) If) If).
    apply Rle_trans with (norm (minus (Riemann_sum f (ptd g)) If) + norm If).
    by generalize (norm_triangle (minus (Riemann_sum f (ptd g)) If) If).
    rewrite Rplus_comm.
    apply Rplus_le_compat_l.
    apply Rlt_le.
    by apply Hex.
    by rewrite /minus -plus_assoc plus_opp_l plus_zero_r.
  clearbody n ; move: H => {Hex} Hex.

  assert (forall i, (S i < size (unif_part a b n))%nat ->
    exists M, forall t,
      nth 0 (unif_part a b n) i <= t <= nth 0 (unif_part a b n) (S i)
      -> norm (f t) <= M).
    move => i ; revert ptd Hex.
    have : sorted Rlt (unif_part a b n).
      apply sorted_nth => j Hj x0.
      rewrite size_mkseq /= in Hj.
      rewrite ?nth_mkseq ?S_INR /= ; try apply SSR_leq.
      apply Rminus_gt ; field_simplify.
      rewrite Rplus_comm Rdiv_1 ; apply Rdiv_lt_0_compat.
      exact: Rgt_minus.
      by intuition.
      apply Rgt_not_eq ; by intuition.
      by intuition.
      by intuition.
    elim: (unif_part a b n) i => [ /= i _ _ Hi | x0].
    by apply lt_n_O in Hi.
    case => [ /= _ i _ _ Hi | x1 s IH].
    by apply lt_S_n, lt_n_O in Hi.
    case => [ | i] Hlt /= Hex Hi.
    assert (exists M, forall t g, x0 <= t <= x1 ->
      pointed_subdiv (SF_seq_f2 g [:: x1 & s]) ->
      norm (plus (scal (x1 - x0) (f t)) (Riemann_sum f (SF_seq_f2 g [:: x1 & s]))) <= M).
    case: (Hex) => M Hex'.
    exists M ;
    move => t g Ht Hg.
    set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ =>  t
        | right _ => g x y
      end.
    replace (plus (scal (x1 - x0) (f t)) (Riemann_sum f (SF_seq_f2 g (x1 :: s))))
      with (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s])).
    apply Hex'.
    case => [ | j] Hj ; rewrite SF_size_f2 /= in Hj ;
    rewrite SF_ly_f2 SF_lx_f2 /=.
    2: apply lt_O_Sn.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    rewrite (nth_pairmap 0).
    rewrite /g0.
    suff : (nth 0 (x1 :: s) j) <> x0.
    case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 ; rewrite SF_ly_f2 SF_lx_f2 /=.
    2: apply lt_O_Sn.
    rewrite (nth_pairmap 0).
    move => Hg' ; by apply Hg', lt_S_n.
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    apply lt_S_n in Hj.
    elim: j Hj => {IH} [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    by apply lt_0_Sn.
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (refl_equal x0).
    case: s Hlt {IH Hex Hex' Hi Hg} => [ | x2 s] Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    elim: s x2 Hlt => [ | x3 s IH] x2 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x2) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    apply f_equal.
    rewrite /g0.
    by case: Req_EM_T (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))).
    apply IH.
    split.
    by apply Hlt.
    split.
    apply Rlt_trans with x2 ; by apply Hlt.
    by apply Hlt.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
    by apply lt_O_Sn.
  move: H => {Hex} Hex.
  case: (Hex) => M Hex'.
  exists ((M + norm (Riemann_sum f (SF_seq_f2 (fun x y => x) (x1 :: s)))) / abs (x1 - x0)).
  move => t Ht.
  have Hg : pointed_subdiv (SF_seq_f2 (fun x y : R => x) (x1 :: s)).
    move => j ; rewrite SF_size_f2 SF_lx_f2.
    rewrite SF_ly_f2 /= => Hj.
    rewrite (nth_pairmap 0).
    split.
    apply Rle_refl.
    apply Rlt_le, (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by [].
    apply SSR_leq ; by intuition.
    apply lt_O_Sn.
  specialize (Hex' _ _ Ht Hg).
  rewrite -(scal_one (f t)).
  rewrite /one /= -(Rinv_l (x1 - x0)).
  2: by apply Rgt_not_eq, Rgt_minus, Hlt.
  rewrite -scal_assoc.
  eapply Rle_trans ; try apply @norm_scal.
  rewrite Rmult_comm.
  rewrite /abs /= Rabs_Rinv.
  2: by apply Rgt_not_eq, Rgt_minus, Hlt.
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat.
  apply Rabs_pos_lt, Rgt_not_eq.
  by apply Rgt_minus, Hlt.
  set v:= scal _ _.
  replace v
    with (minus (plus (scal (x1 - x0) (f t))
            (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s))))
            (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s)))).
  rewrite /minus.
  apply Rle_trans with (norm (plus (scal (x1 - x0) (f t))
        (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s))))
        + norm (opp (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s))))).
  by generalize (norm_triangle (plus (scal (x1 - x0) (f t))
        (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s))))
     (opp (Riemann_sum f (SF_seq_f2 (fun x _ : R => x) (x1 :: s))))).
  rewrite norm_opp.
  apply Rplus_le_compat_r.
  apply Hex'.
  rewrite /minus -plus_assoc plus_opp_r.
  by apply plus_zero_r.
  apply IH.
  by apply Hlt.
  case: Hex => M Hex.
  exists ((M + norm (scal (x1 - x0) (f x0)))) => g Hg.
  set g0 := fun x y =>
      match Req_EM_T x x0 with
        | left _ => x0
        | right _ => g x y
      end.
  have Hg0 : pointed_subdiv (SF_seq_f2 g0 (x0::x1 :: s)).
    move => j ; rewrite SF_size_f2 SF_lx_f2.
    2: apply lt_O_Sn.
    rewrite SF_ly_f2 => Hj.
    rewrite nth_behead (nth_pairmap 0) /=.
    case: j Hj => /= [ | j ] Hj.
    rewrite /g0.
    case: Req_EM_T (refl_equal x0) => // _ _.
    split.
    exact: Rle_refl.
    by apply Rlt_le, Hlt.
    suff : (nth 0 (x1 :: s) j) <> x0.
    rewrite /g0 ; case: Req_EM_T => // _ _.
    move: (Hg j).
    rewrite SF_size_f2 SF_lx_f2.
    2: apply lt_O_Sn.
    rewrite SF_ly_f2 /= => {Hg} Hg.
    move: (Hg (lt_S_n _ _ Hj)) ; rewrite (nth_pairmap 0).
    by [].
    apply SSR_leq ; by intuition.
    apply Rgt_not_eq.
    elim: j Hj => {IH} /= [ | j IH] Hj.
    by apply Hlt.
    apply Rlt_trans with (nth 0 (x1 :: s) j).
    apply IH ; by intuition.
    apply (sorted_nth Rlt (x1::s)).
    by apply Hlt.
    by intuition.
    apply SSR_leq ; by intuition.
    replace (Riemann_sum f (SF_seq_f2 g (x1 :: s)))
      with (minus (Riemann_sum f (SF_seq_f2 g0 (x0::x1::s))) (scal (x1 - x0) (f x0))).
    apply Rle_trans with (norm (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s]))
     + norm (opp (scal (x1 - x0) (f x0)))).
    by generalize (norm_triangle (Riemann_sum f (SF_seq_f2 g0 [:: x0, x1 & s]))
      (opp (scal (x1 - x0) (f x0)))).
    rewrite norm_opp.
    apply Rplus_le_compat_r, (Hex _ Hg0).
    rewrite /minus plus_comm SF_cons_f2 /=.
    rewrite Riemann_sum_cons /= plus_assoc.
    replace (Riemann_sum f (SF_seq_f2 g0 (x1 :: s))) with
      (Riemann_sum f (SF_seq_f2 g (x1 :: s))).
    replace (g0 x0 x1) with x0.
    by rewrite plus_opp_l plus_zero_l.
    rewrite /g0 ; case: Req_EM_T (refl_equal x0) => //.
    elim: s x1 Hlt {IH Hex Hg Hg0 Hi} => [ | x2 s IH] x1 Hlt.
    reflexivity.
    rewrite !(SF_cons_f2 _ x1) /=.
    rewrite !Riemann_sum_cons /=.
    apply f_equal2.
    rewrite /g0 ; by case: Req_EM_T (Rgt_not_eq _ _ (proj1 Hlt)).
    apply IH.
    split.
    apply Rlt_trans with x1 ; by apply Hlt.
    by apply Hlt.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_O_Sn.
    exact: lt_S_n.
  move:H => {Hex} Hex.
  replace b with (last 0 (unif_part a b n)).
  pattern a at 1 ; replace a with (head 0 (unif_part a b n)).
  elim: (unif_part a b n) Hex => /= [ | x0].
  exists (norm (f 0)) => t Ht ;
  rewrite (Rle_antisym t 0) ; by intuition.
  case => /= [ | x1 s] IH Hex.
  exists (norm (f x0)) => t Ht ;
  rewrite (Rle_antisym t x0) ; by intuition.
  case: (Hex _ (lt_n_S _ _ (lt_O_Sn _))) => /= M0 H0.
  case: IH => [ | M IH].
  move => i Hi ; case: (Hex _ (lt_n_S _ _ Hi)) => {Hex} /= M Hex.
  by exists M.
  exists (Rmax M0 M) => t Ht ;
  case: (Rlt_le_dec t x1) => Ht0.
  apply Rle_trans with (2 := RmaxLess1 _ _) ;
  apply H0 ; by intuition.
  apply Rle_trans with (2 := RmaxLess2 _ _) ;
  apply IH ; by intuition.
  apply head_unif_part.
  apply last_unif_part.
Qed.

(** Extensionality *)

Lemma is_RInt_ext :
  forall (f g : R -> V) (a b : R) (l : V),
  (forall x, Rmin a b < x < Rmax a b -> f x = g x) ->
  is_RInt f a b l -> is_RInt g a b l.
Proof.
  intros f g a b.
  wlog: a b / (a < b) => [Hw | Hab] l Heq Hf.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite -Hab in Hf |- *.
    move: Hf ; apply filterlim_ext => x.
    by rewrite Rminus_eq_0 sign_0 !scal_zero_l.
    rewrite -(opp_opp l).
    apply is_RInt_swap.
    apply Hw.
    by [].
    by rewrite Rmin_comm Rmax_comm.
    by apply is_RInt_swap.
    move: Heq ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Heq.
  apply filterlim_locally_ball_norm => eps.
  destruct (proj1 (filterlim_locally_ball_norm _ _) Hf (pos_div_2 eps)) as [d Hd].
  set dx := fun x => pos_div_2 (pos_div_2 eps) / Rmax 1 (norm (minus (g x) (f x))).
  assert (forall x, 0 < dx x).
    intros x.
    apply Rdiv_lt_0_compat.
    apply is_pos_div_2.
    eapply Rlt_le_trans, Rmax_l.
    by apply Rlt_0_1.
  assert (Hdelta : 0 < Rmin d (Rmin (dx a) (dx b))).
    repeat apply Rmin_case => //.
    by apply d.
  exists (mkposreal _ Hdelta) => /= y Hstep [Hptd [Hya Hyb]].
  rewrite (double_var eps).
  eapply ball_norm_triangle.
  apply Hd.
  eapply Rlt_le_trans, Rmin_l.
  by apply Hstep.
  split => //.

  have: (seq_step (SF_lx y) < (Rmin (dx a) (dx b))) => [ | {Hstep} Hstep].
    eapply Rlt_le_trans, Rmin_r.
    by apply Hstep.
  clear d Hd Hdelta Hf.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite !scal_one.
  move: Hya Hyb ;
  rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Hya Hyb.
  move: Hab Heq Hstep ;
  rewrite -Hyb => {b Hyb} ;
  set b := last (SF_h y) (unzip1 (SF_t y)) ;
  rewrite -Hya => {a Hya} ;
  set a := SF_h y => Hab Heq Hstep.
(* *)
  revert a b Hab Heq Hptd Hstep ;
  apply SF_cons_ind with (s := y)
  => {y} [x0 | x0 y IH] a b Hab Heq Hptd Hstep.
  rewrite !Riemann_sum_zero //.
  by apply (ball_norm_center _ (pos_div_2 eps)).
  rewrite !Riemann_sum_cons.
  assert (Hx0 := proj1 (ptd_sort _ Hptd)).
  case: Hx0 => /= Hx0.
Focus 2. (* fst x0 = SF_h y *)
  rewrite Hx0 Rminus_eq_0 !scal_zero_l !plus_zero_l.
  apply: IH.
  move: Hab ; unfold a, b ; simpl ; by rewrite Hx0.
  intros x Hx.
  apply Heq ; split.
  unfold a ; simpl ; rewrite Hx0 ; apply Hx.
  unfold b ; simpl ; apply Hx.
  eapply ptd_cons, Hptd.
  move: Hstep ; unfold a, b ; simpl ; rewrite Hx0.
  apply Rle_lt_trans, Rmax_r.
(* fst x0 < SF_h y *)
  clear IH.
  rewrite (double_var (eps / 2)).
  eapply Rle_lt_trans, Rplus_lt_compat.
  eapply Rle_trans, norm_triangle.
  apply Req_le, f_equal.
  replace (@minus V _ _)
    with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0))))
               (minus (Riemann_sum g y) (Riemann_sum f y))).
  by [].
  rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
  apply f_equal.
  rewrite !plus_assoc ; apply f_equal2 => //.
  by apply plus_comm.
  eapply Rle_lt_trans.
  apply @norm_scal.
  assert (Ha := proj1 (Hptd O (lt_O_Sn _))).
  case: Ha => /= Ha.
  assert (Hb : snd x0 <= b).
    eapply Rle_trans, sorted_last.
    2: apply ptd_sort.
    2: eapply ptd_cons, Hptd.
    2: apply lt_O_Sn.
    simpl.
    apply (Hptd O), lt_O_Sn.
  case: Hb => //= Hb.
  rewrite Heq.
  rewrite minus_eq_zero norm_zero Rmult_0_r.
  apply (is_pos_div_2 (pos_div_2 eps)).
  by split.
  rewrite Hb.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_l, (Rmax_r 1).
  by apply abs_ge_0.
  apply Rlt_div_r.
  eapply Rlt_le_trans, Rmax_l.
  by apply Rlt_0_1.
  rewrite -/(dx b).
  eapply Rlt_le_trans, Rmin_r.
  eapply Rle_lt_trans, Hstep.
  by apply Rmax_l.
  rewrite -Ha.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_l, (Rmax_r 1).
  by apply abs_ge_0.
  apply Rlt_div_r.
  eapply Rlt_le_trans, Rmax_l.
  by apply Rlt_0_1.
  rewrite -/(dx a).
  eapply Rlt_le_trans, Rmin_l.
  eapply Rle_lt_trans, Hstep.
  by apply Rmax_l.

  have: (forall x : R, SF_h y <= x < b -> f x = g x) => [ | {Heq} Heq].
    intros.
    apply Heq ; split.
    by eapply Rlt_le_trans, H0.
    by apply H0.
  have: (seq_step (SF_lx y) < (dx b)) => [ | {Hstep} Hstep].
    eapply Rlt_le_trans, Rmin_r.
    eapply Rle_lt_trans, Hstep.
    apply Rmax_r.
  simpl in b.
  apply ptd_cons in Hptd.
  clear a Hab x0 Hx0.
  revert b Heq Hptd Hstep ;
  apply SF_cons_ind with (s := y)
  => {y} [x0 | x0 y IH] b Heq Hptd Hstep.
  rewrite !Riemann_sum_zero // minus_eq_zero norm_zero.
  apply (is_pos_div_2 (pos_div_2 _)).

  rewrite !Riemann_sum_cons.
  replace (minus (plus (scal (SF_h y - fst x0) (g (snd x0))) (Riemann_sum g y))
    (plus (scal (SF_h y - fst x0) (f (snd x0))) (Riemann_sum f y)))
    with (plus (scal (SF_h y - fst x0) (minus (g (snd x0)) (f (snd x0))))
               (minus (Riemann_sum g y) (Riemann_sum f y))).
  eapply Rle_lt_trans.
  apply @norm_triangle.
  assert (SF_h y <= b).
    eapply Rle_trans, sorted_last.
    2: apply ptd_sort ; eapply ptd_cons, Hptd.
    2: apply lt_O_Sn.
    simpl ; by apply Rle_refl.
  case: H0 => Hb.
  rewrite Heq.
  rewrite minus_eq_zero scal_zero_r norm_zero Rplus_0_l.
  apply IH ; intros.
  apply Heq ; split.
  eapply Rle_trans, H0.
  eapply Rle_trans ; by apply (Hptd O (lt_O_Sn _)).
  by apply H0.
  eapply ptd_cons, Hptd.
  eapply Rle_lt_trans, Hstep.
  by apply Rmax_r.
  split.
  apply (Hptd O (lt_O_Sn _)).
  eapply Rle_lt_trans, Hb.
  apply (Hptd O (lt_O_Sn _)).
  clear IH.
  rewrite Hb !Riemann_sum_zero //.
  rewrite minus_eq_zero norm_zero Rplus_0_r.
  eapply Rle_lt_trans.
  apply @norm_scal.
  assert (snd x0 <= b).
    rewrite -Hb.
    apply (Hptd O (lt_O_Sn _)).
  case: H0 => Hb'.
  rewrite Heq.
  rewrite minus_eq_zero norm_zero Rmult_0_r.
  apply (is_pos_div_2 (pos_div_2 _)).
  split.
  apply (Hptd O (lt_O_Sn _)).
  by [].
  rewrite Hb'.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_l.
  apply abs_ge_0.
  apply (Rmax_r 1).
  apply Rlt_div_r.
  eapply Rlt_le_trans, Rmax_l.
  by apply Rlt_0_1.
  eapply Rle_lt_trans, Hstep.
  rewrite -Hb.
  by apply Rmax_l.
  apply ptd_sort ; eapply ptd_cons, Hptd.
  apply ptd_sort ; eapply ptd_cons, Hptd.
  rewrite /minus opp_plus scal_distr_l -scal_opp_r -!plus_assoc.
  apply f_equal.
  rewrite !plus_assoc.
  apply f_equal2 => //.
  by apply plus_comm.
Qed.

Lemma ex_RInt_ext :
  forall (f g : R -> V) (a b : R),
  (forall x, Rmin a b < x < Rmax a b -> f x = g x) ->
  ex_RInt f a b -> ex_RInt g a b.
Proof.
intros f g a b Heq [If Hex].
exists If.
revert Hex.
now apply is_RInt_ext.
Qed.

(** ** Constant functions *)

Lemma is_RInt_const :
  forall (a b : R) (v : V),
  is_RInt (fun _ => v) a b (scal (b - a) v).
Proof.
intros a b v.
apply filterlim_within_ext with (fun _ => scal (b - a) v).
2: apply filterlim_const.
intros ptd [_ [Hhead Hlast]].
rewrite Riemann_sum_const.
rewrite Hlast Hhead.
rewrite scal_assoc.
apply (f_equal (fun x => scal x v)).
apply sym_eq, sign_min_max.
Qed.

Lemma ex_RInt_const :
  forall (a b : R) (v : V),
  ex_RInt (fun _ => v) a b.
Proof.
intros a b v.
exists (scal (b - a) v).
apply is_RInt_const.
Qed.

(** ** Composition *)

Lemma is_RInt_comp_opp :
  forall (f : R -> V) (a b : R) (l : V),
  is_RInt f (-a) (-b) l ->
  is_RInt (fun y => opp (f (- y))) a b l.
Proof.
intros f a b l Hf.
apply filterlim_locally => eps.
generalize (proj1 (filterlim_locally _ _) Hf eps) ; clear Hf ; intros [delta Hf].
exists delta.
intros ptd Hstep [Hptd [Hh Hl]].
rewrite Riemann_sum_opp.
rewrite scal_opp_r -scal_opp_l /opp /= -sign_opp.
rewrite Ropp_plus_distr.
  set ptd' := (mkSF_seq (-SF_h ptd)
    (seq.map (fun X => (- fst X,- snd X)) (SF_t ptd))).
replace (Riemann_sum (fun x => f (-x)) ptd) with (Riemann_sum f (SF_rev ptd')).
  have H : SF_size ptd = SF_size ptd'.
    rewrite /SF_size /=.
    by rewrite size_map.
  apply Hf.
  clear H ;
  revert ptd' Hstep ;
  apply SF_cons_dec with (s := ptd) => [ x0  s' Hs'| h0 s] ;
  rewrite /seq_step.
  apply cond_pos.
  set s' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite SF_lx_cons.
  revert h0 s' ;
  move: {1 3}(0) ;
  apply SF_cons_ind with (s := s) => {s} [ x1 | h1 s IH] x0 h0 s' Hs' ;
  simpl in Hs'.
  rewrite /= -Ropp_minus_distr' /Rminus -Ropp_plus_distr Ropp_involutive.
  by apply Hs'.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h1,-snd h1) s'').
  rewrite SF_lx_rcons.
  rewrite behead_rcons ; [ | rewrite SF_size_lx ; by apply lt_O_Sn ].
  rewrite head_rcons.
  rewrite pairmap_rcons.
  rewrite foldr_rcons.
  apply: IH => /=.
  replace (Rmax (Rabs (SF_h s - fst h1))
  (foldr Rmax (Rmax (Rabs (- fst h0 - - fst h1)) x0)
     (pairmap (fun x y : R => Rabs (y - x)) (SF_h s) (unzip1 (SF_t s)))))
    with (Rmax (Rabs (fst h1 - fst h0))
        (Rmax (Rabs (SF_h s - fst h1))
           (foldr Rmax x0
              (pairmap (fun x y : R => Rabs (y - x)) (SF_h s)
                 (unzip1 (SF_t s)))))).
  by [].
  rewrite Rmax_assoc (Rmax_comm (Rabs _)) -Rmax_assoc.
  apply f_equal.
  rewrite -(Ropp_minus_distr' (-fst h0)) /Rminus -Ropp_plus_distr Ropp_involutive.
  elim: (pairmap (fun x y : R => Rabs (y + - x)) (SF_h s) (unzip1 (SF_t s)))
    x0 {Hs'} (Rabs (fst h1 + - fst h0)) => [ | x2 t IH] x0 x1 /=.
    by [].
    rewrite Rmax_assoc (Rmax_comm x1) -Rmax_assoc.
    apply f_equal.
    by apply IH.
  split.
  revert ptd' Hptd H ;
  apply SF_cons_ind with (s := ptd) => [ x0 | h0 s IH] s' Hs' H i Hi ;
  rewrite SF_size_rev -H in Hi.
  by apply lt_n_O in Hi.
  rewrite SF_size_cons in Hi.
  apply lt_n_Sm_le in Hi.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_rev_cons (-fst h0,-snd h0) s'').
  rewrite SF_size_cons (SF_size_cons (-fst h0,-snd h0) s'') in H.
  apply eq_add_S in H.
  rewrite SF_lx_rcons SF_ly_rcons.
  rewrite ?nth_rcons.
  rewrite ?SF_size_lx ?SF_size_ly ?SF_size_rev -H.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S i) (S (SF_size s))) => // _.
  apply le_lt_eq_dec in Hi ; case: Hi => [Hi | -> {i}].
  apply lt_le_S in Hi.
  move: (proj2 (SSR_leq _ _) Hi) ;
  case: (ssrnat.leq (S i) (SF_size s)) => // _.
  move: (proj2 (SSR_leq _ _) (le_n_S _ _ Hi)) ;
  case: (ssrnat.leq (S (S i)) (S (SF_size s))) => // _.
  apply IH.
  move: Hs' ; apply ptd_cons.
  apply H.
  rewrite SF_size_rev -H.
  intuition.
  have : ~ is_true (ssrnat.leq (S (SF_size s)) (SF_size s)).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt.
  case: (ssrnat.leq (S (SF_size s)) (SF_size s)) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (SF_size s)) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (SF_size s) (SF_size s)) => // _.
  have : ~ is_true (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))).
    have H0 := lt_n_Sn (SF_size s).
    contradict H0.
    apply SSR_leq in H0.
    by apply le_not_lt, le_S_n.
  case: (ssrnat.leq (S (S (SF_size s))) (S (SF_size s))) => // _.
  move: (@eqtype.eq_refl ssrnat.nat_eqType (S (SF_size s))) ;
  case: (@eqtype.eq_op ssrnat.nat_eqType (S (SF_size s)) (S (SF_size s))) => // _.
  rewrite H SF_lx_rev nth_rev SF_size_lx //=.
  replace (ssrnat.subn (S (SF_size s'')) (S (SF_size s'')))
    with 0%nat by intuition.
  simpl.
  split ; apply Ropp_le_contravar ; apply (Hs' 0%nat) ;
  rewrite SF_size_cons ; by apply lt_O_Sn.
  split.
  rewrite Rmin_opp_Rmax -Hl.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_ind with (s := ptd) => [ h0 | h0 s IH] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  by apply IH.
  rewrite Rmax_opp_Rmin -Hh.
  simpl.
  clear H.
  revert ptd' ;
  move: (0) ;
  apply SF_cons_dec with (s := ptd) => [ h0 | h0 s] x0 s'.
  by simpl.
  set s'' := {| SF_h := - SF_h s; SF_t := [seq (- fst X, - snd X) | X <- SF_t s] |}.
  rewrite (SF_lx_cons (-fst h0,-snd h0) s'') rev_cons /=.
  rewrite head_rcons.
  rewrite behead_rcons ; [ | rewrite size_rev SF_size_lx ; by apply lt_O_Sn].
  rewrite unzip1_zip.
  by rewrite last_rcons.
  rewrite size_rcons size_behead ?size_rev SF_size_ly SF_size_lx //=.
  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | h ptd' IH].
  easy.
  rewrite Riemann_sum_cons.
  rewrite (SF_rev_cons (-fst h, -snd h)
    (mkSF_seq (- SF_h ptd') (seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd')))).
  rewrite -IH => {IH}.
  set s := {|
        SF_h := - SF_h ptd';
        SF_t := seq.map (fun X : R * R => (- fst X, - snd X)) (SF_t ptd') |}.
  rewrite Riemann_sum_rcons.
  rewrite SF_lx_rev.
  have H : (forall s x0, last x0 (rev s) = head x0 s).
    move => T s0 x0.
    case: s0 => [ | x1 s0] //=.
    rewrite rev_cons.
    by rewrite last_rcons.
  rewrite H /=.
  rewrite plus_comm.
  apply: (f_equal (fun x => plus (scal x _) _)).
  simpl ; ring.
Qed.

Lemma ex_RInt_comp_opp :
  forall (f : R -> V) (a b : R),
  ex_RInt f (-a) (-b) ->
  ex_RInt (fun y => opp (f (- y))) a b.
Proof.
  intros f a b [l If].
  exists l.
  by apply is_RInt_comp_opp.
Qed.

Lemma is_RInt_comp_lin
  (f : R -> V) (u v a b : R) (l : V) :
  is_RInt f (u * a + v) (u * b + v) l
    -> is_RInt (fun y => scal u (f (u * y + v))) a b l.
Proof.
  case: (Req_dec u 0) => [-> {u} If | ].
  evar_last.
  apply is_RInt_ext with (fun _ => zero).
  move => x _ ; apply sym_eq ; apply: scal_zero_l.
  apply is_RInt_const.
  apply filterlim_locally_unique with (2 := If).
  rewrite !Rmult_0_l Rplus_0_l.
  rewrite scal_zero_r.
  apply is_RInt_point.

  wlog: u a b / (u > 0) => [Hw | Hu _].
    case: (Rlt_le_dec 0 u) => Hu.
    by apply Hw.
    case: Hu => // Hu _ If.
    apply is_RInt_ext with (fun y => opp (scal (- u) (f ((- u) * (- y) + v)))).
    move => x _.
    rewrite -(scal_opp_l (- u) (f (- u * - x + v))) /=.
    rewrite /opp /= Ropp_involutive.
    apply f_equal.
    apply f_equal ; ring.
    apply (is_RInt_comp_opp (fun y => scal (- u) (f (- u * y + v)))).
    apply Hw.
    by apply Ropp_gt_lt_0_contravar.
    by apply Ropp_neq_0_compat, Rlt_not_eq.
    by rewrite ?Rmult_opp_opp.
  wlog: a b l / (a < b) => [Hw | Hab].
    case: (Rlt_le_dec a b) => Hab If.
    by apply Hw.
    case: Hab If => [Hab | -> {b}] If.
    rewrite -(opp_opp l).
    apply is_RInt_swap.
    apply Hw.
    by [].
    by apply is_RInt_swap.
    evar_last.
    apply is_RInt_point.
    apply filterlim_locally_unique with (2 := If).
    apply is_RInt_point.
  intros If.
  apply filterlim_locally.
  generalize (proj1 (filterlim_locally _ l) If).
  move => {If} If eps.
  case: (If eps) => {If} alpha If.
  have Ha : 0 < alpha / Rabs u.
    apply Rdiv_lt_0_compat.
    by apply alpha.
    by apply Rabs_pos_lt, Rgt_not_eq.
  exists (mkposreal _ Ha) => /= ptd Hstep [Hptd [Hfirst Hlast]].
  set ptd' := mkSF_seq (u * SF_h ptd + v) (map (fun X => (u * fst X + v,u * snd X + v)) (SF_t ptd)).
  replace (scal (sign (b - a)) (Riemann_sum (fun y : R => scal u (f (u * y + v))) ptd))
  with (scal (sign (u * b + v - (u * a + v))) (Riemann_sum f ptd')).
  apply: If.
  revert ptd' ;
  case: (ptd) Hstep => x0 s Hs /= ;
  rewrite /seq_step /= in Hs |- *.
  elim: s x0 Hs => [ | [x1 y0] s IH] /= x0 Hs.
  by apply alpha.
  apply Rmax_case.
  replace (u * x1 + v - (u * x0 + v)) with (u * (x1 - x0)) by ring.
  rewrite Rabs_mult Rmult_comm ; apply Rlt_div_r.
  by apply Rabs_pos_lt, Rgt_not_eq.
  by apply Rle_lt_trans with (2 := Hs), Rmax_l.
  apply IH.
  by apply Rle_lt_trans with (2 := Hs), Rmax_r.
  split.
  revert ptd' ;
  case: (ptd) Hptd => x0 s Hs /= i Hi ;
  rewrite /SF_size size_map /= in Hi ;
  move: (Hs i) => {Hs} Hs ;
  rewrite /SF_size /= in Hs ;
  move: (Hs Hi) => {Hs} ;
  rewrite /SF_lx /SF_ly /= => Hs.
  elim: s i x0 Hi Hs => /= [ | [x1 y0] s IH] i x0 Hi Hs.
  by apply lt_n_O in Hi.
  case: i Hi Hs => /= [ | i] Hi Hs.
  split ; apply Rplus_le_compat_r ;
  apply Rmult_le_compat_l ;
  try by apply Rlt_le.
  by apply Hs.
  by apply Hs.
  apply IH.
  by apply lt_S_n.
  by apply Hs.
  split.
  rewrite /ptd' /= Hfirst.
  rewrite -Rplus_min_distr_r.
  rewrite -Rmult_min_distr_l.
  reflexivity.
  by apply Rlt_le.
  rewrite -Rplus_max_distr_r.
  rewrite -Rmult_max_distr_l.
  rewrite -Hlast.
  rewrite /ptd' /=.
  elim: (SF_t ptd) (SF_h ptd) => [ | [x1 _] /= s IH] x0 //=.
  by apply Rlt_le.
  apply f_equal2.
  replace (u * b + v - (u * a + v)) with (u * (b - a)) by ring.
  rewrite sign_mult.
  rewrite (sign_eq_1 _ Hu).
  apply Rmult_1_l.

  revert ptd' ;
  apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH] //=.
  set s' := {|
      SF_h := u * SF_h s + v;
      SF_t := [seq (u * fst X + v, u * snd X + v)
                 | X <- SF_t s] |}.
  rewrite Riemann_sum_cons (Riemann_sum_cons _ (u * x0 + v,u * y0 + v) s') /=.
  rewrite IH.
  apply f_equal2 => //=.
  rewrite scal_assoc /=.
  apply (f_equal (fun x => scal x _)).
  rewrite /mult /= ; ring.
Qed.

Lemma ex_RInt_comp_lin (f : R -> V) (u v a b : R) :
  ex_RInt f (u * a + v) (u * b + v)
    -> ex_RInt (fun y => scal u (f (u * y + v))) a b.
Proof.
  case => l Hf.
  exists l.
  by apply is_RInt_comp_lin.
Qed.

(** ** Chasles *)

Lemma is_RInt_Chasles_0 (f : R -> V) (a b c : R) (l1 l2 : V) :
  a < b < c -> is_RInt f a b l1 -> is_RInt f b c l2
  -> is_RInt f a c (plus l1 l2).
Proof.
  intros [Hab Hbc] H1 H2.
  case: (ex_RInt_ub f a b).
  by exists l1.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ M1 HM1.
  case: (ex_RInt_ub f b c).
  by exists l2.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ M2 HM2.

  apply filterlim_locally_ball_norm => eps.
  generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 (pos_div_2 eps))) => {H1} H1.
  generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 (pos_div_2 eps))) => {H2} H2.
  case: H1 => d1 H1.
  case: H2 => d2 H2.
  move: H1 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ H1.
  move: H2 ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hbc) => //= _ _ H2.

  have Hd3 : 0 < eps / (4 * ((M1 + 1) + (M2 + 1))).
    apply Rdiv_lt_0_compat.
    by apply eps.
    repeat apply Rmult_lt_0_compat.
    by apply Rlt_0_2.
    by apply Rlt_0_2.
    apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
    specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
    apply Rle_trans with (2 := HM1), norm_ge_0.
    specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
    apply Rle_trans with (2 := HM2), norm_ge_0.
  have Hd : 0 < Rmin (Rmin d1 d2) (mkposreal _ Hd3).
    repeat apply Rmin_case.
    by apply d1.
    by apply d2.
    by apply Hd3.
  exists (mkposreal _ Hd) => /= ptd Hstep [Hptd [Hh Hl]].
  move: Hh Hl ; rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => //= _ _ Hh Hl.
  rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
  rewrite scal_one.
  rewrite /ball_norm (double_var eps).
  apply Rle_lt_trans
    with (norm (minus (Riemann_sum f ptd)
      (plus (Riemann_sum f (SF_cut_down ptd b))
            (Riemann_sum f (SF_cut_up ptd b))))
      + norm (minus (plus (Riemann_sum f (SF_cut_down ptd b))
                          (Riemann_sum f (SF_cut_up ptd b)))
                    (plus l1 l2))).
  set v:= minus _ (plus l1 l2).
  replace v
    with (plus (minus (Riemann_sum f ptd)
     (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b))))
  (minus
     (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))).
  exact: norm_triangle.
  rewrite /v /minus -plus_assoc.
  apply f_equal.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
  apply Rplus_lt_compat.
  apply Rlt_le_trans with (2 := Rmin_r _ _) in Hstep.
  generalize (fun H H0 => Riemann_sum_Chasles_0 f (M1 + 1 + (M2 + 1)) b ptd (mkposreal _ Hd3) H H0 Hptd Hstep).
  rewrite /= Hl Hh => H.
  replace (eps / 2) with (2 * (mkposreal _ Hd3) * (M1 + 1 + (M2 + 1))).
  rewrite -norm_opp opp_plus opp_opp plus_comm.
  simpl ; apply H.
  intros x Hx.
  case: (Rle_lt_dec x b) => Hxb.
  apply Rlt_trans with (M1 + 1).
  apply Rle_lt_trans with M1.
  apply HM1 ; split.
  by apply Hx.
  by apply Hxb.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  apply Rminus_lt_0 ; ring_simplify.
  apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
  specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
  apply Rle_trans with (2 := HM2), norm_ge_0.
  apply Rlt_trans with (M2 + 1).
  apply Rle_lt_trans with M2.
  apply HM2 ; split.
  by apply Rlt_le, Hxb.
  by apply Hx.
  apply Rminus_lt_0 ; ring_simplify ; by apply Rlt_0_1.
  apply Rminus_lt_0 ; ring_simplify.
  apply Rplus_le_lt_0_compat with (2 := Rlt_0_1).
  specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
  apply Rle_trans with (2 := HM1), norm_ge_0.
  split ; by apply Rlt_le.
  simpl ; field.
  apply Rgt_not_eq.
  apply Rplus_lt_0_compat ; apply Rplus_le_lt_0_compat, Rlt_0_1.
  specialize (HM1 _ (conj (Rle_refl _) (Rlt_le _ _ Hab))).
  apply Rle_trans with (2 := HM1), norm_ge_0.
  specialize (HM2 _ (conj (Rle_refl _) (Rlt_le _ _ Hbc))).
  apply Rle_trans with (2 := HM2), norm_ge_0.
  apply Rlt_le_trans with (2 := Rmin_l _ _) in Hstep.
  specialize (H1 (SF_cut_down ptd b)).
  specialize (H2 (SF_cut_up ptd b)).
  apply Rle_lt_trans
    with (norm (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1)
         + norm (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
  replace (minus (plus (Riemann_sum f (SF_cut_down ptd b))
        (Riemann_sum f (SF_cut_up ptd b))) (plus l1 l2))
    with (plus (minus (scal (sign (b - a)) (Riemann_sum f (SF_cut_down ptd b))) l1)
           (minus (scal (sign (c - b)) (Riemann_sum f (SF_cut_up ptd b))) l2)).
  apply @norm_triangle.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite 2!scal_one /minus opp_plus -2!plus_assoc.
  apply f_equal.
  rewrite plus_comm -plus_assoc.
  apply f_equal.
  by apply plus_comm.
  rewrite (double_var (eps / 2)) ; apply Rplus_lt_compat.
  apply H1.
  apply SF_cut_down_step.
  rewrite /= Hl Hh ; split ; by apply Rlt_le.
  by apply Rlt_le_trans with (1 := Hstep), Rmin_l.
  split.
  apply SF_cut_down_pointed.
  rewrite Hh ; by apply Rlt_le.
  by [].
  split.
  rewrite SF_cut_down_h.
  by apply Hh.
  rewrite Hh ; by apply Rlt_le.
  move: (SF_cut_down_l ptd b) => //=.
  apply H2.
  apply SF_cut_up_step.
  rewrite /= Hl Hh ; split ; by apply Rlt_le.
  by apply Rlt_le_trans with (1 := Hstep), Rmin_r.
  split.
  apply SF_cut_up_pointed.
  rewrite Hh ; by apply Rlt_le.
  by [].
  split.
  by rewrite SF_cut_up_h.
  move: (SF_cut_up_l ptd b) => /= ->.
  by apply Hl.
  rewrite Hl ; by apply Rlt_le.
Qed.

Lemma ex_RInt_Chasles_0 (f : R -> V) (a b c : R) :
  a <= b <= c -> ex_RInt f a b -> ex_RInt f b c
  -> ex_RInt f a c.
Proof.
  case => Hab Hbc H1 H2.
  case: Hab => [ Hab | -> ] //.
  case: Hbc => [ Hbc | <- ] //.
  case: H1 => [l1 H1] ; case: H2 => [l2 H2].
  exists (plus l1 l2).
  apply is_RInt_Chasles_0 with b ; try assumption.
  by split.
Qed.

Lemma is_RInt_Chasles_1 (f : R -> V) (a b c : R) l1 l2 :
  a < b < c -> is_RInt f a c l1 -> is_RInt f b c l2 -> is_RInt f a b (minus l1 l2).
Proof.
intros [Hab Hbc] H1 H2.
apply filterlim_locally_ball_norm => eps.
generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => {H1} d1 /= H1.
generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => {H2} d2 /= H2.
exists d1 ; simpl ; intros y Hstep [Hptd [Hh Hl]].
assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\
  pointed_subdiv y /\
  SF_h y = Rmin b c /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax b c).
  apply filter_ex.
  exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
  repeat (split => //=).
  by apply H5.
  by apply H6.
case: H => y2 [Hstep2 H].
specialize (H2 y2 (Rlt_le_trans _ _ _ Hstep2 (Rmin_r _ _)) H).
case: H => Hptd2 [Hh2 Hl2].
set y1 := mkSF_seq (SF_h y) (SF_t y ++ SF_t y2).
  move: Hl Hh2 Hh Hl2 H1 H2 ; rewrite /Rmax /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) (Rlt_le _ _ Hbc) => // _ _ ; case: Rle_dec => // _ _.
  case: Rle_dec (Rlt_le _ _ (Rlt_trans _ _ _ Hab Hbc)) => // _ _.
  move => Hl Hh2 Hh Hl2 H1 H2.
  rewrite -Hl in Hab, Hbc, H2, Hh2 |-* => {b Hl}.
  rewrite -Hh in H1, Hab |- * => {a Hh}.
  rewrite -Hl2 in Hbc, H2, H1 => {c Hl2}.
assert (seq_step (SF_lx y1) < d1).
  unfold y1 ; move: Hstep Hh2.
  clear -Hstep2.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hstep Hl.
  rewrite -Hl.
  by apply Rlt_le_trans with (1 := Hstep2), Rmin_l.
  rewrite /SF_lx /seq_step /= in Hstep |- * ;
  move: (Rle_lt_trans _ _ _ (Rmax_r _ _) Hstep) (Rle_lt_trans _ _ _ (Rmax_l _ _) Hstep) => {Hstep} /= H H0.
  apply Rmax_case.
  by [].
  by apply IH.
assert (pointed_subdiv y1 /\ SF_h y1 = SF_h y /\
  last (SF_h y1) (unzip1 (SF_t y1)) = last (SF_h y2) (unzip1 (SF_t y2))).
  split.
  unfold y1 ; move: Hptd Hh2.
  clear -Hptd2.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hptd Hl.
  rewrite -Hl ; by apply Hptd2.
  case => [ | i] /= Hi.
  by apply (Hptd O (lt_O_Sn _)).
  apply (IH (ptd_cons _ _ Hptd) Hl i (lt_S_n _ _ Hi)).
  unfold y1 ; simpl ; split.
  by [].
  move: Hh2 ; clear ;
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
  by rewrite Hl.
  by apply IH.
specialize (H1 y1 H H0).
move: Hab Hbc Hh2 H1 H2 ; clear ;
set c := last (SF_h y2) (unzip1 (SF_t y2)) ;
set b := last (SF_h y) (unzip1 (SF_t y)) ;
set a := SF_h y => Hab Hbc Hl.
rewrite -> sign_eq_1 by now apply Rlt_Rminus, Rlt_trans with b.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 3!scal_one.
replace (Riemann_sum f y) with (minus (Riemann_sum f y1) (Riemann_sum f y2)).
move => H1 H2.
unfold ball_norm.
set v := minus _ _.
replace v
  with (minus (minus (Riemann_sum f y1) l1) (minus (Riemann_sum f y2) l2)).
  rewrite (double_var eps).
  apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
  rewrite -(norm_opp (minus (Riemann_sum f y2) l2)).
  by apply @norm_triangle.
  rewrite /v /minus 2!opp_plus opp_opp 2!plus_assoc.
  apply (f_equal (fun x => plus x _)).
  rewrite -!plus_assoc.
  apply f_equal.
  by apply plus_comm.
  move: Hl ; unfold y1, b.
  clear.
  apply SF_cons_ind with (s := y) => {y} [ x0 | [x0 y0] y IH ] /= Hl.
  by rewrite -Hl /minus plus_opp_r.
  rewrite (Riemann_sum_cons _ (x0,y0) {| SF_h := SF_h y; SF_t := SF_t y ++ SF_t y2 |}) /=.
  rewrite Riemann_sum_cons /=.
  rewrite /minus -plus_assoc.
  apply f_equal.
  by apply IH.
Qed.

Lemma is_RInt_Chasles_2 (f : R -> V) (a b c : R) l1 l2 :
  a < b < c -> is_RInt f a c l1 -> is_RInt f a b l2 -> is_RInt f b c (minus l1 l2).
Proof.
  intros [Hab Hbc] H1 H2.
  rewrite -(Ropp_involutive a) -(Ropp_involutive b) -(Ropp_involutive c) in H1 H2.
  apply is_RInt_comp_opp, is_RInt_swap in H1.
  apply is_RInt_comp_opp, is_RInt_swap in H2.
  apply Ropp_lt_contravar in Hab.
  apply Ropp_lt_contravar in Hbc.
  generalize (is_RInt_Chasles_1 _ _ _ _ _ _ (conj Hbc Hab) H1 H2).
  clear => H.
  apply is_RInt_comp_opp, is_RInt_swap in H.
  replace (minus l1 l2) with (opp (minus (opp l1) (opp l2))).
  move: H ; apply is_RInt_ext.
  now move => x _ ; rewrite opp_opp Ropp_involutive.
  by rewrite /minus opp_plus 2!opp_opp.
Qed.

Lemma is_RInt_Chasles (f : R -> V) (a b c : R) (l1 l2 : V) :
  is_RInt f a b l1 -> is_RInt f b c l2
  -> is_RInt f a c (plus l1 l2).
Proof.
  wlog: a c l1 l2 / (a <= c) => [Hw | Hac].
    move => H1 H2.
    case: (Rle_lt_dec a c) => Hac.
    by apply Hw.
    rewrite -(opp_opp (plus _ _)) opp_plus plus_comm.
    apply is_RInt_swap.
    apply Hw.
    by apply Rlt_le.
    by apply is_RInt_swap.
    by apply is_RInt_swap.
  case: (Req_dec a b) => [ <- {b} | Hab'] H1.
  - move => H2.
    apply filterlim_locally_ball_norm => /= eps.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    assert (pointed_subdiv (SF_nil a) /\
      SF_h (SF_nil (T := V) a) = Rmin a a /\
      last (SF_h (SF_nil (T := V) a)) (unzip1 (SF_t (SF_nil (T := V) a))) = Rmax a a).
      split.
      move => i Hi ; by apply lt_n_O in Hi.
      rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl a).
    specialize (H1 (SF_nil a) (cond_pos d1) H) => {H d1}.
    rewrite Rminus_eq_0 sign_0 in H1.
    assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
    rewrite /ball_norm H /minus plus_zero_l in H1 => {H}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    exists d2 => ptd Hstep Hptd.
    apply Rle_lt_trans with (norm (minus (scal (sign (c - a)) (Riemann_sum f ptd)) l2) + norm (opp l1)).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    rewrite /minus opp_plus -plus_assoc.
    by apply f_equal, @plus_comm.
    rewrite (double_var eps) ; apply Rplus_lt_compat.
    by apply H2.
    by apply H1.
  case: (Req_dec b c) => [ <- | Hbc'] H2.
  - apply filterlim_locally_ball_norm => /= eps.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    assert (pointed_subdiv (SF_nil b) /\
      SF_h (SF_nil (T := V) b) = Rmin b b /\
      last (SF_h (SF_nil (T := V) b)) (unzip1 (SF_t (SF_nil (T := V) b))) = Rmax b b).
      split.
      move => i Hi ; by apply lt_n_O in Hi.
      rewrite /Rmin /Rmax ; by case: Rle_dec (Rle_refl b).
    specialize (H2 (SF_nil b) (cond_pos d2) H) => {H d2}.
    rewrite Rminus_eq_0 sign_0 in H2.
    assert (H := scal_zero_l (Riemann_sum f (SF_nil a))).
    rewrite /ball_norm H /minus plus_zero_l in H2 => {H}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    exists d1 => ptd Hstep Hptd.
    apply Rle_lt_trans with (norm (minus (scal (sign (b - a)) (Riemann_sum f ptd)) l1) + norm (opp l2)).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    by rewrite /minus opp_plus -plus_assoc.
    rewrite (double_var eps) ; apply Rplus_lt_compat.
    by apply H1.
    by apply H2.
  case: (Req_dec a c) => Hac'.
  - rewrite -Hac' in H1 Hbc' H2 Hac |- * => {c Hac'}.
    apply is_RInt_swap in H2.
    apply filterlim_locally_ball_norm => /= eps.
    exists (mkposreal _ Rlt_0_1) => y Hstep Hy.
    rewrite Rminus_eq_0 sign_0.
    assert (H := scal_zero_l (Riemann_sum f y)).
    rewrite /ball_norm H /minus plus_zero_l opp_plus => {H y Hstep Hy}.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H1 (pos_div_2 eps)) ; case => /= {H1} d1 H1.
    generalize (proj1 (filterlim_locally_ball_norm _ _) H2 (pos_div_2 eps)) ; case => /= {H2} d2 H2.
    assert (exists y, seq_step (SF_lx y) < Rmin d1 d2 /\
      pointed_subdiv y /\
      SF_h y = Rmin a b /\ last (SF_h y) (unzip1 (SF_t y)) = Rmax a b).
      apply filter_ex.
      exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) ; intros y0 H3 [H4 [H5 H6]].
      repeat (split => //=).
      by apply H5.
      by apply H6.
    case: H => y [Hstep Hy].
    specialize (H1 _ (Rlt_le_trans _ _ _ Hstep (Rmin_l _ _)) Hy).
    specialize (H2 _ (Rlt_le_trans _ _ _ Hstep (Rmin_r _ _)) Hy).
    rewrite (double_var eps).
    rewrite /ball_norm -norm_opp /minus opp_plus opp_opp in H2.
    apply Rle_lt_trans with (2 := Rplus_lt_compat _ _ _ _ H1 H2).
    apply Rle_trans with (2 := norm_triangle _ _).
    apply Req_le, f_equal.
    rewrite plus_assoc /minus.
    apply (f_equal (fun x => plus x _)).
    by rewrite plus_comm plus_assoc plus_opp_l plus_zero_l.
  case: (Rle_lt_dec a b) => Hab ; try (case: Hab => //= Hab) ; clear Hab' ;
  case: (Rle_lt_dec b c) => Hbc ; try (case: Hbc => //= Hbc) ; clear Hbc' ;
  try (case: Hac => //= Hac) ; clear Hac'.
  by apply is_RInt_Chasles_0 with b.
  apply is_RInt_swap in H2.
  rewrite -(opp_opp l2).
  by apply is_RInt_Chasles_1 with b.
  apply is_RInt_swap in H1.
  rewrite -(opp_opp l1) plus_comm.
  by apply is_RInt_Chasles_2 with b.
  now contradict Hab ; apply Rle_not_lt, Rlt_le, Rlt_trans with c.
Qed.
Lemma ex_RInt_Chasles (f : R -> V) (a b c : R) :
  ex_RInt f a b -> ex_RInt f b c -> ex_RInt f a c.
Proof.
  intros [l1 H1] [l2 H2].
  exists (plus l1 l2).
  by apply is_RInt_Chasles with b.
Qed.

(** ** Operations *)

Lemma is_RInt_scal :
  forall (f : R -> V) (a b : R) (k : R) (If : V),
  is_RInt f a b If ->
  is_RInt (fun y => scal k (f y)) a b (scal k If).
Proof.
intros f a b k If Hf.
apply filterlim_ext with (fun ptd => scal k (scal (sign (b - a)) (Riemann_sum f ptd))).
intros ptd.
rewrite Riemann_sum_scal.
rewrite 2!scal_assoc.
apply (f_equal (fun x => scal x _)).
apply Rmult_comm.
apply filterlim_comp with (1 := Hf).
apply: filterlim_scal_r.
Qed.

Lemma ex_RInt_scal :
  forall (f : R -> V) (a b : R) (k : R),
  ex_RInt f a b ->
  ex_RInt (fun y => scal k (f y)) a b.
Proof.
intros f a b k [If Hf].
exists (scal k If).
now apply is_RInt_scal.
Qed.

Lemma is_RInt_opp :
  forall (f : R -> V) (a b : R) (If : V),
  is_RInt f a b If ->
  is_RInt (fun y => opp (f y)) a b (opp If).
Proof.
intros f a b If Hf.
apply filterlim_ext with (fun ptd => (scal (opp 1) (scal (sign (b - a)) (Riemann_sum f ptd)))).
intros ptd.
rewrite Riemann_sum_opp.
rewrite scal_opp_one.
apply sym_eq, scal_opp_r.
apply filterlim_comp with (1 := Hf).
rewrite -(scal_opp_one If).
apply: filterlim_scal_r.
Qed.

Lemma ex_RInt_opp :
  forall (f : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt (fun x => opp (f x)) a b.
Proof.
intros f a b [If Hf].
exists (opp If).
now apply is_RInt_opp.
Qed.

Lemma is_RInt_plus :
  forall (f g : R -> V) (a b : R) (If Ig : V),
  is_RInt f a b If ->
  is_RInt g a b Ig ->
  is_RInt (fun y => plus (f y) (g y)) a b (plus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (sign (b - a)) (Riemann_sum g ptd)))).
intros ptd.
rewrite Riemann_sum_plus.
apply sym_eq, @scal_distr_l.
apply filterlim_comp_2 with (1 := Hf) (2 := Hg).
apply: filterlim_plus.
Qed.

Lemma ex_RInt_plus :
  forall (f g : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt g a b ->
  ex_RInt (fun y => plus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (plus If Ig).
now apply is_RInt_plus.
Qed.

Lemma is_RInt_minus :
  forall (f g : R -> V) (a b : R) (If Ig : V),
  is_RInt f a b If ->
  is_RInt g a b Ig ->
  is_RInt (fun y => minus (f y) (g y)) a b (minus If Ig).
Proof.
intros f g a b If Ig Hf Hg.
apply filterlim_ext with (fun ptd => (plus (scal (sign (b - a)) (Riemann_sum f ptd)) (scal (opp 1) (scal (sign (b - a)) (Riemann_sum g ptd))))).
intros ptd.
rewrite Riemann_sum_minus.
unfold minus.
rewrite scal_opp_one.
rewrite -scal_opp_r.
apply sym_eq, @scal_distr_l.
eapply filterlim_comp_2 with (1 := Hf).
apply filterlim_comp with (1 := Hg).
eapply @filterlim_scal_r.
rewrite scal_opp_one.
apply: filterlim_plus.
Qed.

Lemma ex_RInt_minus :
  forall (f g : R -> V) (a b : R),
  ex_RInt f a b ->
  ex_RInt g a b ->
  ex_RInt (fun y => minus (f y) (g y)) a b.
Proof.
intros f g a b [If Hf] [Ig Hg].
exists (minus If Ig).
now apply is_RInt_minus.
Qed.

End is_RInt.

Lemma ex_RInt_Chasles_1 {V : CompleteNormedModule R_AbsRing}
  (f : R -> V) (a b c : R) :
  a <= b <= c -> ex_RInt f a c -> ex_RInt f a b.
Proof.
  intros [Hab Hbc] If.
  case: Hab => [Hab | <- ].
  2: by apply ex_RInt_point.

  assert (H1 := filterlim_locally_cauchy (F := (Riemann_fine a b)) (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum f ptd))).
  apply H1 ; clear H1.
  intros eps.

  set (M := @norm_factor _ V).
  assert (He : 0 < eps / M).
    apply Rdiv_lt_0_compat.
    apply cond_pos.
    apply norm_factor_gt_0.

  assert (H1 := proj2 (filterlim_locally_cauchy (F := (Riemann_fine a c)) (fun ptd : SF_seq => scal (sign (c - a)) (Riemann_sum f ptd)))).
  destruct (H1 If (mkposreal _ He)) as [P [[alpha HP] H2]] ; clear If H1 ; rename H2 into If.
  destruct (filter_ex (F := Riemann_fine b c) (fun y => seq_step (SF_lx y) < alpha
    /\ pointed_subdiv y /\
     SF_h y = Rmin b c /\ seq.last (SF_h y) (SF_lx y) = Rmax b c)) as [y' Hy'].
    by exists alpha.

  exists (fun y => P (SF_cat y y') /\ last (SF_h y) (SF_lx y) = Rmax a b) ; split.
  exists alpha ; intros.
  assert (last 0 (SF_lx y) = head 0 (SF_lx y')).
    simpl in H0, Hy' |- *.
    rewrite (proj1 (proj2 (proj2 Hy'))).
    rewrite (proj2 (proj2 H0)).
    rewrite /Rmin ; case: Rle_dec => // _.
    rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => //.
  split.
  apply HP ; intuition.
  rewrite SF_lx_cat seq_step_cat.
  by apply Rmax_case.
  by apply lt_O_Sn.
  by apply lt_O_Sn.
  by [].
  apply SF_cat_pointed => //.
  rewrite H3 /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  case: Rle_dec (Rlt_le _ _ (Rlt_le_trans _ _ _ Hab Hbc)) => //.
  rewrite SF_last_cat // H8.
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  case: Rle_dec (Rlt_le _ _ (Rlt_le_trans _ _ _ Hab Hbc)) => //.
  by apply H0.

  intros.
  specialize (If _ _ (proj1 H) (proj1 H0)).
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite -> sign_eq_1 in If by now apply Rlt_Rminus, Rlt_le_trans with b.
  apply: norm_compat1.
  eapply Rlt_le_trans.
  eapply Rle_lt_trans.
  2: apply norm_compat2 with (1 := If).
  apply Req_le, f_equal.
  rewrite !scal_one.
  case: H => _ ; case: H0 => _ ; clear ; intros.
  rewrite -b1 in b0.
  move: v u b0 y' {b1}.
  apply (SF_cons_ind (fun v => forall u : SF_seq,
    last (SF_h v) (SF_lx v) = last (SF_h u) (SF_lx u) ->
    forall y' : SF_seq,
    minus (Riemann_sum f v) (Riemann_sum f u) =
    minus (Riemann_sum f (SF_cat v y')) (Riemann_sum f (SF_cat u y')))) => [v0 | v0 v IH u Huv y].
  apply (SF_cons_ind (fun u =>
    last (SF_h (SF_nil v0)) (SF_lx (SF_nil v0)) = last (SF_h u) (SF_lx u) ->
    forall y' : SF_seq,
    minus (Riemann_sum f (SF_nil v0)) (Riemann_sum f u) =
    minus (Riemann_sum f (SF_cat (SF_nil v0) y')) (Riemann_sum f (SF_cat u y')))) => [u0 /= Huv | u0 u IH Huv y].
  apply (SF_cons_ind (fun y' : SF_seq =>
    minus (Riemann_sum f (SF_nil v0)) (Riemann_sum f (SF_nil u0)) =
    minus (Riemann_sum f (SF_cat (SF_nil v0) y'))
      (Riemann_sum f (SF_cat (SF_nil u0) y')))) => [y0 | y0 y IH].
  by [].
  simpl in Huv.
  rewrite Huv /SF_cat /=.
  rewrite (Riemann_sum_cons _ (u0,snd y0)) /=.
  rewrite /minus opp_plus (plus_comm (scal _ _)) -plus_assoc.
  now rewrite (plus_assoc (scal _ _)) !plus_opp_r plus_zero_l plus_opp_r.
  rewrite -SF_cons_cat !Riemann_sum_cons.
  rewrite /minus !opp_plus !(plus_comm (opp (scal _ _))) !plus_assoc.
  by rewrite -!/(minus _ _) -IH.
  rewrite -SF_cons_cat !Riemann_sum_cons.
  rewrite /minus -!plus_assoc.
  by rewrite -!/(minus _ _) -IH.
  fold M.
  apply Req_le ; simpl ; field.
  by apply Rgt_not_eq, norm_factor_gt_0.
Qed.

Lemma ex_RInt_Chasles_2 {V : CompleteNormedModule R_AbsRing}
  (f : R -> V) (a b c : R) :
   a <= b <= c -> ex_RInt f a c -> ex_RInt f b c.
Proof.
  intros.
  rewrite -(Ropp_involutive a) -(Ropp_involutive c)
    in H0.
  apply ex_RInt_comp_opp in H0.
  apply ex_RInt_swap in H0.
  eapply ex_RInt_Chasles_1 in H0.
  apply ex_RInt_comp_opp in H0.
  apply ex_RInt_swap in H0.
  move: H0 ; apply ex_RInt_ext => x _.
  by rewrite opp_opp Ropp_involutive.
  split ; apply Ropp_le_contravar ; apply H.
Qed.

Lemma ex_RInt_inside {V : CompleteNormedModule R_AbsRing} :
  forall (f : R -> V) (a b x e : R),
  ex_RInt f (x-e) (x+e) -> Rabs (a-x) <= e -> Rabs (b-x) <= e ->
  ex_RInt f a b.
Proof.
intros f a b x e Hf Ha Hb.
wlog: a b Ha Hb / (a <= b) => [Hw | Hab].
case (Rle_or_lt a b); intros H.
now apply Hw.
apply ex_RInt_swap.
apply Hw; try easy.
now left.
apply (ex_RInt_Chasles_1 f a b) with (x+e).
split.
exact Hab.
assert (x-e <= b <= x+e) by now apply Rabs_le_between'.
apply H.
apply ex_RInt_Chasles_2 with (x-e).
now apply Rabs_le_between'.
exact Hf.
Qed.

(** ** Exchange limit and integral *)

Lemma filterlim_RInt {U} {V : CompleteNormedModule R_AbsRing} :
  forall (f : U -> R -> V) (a b : R) F (FF : ProperFilter F)
    g h,
  (forall x, is_RInt (f x) a b (h x))
  -> (filterlim f F (locally g))
  -> exists If, filterlim h F (locally If) /\ is_RInt g a b If.
Proof.
intros f a b F FF g h Hfh Hfg.
wlog: a b h Hfh / (a <= b) => [Hw | Hab].
  case: (Rle_lt_dec a b) => Hab.
  by apply Hw.
  destruct (Hw b a (fun x => opp (h x))) as [If [Hfh' Hfg']].
  intro x.
  by apply @is_RInt_swap.
  by apply Rlt_le.
  exists (opp If) ; split.
  apply filterlim_ext with (fun x => opp (opp (h x))).
  move => x.
  by apply opp_opp.
  eapply (filterlim_comp _ _ _ (fun x => opp (h x)) opp).
  by apply Hfh'.
  now generalize (filterlim_opp If).
  by apply @is_RInt_swap.

case: Hab => Hab.

destruct (fun FF2 HF2 => filterlim_switch_dom
  F FF (locally_dist (fun ptd : SF_seq.SF_seq => SF_seq.seq_step (SF_seq.SF_lx ptd))) FF2
  (fun ptd : SF_seq.SF_seq => SF_seq.pointed_subdiv ptd /\
    SF_seq.SF_h ptd = Rmin a b /\
    seq.last (SF_seq.SF_h ptd) (SF_seq.SF_lx ptd) = Rmax a b) HF2
  (fun (x : U) ptd => scal (sign (b - a)) (Riemann_sum (f x) ptd))
  (fun ptd => scal (sign (b - a)) (Riemann_sum g ptd)) h) as [If [Hh Hg]].
by apply locally_dist_filter.
intros P [eP HP].
assert (Hn : 0 <= ((b - a) / eP)).
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0.
    apply Rlt_le, Hab.
    apply cond_pos.
  set n := (nfloor _ Hn).
  exists (SF_seq.SF_seq_f2 (fun x y => x) (SF_seq.unif_part (Rmin a b) (Rmax a b) n)).
  destruct (Riemann_fine_unif_part (fun x y => x) a b n).
  intros u v Huv.
  split.
  apply Rle_refl.
  exact Huv.
  now apply Rlt_le, Hab.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab)  => // _ _.
  split.
  apply H0.
  apply HP.
  apply Rle_lt_trans with (1 := H).
  apply Rlt_div_l.
  apply INRp1_pos.
  unfold n, nfloor.
  destruct nfloor_ex as [n' Hn'].
  simpl.
  rewrite Rmult_comm.
  apply Rlt_div_l.
  apply cond_pos.
  apply Hn'.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab)  => // _ _.
2: by apply Hfh.

set (M := @norm_factor _ V).
intros P [eps HP].
have He: 0 < (eps / (b - a)) / (2 * M).
  apply Rdiv_lt_0_compat.
  apply Rdiv_lt_0_compat.
  by apply eps.
  by rewrite -Rminus_lt_0.
  apply Rmult_lt_0_compat.
  by apply Rlt_0_2.
  apply norm_factor_gt_0.
generalize (Hfg _ (locally_ball g (mkposreal _ He))) => {Hfg Hfh}.
unfold filtermap ;
apply filter_imp => x Hx.
apply HP.
case => t [Ht [Ha Hb]] /=.
rewrite -> sign_eq_1 by exact: Rlt_Rminus.
rewrite 2!scal_one.
apply: norm_compat1.
generalize (Riemann_sum_minus (f x) g t) => <-.
refine (_ (Riemann_sum_norm (fun x0 : R => minus (f x x0) (g x0)) (fun _ => M * ((eps / (b - a)) / (2 * M))) t Ht _)).
move => H ; apply Rle_lt_trans with (1 := H).
rewrite Riemann_sum_const.
rewrite Hb Ha.
rewrite /scal /= /mult /=.
replace ((b - a) * (M * ((eps / (b - a)) / (2 * M)))) with (eps / 2).
rewrite {2}(double_var eps) -{1}(Rplus_0_l (eps / 2)).
apply Rplus_lt_compat_r.
apply Rdiv_lt_0_compat.
by apply eps.
by apply Rlt_0_2.
field.
split.
apply Rgt_not_eq.
apply Rlt_gt.
by rewrite -Rminus_lt_0.
apply Rgt_not_eq.
apply norm_factor_gt_0.
intros t0 Ht0.
apply Rlt_le.
apply (norm_compat2 _ _ (mkposreal _ He) (Hx t0)).
exists If ; split.
by apply Hh.
by apply Hg.

exists zero.
rewrite -Hab in Hfh |- * => {b Hab}.
split.
apply filterlim_ext with (fun _ => zero).
intros x.
apply filterlim_locally_unique with (2 := Hfh x).
apply is_RInt_point.
apply filterlim_const.
apply is_RInt_point.
Qed.

(** ** Continuous imply Riemann-integrable *)

Section StepFun.

Context {V : NormedModule R_AbsRing}.

Lemma is_RInt_SF (f : R -> V) (s : SF_seq) :
  SF_sorted Rle s ->
  let a := SF_h s in
  let b := last (SF_h s) (unzip1 (SF_t s)) in
  is_RInt (SF_fun (SF_map f s) zero) a b (Riemann_sum f s).
Proof.
  apply SF_cons_ind with (s := s) => {s} [ x0 | x0 s IH] Hsort a b.
  rewrite Riemann_sum_zero //.
  by apply is_RInt_point.
  - rewrite Riemann_sum_cons.
    apply is_RInt_Chasles with (SF_h s).
    move: (proj1 Hsort) ;
    unfold a ; clear IH Hsort a b ; simpl => Hab.
    eapply is_RInt_ext, is_RInt_const.
    rewrite /Rmin /Rmax ; case: Rle_dec => // _ x Hx.
    unfold SF_fun ; simpl.
    case: Rlt_dec => //= H.
    contradict H ; apply Rle_not_lt, Rlt_le, Hx.
    move: Hab Hx ;
    apply SF_cons_dec with (s := s) => {s} /= [x1 | x1 s] Hab Hx.
    case: Rle_dec (Rlt_le _ _ (proj2 Hx)) => //.
    case: Rlt_dec (proj2 Hx) => //.
  - eapply is_RInt_ext, IH.
    clear a IH.
    revert b ; simpl.
    rewrite /Rmin /Rmax ; case: Rle_dec => // Hab x Hx.
    rewrite /SF_fun /=.
    case: Rlt_dec => /= Hx0.
    contradict Hx0.
    apply Rle_not_lt.
    eapply Rle_trans, Rlt_le, Hx.
    by apply Hsort.
    move: Hab Hx Hsort ;
    apply SF_cons_dec with (s := s) => {s} [x1 | x1 s] //= Hab Hx Hsort.
    case: Hx => H H'.
    contradict H' ; by apply Rle_not_lt, Rlt_le.
    case: Rlt_dec => //= H.
    contradict H ; by apply Rle_not_lt, Rlt_le, Hx.
    contradict Hab.
    apply (sorted_last ((SF_h s) :: (unzip1 (SF_t s))) O (proj2 Hsort) (lt_O_Sn _) (SF_h s)).
    by apply Hsort.
Qed.

Lemma ex_RInt_SF (f : R -> V) (s : SF_seq) :
  SF_sorted Rle s ->
  let a := SF_h s in
  let b := last (SF_h s) (unzip1 (SF_t s)) in
  ex_RInt (SF_fun (SF_map f s) zero) a b.
Proof.
  intros.
  eexists.
  by apply is_RInt_SF.
Qed.

End StepFun.

Lemma ex_RInt_continuous {V : CompleteNormedModule R_AbsRing} (f : R -> V) (a b : R) :
  (forall z, Rmin a b <= z <= Rmax a b -> continuous f z)
  -> ex_RInt f a b.
Proof.
  wlog: f / (forall z : R, continuous f z) => [ Hw Cf | Cf _ ].
    destruct (C0_extension_le f (Rmin a b) (Rmax a b)) as [g [Cg Hg]].
    by apply Cf.
    apply ex_RInt_ext with g.
    intros x Hx ; apply Hg ; split ; apply Rlt_le ; apply Hx.
    apply Hw => // z _ ; by apply Cg.

  wlog: a b / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite Hab ; by apply ex_RInt_point.
    apply ex_RInt_swap.
    by apply Hw.

  assert (H := unifcont_normed_1d f a b (fun x Hx => Cf x)).

  set n := fun eps => proj1_sig (seq_step_unif_part_ex a b (proj1_sig (H eps))).
  set s := fun eps => (SF_seq_f2 (fun x y => ((x+y)/2)%R) (unif_part a b (n eps))).
  set (f_eps := fun eps => fun x => match (Rle_dec a x) with
    | left _ => match (Rle_dec x b) with
       | left _ => SF_fun (SF_map f (s eps)) zero x
       | right _ => f x
       end
     | right _ => f x
     end).
  set F := fun (P : posreal -> Prop) => exists eps : posreal, forall x : posreal,
    x < eps -> P x.
  set If_eps := fun eps => Riemann_sum f (s eps).

  assert (FF : ProperFilter F).
  - assert (forall P, F P <-> at_right 0 (fun x => 0 < x /\ forall Hx, P (mkposreal x Hx))).
      split ; intros [e He].
      exists e => y Hy H0 ; split => //.
      move => {H0} H0.
      apply He.
      eapply Rle_lt_trans, Hy.
      rewrite minus_zero_r.
      by apply Req_le, sym_eq, Rabs_pos_eq, Rlt_le.
      exists e ; intros [ y H0] Hy.
      apply He.
      apply Rabs_lt_between.
      rewrite minus_zero_r ; split.
      eapply Rlt_trans, H0.
      rewrite -Ropp_0 ; apply Ropp_lt_contravar, e.
      by apply Hy.
      by apply H0.
    case: (at_right_proper_filter 0) => H1 H2.
    split.
    + intros P HP.
      apply H0 in HP.
      destruct (H1 _ HP) as [x [Hx Px]].
      by exists (mkposreal x Hx).
      destruct H2 ; split.
    + by exists (mkposreal _ Rlt_0_1).
    + intros.
      apply H0.
      eapply filter_imp.
      2: apply filter_and ; apply H0.
      2: apply H2.
      2: apply H3.
      intuition ; apply H4.
    + intros.
      apply H0.
      eapply filter_imp.
      2: apply H0 ; apply H3.
      intuition.
      by apply H4.
      by apply H2, H4.
  assert (Ha : forall eps, a = (SF_h (s eps))).
    intros eps ; simpl.
    rewrite /Rdiv ; ring.
  assert (Hb : forall eps, b = (last (SF_h (s eps)) (unzip1 (SF_t (s eps))))).
    intros eps.
    rewrite -(last_unif_part 0 a b (n eps)) ; simpl.
    apply f_equal.
    elim: {2 4}(n eps) (a + 1 * (b - a) / (INR (n eps) + 1))%R (2%nat) => [ | m IH] //= x0 k.
    by rewrite -IH.
  destruct (filterlim_RInt f_eps a b F FF f If_eps) as [If HI].
  - intros eps.
    rewrite (Ha eps) (Hb eps).
    eapply is_RInt_ext.
    2: apply (is_RInt_SF f (s eps)).
    rewrite -Hb -Ha.
    rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ x [Hax Hxb].
    rewrite /f_eps.
    case: Rle_dec (Rlt_le _ _ Hax) => // _ _.
    case: Rle_dec (Rlt_le _ _ Hxb) => // _ _.
    rewrite /s /SF_sorted SF_lx_f2.
    by apply unif_part_sort, Rlt_le.
    by apply lt_O_Sn.
  - apply (filterlim_locally f_eps) => /= eps.
    rewrite /ball /= /fct_ball.
    exists eps => e He t.
    eapply ball_le.
    apply Rlt_le, He.
    apply (norm_compat1 (f t) (f_eps e t) e).
    rewrite /f_eps.
    case: Rle_dec => Hat.
    case: Rle_dec => Hta.
    rewrite SF_fun_incr.
    rewrite SF_map_lx SF_lx_f2.
    by apply unif_part_sort, Rlt_le.
    by apply lt_O_Sn.
    rewrite SF_map_lx SF_lx_f2.
    rewrite last_unif_part head_unif_part.
    by split.
    by apply lt_O_Sn.
    intros Hsort Ht.
    case: sorted_dec.
    + rewrite SF_map_lx SF_lx_f2.
      intros Hi ; set i := proj1_sig Hi.
      rewrite SF_map_ly (nth_map 0).
      apply (proj2_sig (H e)).
      by split.
      split ; eapply Rle_trans.
      2: apply ptd_f2.
      rewrite SF_lx_f2 {1}(Ha e).
      apply sorted_head.
      apply unif_part_sort.
      by apply Rlt_le.
      eapply lt_trans, (proj2_sig Hi).
      eapply lt_trans ; apply lt_n_Sn.
      by apply lt_O_Sn.
      by apply unif_part_sort, Rlt_le.
      intros x y Hxy.
      lra.
      rewrite SF_size_f2.
      move: (proj2 (proj2_sig Hi)).
      unfold i.
      case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] /= k Hk.
      by apply lt_n_O in Hk.
      apply lt_S_n.
      eapply lt_trans, Hk.
      by apply lt_n_Sn.
      apply ptd_f2.
      by apply unif_part_sort, Rlt_le.
      intros x y Hxy.
      lra.
      rewrite SF_size_f2.
      move: (proj2 (proj2_sig Hi)).
      unfold i ;
      case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] /= k Hk.
      by apply lt_n_O in Hk.
      apply lt_S_n.
      eapply lt_trans, Hk.
      by apply lt_n_Sn.
      rewrite SF_lx_f2 ; try by apply lt_O_Sn.
      rewrite {2}(Hb e).
      eapply Rle_trans, (sorted_last _ i).
      apply Req_le.
      unfold s ; simpl.
      unfold i ;
      elim: {1 3 6}(n e) (2%nat) (a + 1 * (b - a) / (INR (n e) + 1))%R (proj1_sig Hi) (proj2 (proj2_sig Hi)) => [ | m IH] // k x0 j Hj.
      simpl in Hj ;
      by apply lt_S_n, lt_S_n, lt_n_O in Hj.
      case: j Hj => [ | j] Hj //=.
      rewrite -IH //.
      apply lt_S_n.
      rewrite size_mkseq.
      by rewrite size_mkseq in Hj.
      move: (unif_part_sort a b (n e) (Rlt_le _ _ Hab)).
      unfold s.
      elim: (unif_part a b (n e)) => [ | h] //=.
      case => [ | h0 l] IH // [Hh Hl].
      move: (IH Hl) => /=.
      case: l Hl {IH} => //= ;
      split => // ; by apply Hl.
      rewrite size_mkseq in Hi, i |- *.
      apply lt_S_n.
      eapply lt_le_trans.
      eapply lt_trans, (proj2_sig Hi).
      by apply lt_n_Sn.
      rewrite /s.
      elim: (n e) (a) (b) => [ | m IH] // a' b'.
      apply le_n_S ; rewrite unif_part_S ; by apply IH.
      apply Rle_lt_trans with (norm (minus (nth 0 (unif_part a b (n e)) (S i))
      (nth 0 (unif_part a b (n e)) i))).
      change norm with Rabs.
      apply Rabs_le_between ; rewrite Rabs_pos_eq.
      change minus with Rminus ; rewrite Ropp_minus_distr'.
      rewrite /i {i}.
      destruct Hi as [i [[H1 H2] H3]].
      simpl sval.
      cut (nth 0 (unif_part a b (n e)) i <= nth 0 (SF_ly (s e)) i <= nth 0 (unif_part a b (n e)) (S i)).
        lra.
      rewrite SF_ly_f2 nth_behead (nth_pairmap 0).
      move: {-2 4}(S i) H2 => Si /= ; clear -H1 H3 ; lra.
      now apply SSR_leq, lt_le_weak.
      apply -> Rminus_le_0.
      apply (sorted_nth Rle (unif_part a b (n e))).
      by apply unif_part_sort, Rlt_le.
      move: (proj2 (proj2_sig Hi)).
      unfold i ;
      case: (size (unif_part a b (n e))) (proj1_sig Hi) => [ | m] j /= Hm.
      by apply lt_n_O in Hm.
      apply lt_S_n.
      eapply lt_trans, Hm.
      by apply lt_n_Sn.
      eapply Rle_lt_trans.
      apply nth_le_seq_step.
      eapply lt_trans, (proj2_sig Hi).
      by apply lt_n_S.
      apply (proj2_sig (seq_step_unif_part_ex a b (proj1_sig (H e)))).
      rewrite SSR_leq.
      rewrite SF_size_ly.
      apply le_S_n ; rewrite -SF_size_lx.
      rewrite SF_lx_f2.
      by apply lt_le_weak, (proj2_sig Hi).
      by apply lt_O_Sn.
      by apply lt_O_Sn.
    + intros Hi.
      move: Hsort Ht Hi.
      rewrite SF_map_lx SF_size_map SF_size_lx.
      rewrite SF_lx_f2.
      rewrite -SF_size_ly SF_ly_f2 size_behead size_pairmap size_mkseq.
      simpl (S (Peano.pred (S (S (n e)))) - 2)%nat.
      simpl (S (Peano.pred (S (S (n e)))) - 1)%nat.
      simpl (Peano.pred (S (S (n e))) - 1)%nat.
      rewrite -minus_n_O.
      intros Hsort Ht Hi.
      rewrite SF_map_ly (nth_map 0).
      apply (proj2_sig (H e)).
      by split.
      split ; eapply Rle_trans.
      2: apply ptd_f2.
      rewrite SF_lx_f2 {1}(Ha e).
      apply sorted_head.
      apply unif_part_sort.
      by apply Rlt_le.
      rewrite size_mkseq.
      eapply lt_trans ; apply lt_n_Sn.
      by apply lt_O_Sn.
      by apply unif_part_sort, Rlt_le.
      intros x y Hxy.
      lra.
      rewrite SF_size_f2.
      rewrite size_mkseq.
      by apply lt_n_Sn.
      apply ptd_f2.
      by apply unif_part_sort, Rlt_le.
      intros x y Hxy.
      lra.
      rewrite SF_size_f2.
      rewrite size_mkseq.
      by apply lt_n_Sn.
      rewrite SF_lx_f2 ; try by apply lt_O_Sn.
      rewrite {2}(Hb e).
      apply Req_le.
      rewrite (last_unzip1 _ 0).
      fold (SF_last 0 (s e)).
      rewrite SF_last_lx SF_lx_f2.
      by rewrite (last_nth 0) size_mkseq.
      apply lt_O_Sn.
      apply Rle_lt_trans with (norm (minus (nth 0 (unif_part a b (n e)) (S (n e)))
      (nth 0 (unif_part a b (n e)) (n e)))).
      change norm with Rabs.
      apply Rabs_le_between ; rewrite Rabs_pos_eq.
      change minus with Rminus ; rewrite Ropp_minus_distr'.
      cut (nth 0 (unif_part a b (n e)) (n e) <= nth 0 (SF_ly (s e)) (n e) <= nth 0 (unif_part a b (n e)) (S (n e))).
        lra.
      rewrite SF_ly_f2 nth_behead (nth_pairmap 0).
      move: {-2 4}(S (n e)) Hi => Si /= ; clear ; lra.
      rewrite size_mkseq.
      apply SSR_leq, le_refl.
      apply -> Rminus_le_0.
      apply (sorted_nth Rle (unif_part a b (n e))).
      by apply unif_part_sort, Rlt_le.
      rewrite size_mkseq ; by apply lt_n_Sn.
      eapply Rle_lt_trans.
      apply nth_le_seq_step.
      rewrite size_mkseq ; by apply lt_n_Sn.
      apply (proj2_sig (seq_step_unif_part_ex a b (proj1_sig (H e)))).
      rewrite SSR_leq.
      rewrite SF_size_ly.
      apply le_S_n ; rewrite -SF_size_lx.
      rewrite SF_lx_f2.
      rewrite size_mkseq ; by apply le_refl.
      by apply lt_O_Sn.
      by apply lt_O_Sn.
    rewrite minus_eq_zero norm_zero ; by apply e.
    rewrite minus_eq_zero norm_zero ; by apply e.
  now exists If.
Qed.

(** ** Norm *)

Section norm_RInt.

Context {V : NormedModule R_AbsRing}.

Lemma norm_RInt_le :
  forall (f : R -> V) (g : R -> R) (a b : R) (lf : V) (lg : R),
  a <= b ->
  (forall x, a <= x <= b -> norm (f x) <= g x) ->
  is_RInt f a b lf ->
  is_RInt g a b lg ->
  norm lf <= lg.
Proof.
  intros f g a b lf lg Hab H Hf Hg.
  change (Rbar_le (norm lf) lg).
  apply (filterlim_le (F := Riemann_fine a b)) with
    (fun ptd : SF_seq => norm (scal (sign (b - a)) (Riemann_sum f ptd)))
    (fun ptd : SF_seq => scal (sign (b - a)) (Riemann_sum g ptd)).
  3: apply Hg.
  exists (mkposreal _ Rlt_0_1) => ptd _ [Hptd [Hh Hl]].
  destruct Hab as [Hab|Hab].
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite !scal_one.
  apply Riemann_sum_norm.
  by [].
  move => t.
  rewrite Hl Hh /Rmin /Rmax ; case: Rle_dec => [_|].
  apply H.
  move => /Rnot_le_lt Hab'.
  elim (Rlt_not_le _ _ Hab).
  now apply Rlt_le.
  rewrite -> Rminus_diag_eq by now apply sym_eq.
  rewrite sign_0.
  rewrite 2!scal_zero_l.
  rewrite norm_zero ; by right.
  apply filterlim_comp with (locally lf).
  by apply Hf.
  by apply filterlim_norm.
Qed.

Lemma norm_RInt_le_const :
  forall (f : R -> V) (a b : R) (lf : V) (M : R),
  a <= b ->
  (forall x, a <= x <= b -> norm (f x) <= M) ->
  is_RInt f a b lf ->
  norm lf <= (b - a) * M.
Proof.
intros f a b lf M Hab H Hf.
apply norm_RInt_le with (1 := Hab) (2 := H) (3 := Hf).
apply: is_RInt_const.
Qed.

Lemma norm_RInt_le_const_abs :
  forall (f : R -> V) (a b : R) (lf : V) (M : R),
  (forall x, Rmin a b <= x <= Rmax a b -> norm (f x) <= M) ->
  is_RInt f a b lf ->
  norm lf <= Rabs (b - a) * M.
Proof.
intros f a b lf M H Hf.
unfold Rabs.
case Rcase_abs => Hab.
apply Rminus_lt in Hab.
rewrite Ropp_minus_distr.
apply is_RInt_swap in Hf.
rewrite <- norm_opp.
apply norm_RInt_le_const with (3 := Hf).
now apply Rlt_le.
intros x Hx.
apply H.
now rewrite -> Rmin_right, Rmax_left by now apply Rlt_le.
apply Rminus_ge in Hab.
apply Rge_le in Hab.
apply norm_RInt_le_const with (1 := Hab) (3 := Hf).
intros x Hx.
apply H.
now rewrite -> Rmin_left, Rmax_right.
Qed.

End norm_RInt.

(** * Specific Normed Modules *)

(** Pairs *)

Section prod.

Context {U V : NormedModule R_AbsRing}.

Lemma is_RInt_fct_extend_fst
  (f : R -> U * V) (a b : R) (l : U * V) :
  is_RInt f a b l -> is_RInt (fun t => fst (f t)) a b (fst l).
Proof.
  intros Hf P [eP HP].
  destruct (Hf (fun u : U * V => P (fst u))) as [ef Hf'].
    exists eP => y Hy.
    apply HP.
    apply Hy.
  exists ef => y H1 H2.
  replace (Riemann_sum (fun t : R => fst (f t)) y)
    with (fst (Riemann_sum f y)).
  by apply Hf'.
  clear.
  apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
  by rewrite /Riemann_sum /=.
  by rewrite ?Riemann_sum_cons /= IH.
Qed.

Lemma is_RInt_fct_extend_snd
  (f : R -> U * V) (a b : R) (l : U * V) :
  is_RInt f a b l -> is_RInt (fun t => snd (f t)) a b (snd l).
Proof.
  intros Hf P [eP HP].
  destruct (Hf (fun u : U * V => P (snd u))) as [ef Hf'].
    exists eP => y Hy.
    apply HP.
    apply Hy.
  exists ef => y H1 H2.
  replace (Riemann_sum (fun t : R => snd (f t)) y)
    with (snd (Riemann_sum f y)).
  by apply Hf'.
  clear.
  apply SF_cons_ind with (s := y) => {y} [x0 | [x1 y0] y IH].
  by rewrite /Riemann_sum /=.
  by rewrite ?Riemann_sum_cons /= IH.
Qed.

Lemma is_RInt_fct_extend_pair
  (f : R -> U * V) (a b : R) lu lv :
  is_RInt (fun t => fst (f t)) a b lu ->
  is_RInt (fun t => snd (f t)) a b lv
    -> is_RInt f a b (lu,lv).
Proof.
  move => H1 H2.
  apply filterlim_locally => eps.
  generalize (proj1 (filterlim_locally _ _) H1 eps) => {H1} ; intros [d1 H1].
  generalize (proj1 (filterlim_locally _ _) H2 eps) => {H2} ; intros [d2 H2].
  simpl in H1, H2.
  exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= ptd Hstep Hptd.
  rewrite (Riemann_sum_pair f ptd) ; simpl.
  split.
  apply H1 => //.
  by apply Rlt_le_trans with (2 := Rmin_l d1 d2).
  apply H2 => //.
  by apply Rlt_le_trans with (2 := Rmin_r d1 d2).
Qed.

Lemma ex_RInt_fct_extend_fst
  (f : R -> U * V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun t => fst (f t)) a b.
Proof.
  intros [l Hl].
  exists (fst l).
  by apply is_RInt_fct_extend_fst.
Qed.

Lemma ex_RInt_fct_extend_snd
  (f : R -> U * V) (a b : R) :
  ex_RInt f a b -> ex_RInt (fun t => snd (f t)) a b.
Proof.
  intros [l Hl].
  exists (snd l).
  by apply is_RInt_fct_extend_snd.
Qed.

Lemma ex_RInt_fct_extend_pair
  (f : R -> U * V) (a b : R) :
  ex_RInt (fun t => fst (f t)) a b ->
  ex_RInt (fun t => snd (f t)) a b
    -> ex_RInt f a b.
Proof.
  move => [l1 H1] [l2 H2].
  exists (l1,l2).
  by apply is_RInt_fct_extend_pair.
Qed.

Lemma RInt_fct_extend_pair
   (U_RInt : (R -> U) -> R -> R -> U) (V_RInt : (R -> V) -> R -> R -> V) :
  (forall f a b l, is_RInt f a b l -> U_RInt f a b = l)
  -> (forall f a b l, is_RInt f a b l -> V_RInt f a b = l)
  -> forall f a b l, is_RInt f a b l
    -> (U_RInt (fun t => fst (f t)) a b, V_RInt (fun t => snd (f t)) a b) = l.
Proof.
  intros HU HV f a b l Hf.
  apply injective_projections ; simpl.
  apply HU ; by apply is_RInt_fct_extend_fst.
  apply HV ; by apply is_RInt_fct_extend_snd.
Qed.

End prod.

(** * The total function [RInt] *)

Section RInt.

Context {V : CompleteNormedModule R_AbsRing}.

Definition RInt (f : R -> V) (a b : R) := iota (is_RInt f a b).

Lemma is_RInt_unique (f : R -> V) (a b : R) (l : V) :
  is_RInt f a b l -> RInt f a b = l.
Proof.
apply iota_filterlim_locally.
Qed.

Lemma RInt_correct (f : R -> V) (a b : R) :
  ex_RInt f a b -> is_RInt f a b (RInt f a b).
Proof.
intros [If HIf].
erewrite is_RInt_unique ; exact HIf.
Qed.

Lemma opp_RInt_swap :
  forall f a b,
  ex_RInt f a b ->
  opp (RInt f a b) = RInt f b a.
Proof.
intros f a b [If HIf].
apply sym_eq, is_RInt_unique.
apply: is_RInt_swap.
apply RInt_correct.
now exists If.
Qed.

(** Correction of RInt *)

(*
Lemma is_RInt_lim_seq (f : R -> R) (a b : R) :
  forall If : R, is_RInt f a b If -> is_lim_seq (RInt_val f a b) If.
Proof.
  wlog: a b /(a < b) => [Hw | Hab] If Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.

    Focus 2.
    cut (is_lim_seq (RInt_val f b a) (-If)).
      intros H.
      apply is_lim_seq_spec in H.
      apply is_lim_seq_spec.
      move => eps ; case: (H eps) => {H} N H ; exists N => n Hn.
      rewrite RInt_val_swap.
      rewrite /opp /=.
      replace (- RInt_val f b a n - If) with (- (RInt_val f b a n - - If)) by ring.
      rewrite Rabs_Ropp ; by apply H.
    apply Hw.
    exact: Hab.

    exact: is_RInt_swap.

    assert (forall n, RInt_val f a a n = 0).
      move => n ; by rewrite RInt_val_point.
    rewrite -Hab in Hex |- * => {Hab b}.
    replace If with 0.
    apply is_lim_seq_spec.
    move => eps ; exists O => n _.
    rewrite H.
    rewrite Rminus_0_r Rabs_R0 ; apply eps.
    suff H0 : forall eps : posreal, Rabs If < eps.
    apply Rle_antisym ; apply le_epsilon => e He ;
    set eps := mkposreal e He ; apply Rlt_le.
    rewrite -(Rminus_eq_0 If) ;
    apply Rplus_lt_compat_l, Rle_lt_trans with (Rabs If).
    exact: Rabs_maj2.
    by apply (H0 eps).
    rewrite Rplus_0_l ;
    apply Rle_lt_trans with (Rabs If).
    exact: Rle_abs.
    by apply (H0 eps).
    generalize (proj1 (filterlim_locally _ If) Hex).
    clear Hex.
    intros Hex.
    move => eps ; move: (Hex eps) => {Hex}.
    rewrite Rminus_eq_0 sign_0.
    case => alpha Halpha.
    set ptd := @SF_nil R a.
    replace If with (If - 0 * Riemann_sum f ptd) by ring.
    rewrite Rabs_minus_sym.
    apply Halpha.
    by apply alpha.
    split.
    move => i /= Hi.
    by apply lt_n_O in Hi.
    split.
    rewrite /Rmin ; by case: Rle_dec (Rle_refl a).
    rewrite /Rmax ; by case: Rle_dec (Rle_refl a).
(* * Preuve dans la cas a < b *)
  apply is_lim_seq_spec.
  move => eps.
  generalize (proj1 (filterlim_locally _ If) Hex).
  clear Hex.
  intros Hex.
  case: (Hex eps) => {Hex} alpha Hex.
(* ** Trouver N *)
  have HN : 0 <= (b-a)/alpha.
    apply Rdiv_le_0_compat.
    apply -> Rminus_le_0 ; apply Rlt_le, Hab.
    by apply alpha.
  set N := (nfloor _ HN).
  exists N => n Hn.
  rewrite -Rabs_Ropp.
  set ptd := SF_seq_f2 (fun x y => (x+y)/2) (unif_part a b n).
(* ** Appliquer Hex *)
  replace (- (RInt_val f a b n - If))
    with (If - sign (b - a) * Riemann_sum f ptd).
  rewrite Rabs_minus_sym.
  apply: Hex.
  apply Rle_lt_trans with ((b-a)/(INR n + 1)).
  suff : forall i, (S i < size (SF_lx ptd))%nat ->
    nth 0 (SF_lx ptd) (S i) - nth 0 (SF_lx ptd) i = (b-a)/(INR n + 1).
  elim: (SF_lx ptd) => /= [ | x0].
  move => _ ; apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  case => /=[ | x1 s] IH Hs.
  apply Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  replace (seq_step _) with (Rmax (Rabs (x1 - x0)) (seq_step (x1::s))) by auto.
  rewrite (Hs _ (lt_n_S _ _ (lt_O_Sn _))) Rabs_right.
  apply Rmax_lub.
  by apply Rle_refl.
  apply IH => i Hi.
  by apply (Hs _ (lt_n_S _ _ Hi)).
  apply Rle_ge, Rdiv_le_0_compat ;
  [ by apply Rlt_le, Rgt_minus | by apply INRp1_pos].
  rewrite SF_lx_f2.
  replace (head 0%R (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n) by auto.
  rewrite size_mkseq => i Hi ; rewrite !nth_mkseq ?S_INR.
  field ; apply Rgt_not_eq, INRp1_pos.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  eapply lt_O_Sn.
  apply Rle_lt_trans with ((b-a)/(INR N + 1)).
  apply Rmult_le_compat_l.
  by apply Rlt_le, Rgt_minus.
  apply Rinv_le_contravar.
  by apply INRp1_pos.
  by apply Rplus_le_compat_r, le_INR.
  apply Rlt_div_l.
  by apply INRp1_pos.
  rewrite Rmult_comm ; apply Rlt_div_l.
  by apply alpha.
  rewrite /N /nfloor ; case: nfloor_ex => N' HN' /=.
  by apply HN'.
  split.
  move => i.
  rewrite SF_size_f2 size_mkseq => Hi ; simpl in Hi.
  rewrite SF_ly_f2 SF_lx_f2.
  2: apply lt_O_Sn.
  replace (head 0 (unif_part a b n) :: behead (unif_part a b n)) with
    (unif_part a b n) by auto.
  rewrite nth_behead (nth_pairmap 0).
  replace (nth 0 (0 :: unif_part a b n) (S i)) with
    (nth 0 (unif_part a b n) i) by auto.
  have : nth 0 (unif_part a b n) i <= nth 0 (unif_part a b n) (S i).
    apply (sorted_nth Rle).
    by apply unif_part_sort, Rlt_le.
    by rewrite size_mkseq.
  move : (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i)) => x y Hxy.
  lra.
  apply SSR_leq ; rewrite size_mkseq ; by intuition.
  split.
  rewrite /Rmin /= ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  rewrite -nth_last SF_lx_f2.
  2: apply lt_O_Sn.
  rewrite size_mkseq nth_mkseq ?S_INR /=.
  rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  field ; apply Rgt_not_eq, INRp1_pos.
  by [].
  rewrite Ropp_minus_distr'.
  apply f_equal.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  rewrite Rmult_1_l.
  by [].
Qed.
*)

(** ** Usual rewritings *)

Lemma RInt_ext (f g : R -> V) (a b : R) :
  (forall x, Rmin a b < x < Rmax a b -> f x = g x) ->
  RInt f a b = RInt g a b.
Proof.
intros Hfg.
apply eq_close.
apply: close_iota ; split ; apply is_RInt_ext.
exact Hfg.
intros t Ht.
now apply sym_eq, Hfg.
Qed.

Lemma RInt_point (a : R) (f : R -> V) :
  RInt f a a = zero.
Proof.
apply is_RInt_unique.
exact: is_RInt_point.
Qed.

Lemma RInt_const (a b : R) (c : V) :
  RInt (fun _ => c) a b = scal (b - a) c.
Proof.
apply is_RInt_unique.
exact: is_RInt_const.
Qed.

(*
Lemma RInt_comp_opp (f : R -> V) (a b : R) :
  ex_RInt f (-a) (-b) ->
  RInt (fun y => f (- y)) a b = opp (RInt f (-a) (-b)).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_comp_opp.

  case: (Req_dec a b) => [<- {b} | Hab].
  by rewrite ?RInt_point.
  wlog: a b Hab / (a < b) => [Hw | {Hab} Hab].
    case: (Rle_lt_dec a b) => Hab'.
    case: Hab' => // Hab'.
    by apply Hw.
    rewrite -(RInt_swap _ b) -(RInt_swap _ (-b)).
    rewrite Hw => //.
    by apply Rlt_not_eq.
  rewrite /RInt.
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  case: Rle_dec (Rlt_not_le _ _ (Ropp_lt_contravar _ _ Hab)) => // _ _.
  rewrite -Rbar_opp_real.
  apply f_equal.
  rewrite -Lim_seq_opp.
  apply Lim_seq_ext => n.
  rewrite RInt_val_swap /RInt_val Riemann_sum_opp.
  simpl opp ; apply f_equal.
  rewrite Riemann_sum_map SF_map_f2.
  replace (unif_part (- b) (- a) n) with (map Ropp (unif_part b a n)).
Focus 2.
apply eq_from_nth with 0.
by rewrite size_map !size_mkseq.
rewrite size_map !size_mkseq => i Hi.
rewrite (nth_map 0 0).
rewrite ?(nth_mkseq 0) => //.
field ; rewrite -S_INR ; apply not_0_INR, sym_not_eq, O_S.
by rewrite size_mkseq.
elim: (unif_part b a n) => /= [ | x0 s IH].
rewrite /Riemann_sum /=.
apply opp_zero.
destruct s as [ | x1 s].
rewrite /Riemann_sum /=.
apply opp_zero.
rewrite (SF_cons_f2 _ (- x0)).
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /=.
rewrite (SF_cons_f2 _ (x0)).
2: by apply lt_O_Sn.
rewrite Riemann_sum_cons /=.
rewrite -IH /opp /plus /= Ropp_plus_distr.
apply f_equal2.
replace (- ((x0 + x1) / 2)) with ((- x0 + - x1) / 2) by field.
rewrite /scal /= /mult /=.
ring.
apply f_equal.
clear.
by [].
Qed.
*)

Lemma RInt_comp_lin (f : R -> V) (u v a b : R) :
  ex_RInt f (u * a + v) (u * b + v) ->
  RInt (fun y => scal u (f (u * y + v))) a b = RInt f (u * a + v) (u * b + v).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_comp_lin.
exact: RInt_correct.
Qed.

Lemma RInt_Chasles :
  forall f a b c,
  ex_RInt f a b -> ex_RInt f b c ->
  plus (RInt f a b) (RInt f b c) = RInt f a c.
Proof.
intros f a b c H1 H2.
apply sym_eq, is_RInt_unique.
apply: is_RInt_Chasles ;
  now apply RInt_correct.
Qed.

Lemma RInt_scal (f : R -> V) (a b l : R) :
  ex_RInt f a b ->
  RInt (fun x => scal l (f x)) a b = scal l (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_scal.
exact: RInt_correct.
Qed.

Lemma RInt_opp (f : R -> V) (a b : R) :
  ex_RInt f a b ->
  RInt (fun x => opp (f x)) a b = opp (RInt f a b).
Proof.
intros Hf.
apply is_RInt_unique.
apply: is_RInt_opp.
exact: RInt_correct.
Qed.

Lemma RInt_plus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => plus (f x) (g x)) a b = plus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
apply: is_RInt_plus ;
  now apply RInt_correct.
Qed.

Lemma RInt_minus :
  forall f g a b, ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => minus (f x) (g x)) a b = minus (RInt f a b) (RInt g a b).
Proof.
intros f g a b Hf Hg.
apply is_RInt_unique.
apply: is_RInt_minus ;
  now apply RInt_correct.
Qed.

End RInt.

(** ** Order *)

Lemma is_RInt_ge_0 (f : R -> R) (a b If : R) :
  a <= b -> is_RInt f a b If ->
  (forall x, a < x < b -> 0 <= f x) -> 0 <= If.
Proof.
intros Hab HIf Hf.
set (f' := fun x => if Rle_dec x a then 0 else if Rle_dec b x then 0 else f x).
apply is_RInt_ext with (g := f') in HIf.
apply closed_filterlim_loc with (1 := HIf) (3 := closed_ge 0).
unfold Riemann_fine, within.
apply filter_forall.
intros ptd Hptd.
replace 0 with (scal (sign (b - a)) (Riemann_sum (fun _ => 0) ptd)).
apply Rmult_le_compat_l.
apply sign_ge_0.
now apply Rge_le, Rge_minus, Rle_ge.
apply Riemann_sum_le.
apply Hptd.
intros t _.
unfold f'.
case Rle_dec as [H1|H1].
apply Rle_refl.
case Rle_dec as [H2|H2].
apply Rle_refl.
apply Hf.
now split; apply Rnot_le_lt.
rewrite Riemann_sum_const.
by rewrite !scal_zero_r.
rewrite (Rmin_left _ _ Hab) (Rmax_right _ _ Hab).
intros x Hx.
unfold f'.
case Rle_dec as [H1|H1].
now elim (Rle_not_lt _ _ H1).
case Rle_dec as [H2|H2].
now elim (Rle_not_lt _ _ H2).
easy.
Qed.

Lemma RInt_ge_0 (f : R -> R) (a b : R) :
  a <= b -> ex_RInt f a b
  -> (forall x, a < x < b -> 0 <= f x) -> 0 <= RInt f a b.
Proof.
  intros Hab Hf Hpos.
  apply: is_RInt_ge_0 Hab _ Hpos.
  exact: RInt_correct.
Qed.

Lemma is_RInt_le (f g : R -> R) (a b If Ig : R) :
  a <= b ->
  is_RInt f a b If -> is_RInt g a b Ig ->
  (forall x, a < x < b -> f x <= g x) ->
  If <= Ig.
Proof.
  intros Hab Hf Hg Hfg.
  apply Rminus_le_0.
  apply: is_RInt_ge_0 Hab _ _.
  apply: is_RInt_minus Hg Hf.
  intros x Hx.
  apply -> Rminus_le_0.
  apply Hfg, Hx.
Qed.

Lemma RInt_le (f g : R -> R) (a b : R) :
  a <= b ->
  ex_RInt f a b -> ex_RInt g a b->
  (forall x, a < x < b -> f x <= g x) ->
  RInt f a b <= RInt g a b.
Proof.
  intros Hab Hf Hg Hfg.
  apply: is_RInt_le Hab _ _ Hfg.
  exact: RInt_correct.
  exact: RInt_correct.
Qed.

Lemma RInt_gt_0 (g : R -> R) (a b : R) :
  (a < b) -> (forall x, a < x < b -> (0 < g x)) ->
  (forall x, a <= x <= b -> continuous g x) ->
  0 < RInt g a b.
Proof.
  intros Hab Hg Cg.
  set c := (a + b) / 2.
  assert (Hc : a < c < b).
    unfold c ; lra.
  assert (H : locally c (fun (x : R) => g c / 2 <= g x)).
    specialize (Hg _ Hc).
    specialize (Cg c (conj (Rlt_le _ _ (proj1 Hc)) (Rlt_le _ _ (proj2 Hc)))).
    case: (proj1 (filterlim_locally _ _) Cg (pos_div_2 (mkposreal _ Hg))) => /= d Hd.
    exists d => /= x Hx.
    specialize (Hd _ Hx).
    rewrite /ball /= /AbsRing_ball in Hd.
    apply Rabs_lt_between' in Hd.
    field_simplify (g c - g c / 2) in Hd.
    by apply Rlt_le, Hd.
  assert (Ig : ex_RInt g a b).
    apply @ex_RInt_continuous.
    rewrite Rmin_left.
    rewrite Rmax_right.
    intros.
    now apply Cg.
    by apply Rlt_le.
    by apply Rlt_le.
  case: H => /= d Hd.
  set a' := Rmax (c - d / 2) ((a + c) / 2).
  set b' := Rmin (c + d / 2) ((c + b) / 2).
  assert (Hab' : a' < b').
    apply Rlt_trans with c.
    apply Rmax_case.
    generalize (cond_pos d) ; lra.
    lra.
    apply Rmin_case.
    generalize (cond_pos d) ; lra.
    lra.
  assert (Ha' : a < a' < b).
    split.
    eapply Rlt_le_trans, Rmax_r.
    lra.
    apply Rmax_case.
    generalize (cond_pos d) ; lra.
    lra.
  assert (Hb' : a < b' < b).
    split.
    lra.
    eapply Rle_lt_trans.
    apply Rmin_r.
    lra.
  assert (ex_RInt g a a').
    eapply @ex_RInt_Chasles_1, Ig ; split ; by apply Rlt_le, Ha'.
  assert (ex_RInt g a' b).
    eapply @ex_RInt_Chasles_2, Ig ; split ; by apply Rlt_le, Ha'.
  assert (ex_RInt g a' b').
    eapply @ex_RInt_Chasles_1, H0 ; split => // ; apply Rlt_le => //.
    by apply Hb'.
  assert (ex_RInt g b' b).
    eapply @ex_RInt_Chasles_2, H0 ; split => // ; apply Rlt_le => //.
    by apply Hb'.
  rewrite -(RInt_Chasles g a a' b) //.
  apply Rplus_le_lt_0_compat.
  apply (is_RInt_ge_0 g a a').
  by apply Rlt_le, Ha'.
  exact: RInt_correct.
  intros ; apply Rlt_le, Hg ; split.
  by apply H3.
  eapply Rlt_trans, Ha'.
  apply H3.
  rewrite -(RInt_Chasles g a' b' b) //.
  apply Rplus_lt_le_0_compat.
  apply Rlt_le_trans with ((b' - a') * (g c / 2)).
  specialize (Hg _ Hc).
  apply Rmult_lt_0_compat.
  by apply -> Rminus_lt_0.
  apply Rdiv_lt_0_compat => //.
  by apply Rlt_0_2.
  eapply is_RInt_le.
  apply Rlt_le, Hab'.
  apply @is_RInt_const.
  exact: RInt_correct.
  intros ; apply Hd.
  rewrite (double_var d).
  apply Rabs_lt_between' ; split.
  eapply Rlt_trans, H3.
  eapply Rlt_le_trans, Rmax_l.
  apply Rminus_lt_0 ; ring_simplify.
  by apply is_pos_div_2.
  eapply Rlt_trans.
  apply H3.
  eapply Rle_lt_trans.
  apply Rmin_l.
  apply Rminus_lt_0 ; ring_simplify.
  by apply is_pos_div_2.
  eapply is_RInt_ge_0.
  2: exact: RInt_correct.
  apply Rlt_le, Hb'.
  intros ; apply Rlt_le, Hg.
  split.
  eapply Rlt_trans, H3.
  by apply Hb'.
  by apply H3.
Qed.

Lemma RInt_lt (f g : R -> R) (a b : R) :
  a < b ->
  (forall x : R, a <= x <= b ->continuous g x) ->
  (forall x : R, a <= x <= b ->continuous f x) ->
  (forall x : R, a < x < b -> f x < g x) ->
  RInt f a b < RInt g a b.
Proof.
  intros Hab Cg Cf Hfg.
  apply Rminus_lt_0.
  assert (Ig : ex_RInt g a b).
    apply @ex_RInt_continuous.
    rewrite Rmin_left.
    rewrite Rmax_right.
    intros.
    now apply Cg.
    by apply Rlt_le.
    by apply Rlt_le.
  assert (ex_RInt f a b).
    apply @ex_RInt_continuous.
    rewrite Rmin_left.
    rewrite Rmax_right.
    intros.
    now apply Cf.
    by apply Rlt_le.
    by apply Rlt_le.
  rewrite -[Rminus]/(@minus R_AbelianGroup) -RInt_minus //.
  apply RInt_gt_0 => //.
  now intros ; apply -> Rminus_lt_0 ; apply Hfg.
  intros.
  apply @continuous_minus.
  by apply Cg.
  by apply Cf.
Qed.

Lemma abs_RInt_le_const :
  forall (f : R -> R) a b M,
  a <= b -> ex_RInt f a b ->
  (forall t, a <= t <= b -> Rabs (f t) <= M) ->
  Rabs (RInt f a b) <= (b - a) * M.
Proof.
intros f a b M Hab If H.
apply: (norm_RInt_le_const f) => //.
exact: RInt_correct.
Qed.

(** * Equivalence with standard library *)

Lemma ex_RInt_Reals_aux_1 (f : R -> R) (a b : R) :
  forall pr : Riemann_integrable f a b,
    is_RInt f a b (RiemannInt pr).
Proof.
  wlog: a b / (a < b) => [Hw | Hab].
    case: (total_order_T a b) => [[Hab | <-] | Hab] pr.
    by apply Hw.
    rewrite RiemannInt_P9.
    apply: is_RInt_point.
    move: (RiemannInt_P1 pr) => pr'.
    rewrite (RiemannInt_P8 pr pr').
    apply: is_RInt_swap.
    apply Hw => //.
  rewrite /is_RInt.
  intros pr.
  apply filterlim_locally.
  unfold Riemann_fine.
  rewrite Rmin_left.
  2: now apply Rlt_le.
  rewrite Rmax_right.
  2: now apply Rlt_le.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.

  cut (forall (phi : StepFun a b) (eps : posreal),
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (unzip1 (SF_t ptd)) = b ->
    Rabs (RiemannInt_SF phi - 1 * Riemann_sum phi ptd) <= eps).

  intros H.
  rewrite /RiemannInt /= -/(Rminus _ _) => eps ; case: RiemannInt_exists => If HIf.
  set eps2 := pos_div_2 eps.
  set eps4 := pos_div_2 eps2.
(* RInt (f-phi) < eps/4 *)
  case: (HIf _ (cond_pos eps4)) => {HIf} N HIf.
  case: (nfloor_ex (/eps4) (Rlt_le _ _ (Rinv_0_lt_compat _ (cond_pos eps4)))) => n Hn.
  move: (HIf (N+n)%nat (le_plus_l _ _)) => {HIf}.
  rewrite /phi_sequence /R_dist ; case: pr => phi [psi pr] ;
  simpl RiemannInt_SF => HIf.
(* RInt psi < eps/4*)
  have H0 : Rabs (RiemannInt_SF psi) < eps4.
    apply Rlt_le_trans with (1 := proj2 pr).
    rewrite -(Rinv_involutive eps4 (Rgt_not_eq _ _ (cond_pos eps4))) /=.
    apply Rle_Rinv.
    apply Rinv_0_lt_compat, eps4.
    intuition.
    apply Rlt_le, Rlt_le_trans with (1 := proj2 Hn).
    apply Rplus_le_compat_r.
    apply le_INR, le_plus_r.
(* Rsum phi < eps/4 and Rsum psi < eps/4 *)
  case: (H phi eps4) => alpha0 Hphi.
  case: (H psi eps4) => {H} alpha1 Hpsi.
  have Halpha : (0 < Rmin alpha0 alpha1).
    apply Rmin_case_strong => _ ; [apply alpha0 | apply alpha1].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hstep [Hsort [Ha Hb]].
  rewrite (double_var eps) 1?(double_var (eps/2)) ?Rplus_assoc.
  rewrite /ball /= /AbsRing_ball /= /abs /=.
  rewrite Rabs_minus_sym.
  replace (_-_) with (-(RiemannInt_SF phi - If)
    + (RiemannInt_SF phi - Riemann_sum f ptd)) ;
    [ | rewrite /scal /= /mult /= ; by ring_simplify ].
  apply Rle_lt_trans with (1 := Rabs_triang _ _), Rplus_lt_le_compat.
  rewrite Rabs_Ropp ; apply HIf.
  clear HIf ;
  replace (_-_) with ((RiemannInt_SF phi - 1* Riemann_sum phi ptd)
    + (Riemann_sum phi ptd - Riemann_sum f ptd)) ;
    [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Hphi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_l.
  rewrite -Ropp_minus_distr' Rabs_Ropp.
  change Rminus with (@minus R_AbelianGroup).
  rewrite -Riemann_sum_minus.
  have H1 : (forall t : R,
    SF_h ptd <= t <= last (SF_h ptd) (SF_lx ptd) -> Rabs (f t - phi t) <= psi t).
    move => t Ht.
    apply pr ; move: (Rlt_le _ _ Hab) ; rewrite /Rmin /Rmax ;
    case: Rle_dec => // _ _ ; rewrite -Ha -Hb //.
  apply Rle_trans with (1 := Riemann_sum_norm (fun t => f t - phi t) _ _ Hsort H1).
  apply Rle_trans with (1 := Rle_abs _).
  replace (Riemann_sum psi ptd) with
    (-(RiemannInt_SF psi - 1* Riemann_sum psi ptd)
    + RiemannInt_SF psi) ; [ | by ring_simplify].
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  rewrite Rabs_Ropp ; apply Hpsi => //.
  apply Rlt_le_trans with (1 := Hstep) ; rewrite /alpha ; apply Rmin_r.
  apply Rlt_le, H0.

(* forall StepFun *)

  case => phi [lx [ly Hphi]] eps /= ;
  rewrite /RiemannInt_SF /subdivision /subdivision_val ;
  move: (Rlt_le _ _ Hab) ; case: Rle_dec => //= _ _.
  clear pr.
  move: (Rlt_le _ _ Hab) Hphi => {Hab} ;
  elim: lx ly eps a b => [ | lx0 lx IH] ly eps a b Hab.
(* lx = [::] *)
  case ; intuition ; by [].
  case: lx IH ly => [ | lx1 lx] IH ;
  case => [ {IH} | ly0 ly] Had ; try by (case: Had ; intuition ; by []).
(* lx = [:: lx0] *)
  exists eps => ptd Hptd Hstep (*Hsort*) Ha Hb /=.
  rewrite Riemann_sum_zero.
  rewrite Rmult_0_r Rminus_0_r Rabs_R0 ; apply Rlt_le, eps.
  by apply ptd_sort.
  rewrite /SF_lx /= Hb Ha ; case: Had => {Ha Hb} _ [Ha [Hb _]] ; move: Ha Hb ;
  rewrite /Rmin /Rmax ; case: Rle_dec => // _ <- <- //.
(* lx = [:: lx0, lx1 & lx] *)
  set eps2 := pos_div_2 eps ; set eps4 := pos_div_2 eps2.
(* * alpha1 from IH *)
  case: (IH ly eps4 lx1 b) => {IH}.

  replace b with (last 0 (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx)))).
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1%nat)
  with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; apply lt_n_S, lt_O_Sn.
  case: Had => /= _ [_ [Hb _]] ; move: Hb ; rewrite /Rmax ;
  case : Rle_dec => //= _ ;
  elim: (lx) lx1  => //= h s IH _ ; apply IH.
  apply (StepFun_P7 Hab Had).

  move => /= alpha1 IH.
(* * alpha2 from H *)
  cut (forall eps : posreal,
    exists alpha : posreal,
    forall ptd : SF_seq,
    pointed_subdiv ptd ->
    seq_step (SF_lx ptd) < alpha ->
    SF_h ptd = a ->
    last (SF_h ptd) (SF_lx ptd) = lx1 ->
    Rabs (ly0 * (lx1 - lx0) - Riemann_sum phi ptd) <= eps).

  intros H.
  case: (H eps4) => {H} alpha2 H.
(* * alpha3 from (fmax - fmin) *)
  set fmin1 := foldr Rmin 0 (ly0::Rlist2seq ly).
  set fmin2 := foldr Rmin 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmin := Rmin fmin1 fmin2.
  set fmax1 := foldr Rmax 0 (ly0::Rlist2seq ly).
  set fmax2 := foldr Rmax 0 (map phi (lx0::lx1::Rlist2seq lx)).
  set fmax := Rmax fmax1 fmax2.

  have Ha3 : (0 < eps4 / (Rmax (fmax - fmin) 1)).
    apply Rdiv_lt_0_compat ; [ apply eps4 | ].
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha3 := mkposreal _ Ha3.
(* * alpha = Rmin (Rmin alpha1 alpha2) alpha3 *)
  have Halpha : (0 < Rmin (Rmin alpha1 alpha2) alpha3).
    apply Rmin_case_strong => _ ; [ | apply alpha3].
    apply Rmin_case_strong => _ ; [ apply alpha1 | apply alpha2].
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd Hptd Hstep Ha Hb.

  suff Hff : forall x, a <= x <= b -> fmin <= phi x <= fmax.
  suff Hab1 : forall i, (i <= SF_size ptd)%nat -> a <= nth 0 (SF_lx ptd) i <= b.
  suff Hab0 : a <= lx1 <= b.

  rewrite (SF_Chasles _ _ lx1 (SF_h ptd)) /=.
  replace (_-_) with
    ((ly0 * (lx1 - lx0) - 1* Riemann_sum phi (SF_cut_down' ptd lx1 (SF_h ptd)))
    + (Int_SF ly (RList.cons lx1 lx) - 1* Riemann_sum phi (SF_cut_up' ptd lx1 (SF_h ptd))))
    ; [ | rewrite /plus /= ; by ring_simplify].

  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* partie [lx0;lx1] *)

  set ptd_r_last := (SF_last a (SF_cut_down' ptd lx1 a)).
  set ptd_r_belast := (SF_belast (SF_cut_down' ptd lx1 a)).
  set ptd_r := SF_rcons ptd_r_belast (lx1, (fst (SF_last a ptd_r_belast) + lx1)/2).

  move: (H ptd_r) => {H} H.

  replace (_-_) with ((ly0 * (lx1 - lx0) - Riemann_sum phi ptd_r) +
    (phi ((fst (SF_last 0 ptd_r_belast) + lx1)/2) - phi (snd ptd_r_last))
      * (lx1 - fst (SF_last 0 ptd_r_belast))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.

(* * appliquer H *)
  apply: H => {IH}.

  Focus 3.
    rewrite -Ha /ptd_r /ptd_r_belast.
    move: (proj1 Hab0) ; rewrite -Ha.
    apply SF_cons_dec with (s := ptd) => [x0 | [x0 y0] s] //= Hx0 ;
    by case: Rle_dec.
  Focus 3.
    revert ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
    rewrite -Ha ;
    apply SF_cons_ind with (s := ptd) => [x0 | [x0 y0] s IH]
    //= Hx0 ; case: Rle_dec => //= _.
    by rewrite unzip1_rcons /= last_rcons.

(* ** ptd_r est une subdivision pointée *)

  revert ptd_r_belast ptd_r Hptd ;
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH ] Hptd.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.

  case => /= [ _ | i Hi] .
  case: Rle_dec => //= Hx0 ; lra.
  contradict Hi ; apply le_not_lt.
  case: Rle_dec => //= Hx0 ; rewrite /SF_size /= ;
  apply le_n_S, le_O_n.

  move: (IH (ptd_cons _ _ Hptd)) => {IH} IH.
  case => [ _ | i Hi].
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -unzip1_fst /=.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: Rle_dec => //= Hx0.
  case: Rle_dec => //= Hx1.
  move: Hptd Hx1 ; apply SF_cons_dec with (s := s)
    => {s IH} /= [x1 | [x1 y1] s] //= Hptd Hx1.
  by apply (Hptd O (lt_O_Sn _)).
  case: Rle_dec => //= Hx2.
  by apply (Hptd O (lt_O_Sn _)).
  by apply (Hptd O (lt_O_Sn _)).
  lra.
  lra.
  move: Hi (IH i) => {IH}.
  rewrite ?SF_size_rcons -?SF_size_lx ?SF_lx_rcons ?SF_ly_rcons.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_ly /=.
  rewrite -?(last_map (@fst R R)) -?unzip1_fst.
  rewrite ?unzip2_rcons ?unzip1_rcons /=.
  rewrite ?unzip1_belast ?unzip2_belast /=.
  rewrite ?unzip1_behead ?unzip2_behead /=.
  case: (Rle_dec x0 lx1) => //= Hx0.
  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  rewrite size_belast size_belast'.
  move: Hx1 ;
  apply SF_cons_dec with (s := s) => {s Hptd} /= [ x1 | [x1 y1] s] //= Hx1.
  move => Hi IH ; apply IH ; by apply lt_S_n.
  case: Rle_dec => //= Hx2.

  move => Hi IH ; apply IH ; by apply lt_S_n.

  move => Hi IH ; apply IH ; by apply lt_S_n.

  move => Hi ; by apply lt_S_n, lt_n_O in Hi.
  move => Hi ; by apply lt_S_n, lt_n_O in Hi.

  apply Rlt_le_trans with (2 := Rmin_r alpha1 alpha2) ;
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep) => {Hstep}.
  move: Hab0 ; rewrite -Ha -Hb ;
  revert ptd_r_belast ptd_r => {Hab1} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //= Hab0.
  rewrite /SF_lx /SF_rcons /SF_belast /SF_last /SF_cut_down' /=.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) /seq_step /=.
  rewrite Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  move: Hab0 (fun Hx1 => IH (conj Hx1 (proj2 Hab0))) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hab0 IH.
  rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: Rle_dec => //= Hx1.
  rewrite /seq_step /=.
  apply Rle_max_compat_l.
  rewrite (Rle_antisym _ _ Hx1 (proj2 Hab0)) Rminus_eq_0 Rabs_R0.
  apply Rmax_case_strong ; by intuition.
  rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  apply Rplus_le_compat_r.
  by apply Rlt_le, Rnot_le_lt.
  apply Rle_ge ; rewrite -Rminus_le_0 ; by apply Hab0.
  move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /SF_rcons /SF_lx /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 lx1) => //= _ _.
  case: (Rle_dec x1 lx1) => //= Hx1 IH.
  move: (IH Hx1) => {IH}.
  case: (Rle_dec (SF_h s) lx1) => //= Hx2.
  rewrite /seq_step -?(last_map (@fst R R)) /= => IH ;
  apply Rle_max_compat_l, IH.
  rewrite /seq_step /= ; apply Rle_max_compat_l.
  rewrite /seq_step /= ; apply Rmax_le_compat.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.
  apply Rle_ge ; rewrite -Rminus_le_0 ; apply Hab0.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  apply SF_cons_ind with (s := s) => {s IH Hab0} /= [x2 | [x2 y2] s IH] //=.
  exact: Rle_refl.
  apply Rmax_case_strong => _.
  apply Rabs_pos.
  exact: IH.
(* ** transition 1 *)
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (fst (SF_last 0 ptd_r_belast) + lx1) / 2 <= b.
  suff H1 : a <= snd ptd_r_last <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_r_last Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@snd R R)) -?unzip2_snd.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  cut (a <= fst (SF_last 0 ptd_r_belast) <= b).
  lra.
  split.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  revert ptd_r_belast ptd_r Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply (Hab1 O (le_O_n _)).
  by apply Hab0.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.
  rewrite /SF_cut_down' /SF_last /= -?(last_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hab0.

  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite Rabs_right.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_r_belast ptd_r Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /SF_cut_down' /SF_belast /SF_last /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  rewrite (Rle_antisym _ _ (proj1 Hab0) (proj2 Hab0)) ; apply Req_le ; by ring.
  move => Hptd Hab0 ;
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  rewrite /SF_cut_down' /SF_belast /SF_last /=.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx3.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_r, Rlt_le, Rnot_le_lt, Hx1.

  apply Rle_ge ; rewrite -Rminus_le_0.
  revert ptd_r_belast ptd_r ; rewrite -Ha in Hab0 ; move: (proj1 Hab0) ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down' /SF_belast /SF_last /=.
  by case: Rle_dec.
  move: IH ; rewrite /SF_cut_down' /SF_belast /SF_last /=.
  case: (Rle_dec x0 _) => //= _.
  case: (Rle_dec (SF_h s) _) => //= Hx1 IH.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //=.
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] //= Hx2.
  case: (Rle_dec (SF_h s) _) => //=.

  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.

  clear H IH.
  rewrite Rplus_assoc Rmult_1_l.
  apply (f_equal (Rplus (ly0 * (lx1 - lx0)))).
  rewrite -(Ropp_involutive (-_+_)).
  apply Ropp_eq_compat.
  rewrite Ropp_plus_distr Ropp_involutive.
  revert ptd_r_last ptd_r_belast ptd_r ; move: (proj1 Hab0) ;
  rewrite -Ha => {Hab0} ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  rewrite /SF_cut_down' /=.
  case: (Rle_dec x0 lx1) => //= _.
  rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
  by ring.

  case: (Rle_dec (SF_h s) lx1) => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} [x1 | [x1 y1] s] /= Hx1.
  rewrite /SF_cut_down' /= ;
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _.
  rewrite /Riemann_sum /= => _.
  rewrite /plus /zero /scal /= /mult /=.
  ring.
  rewrite /SF_cut_down' /= ;
  case: (Rle_dec x0 _) => //= _ ;
  case: (Rle_dec x1 _) => //= _ ;
  case: (Rle_dec (SF_h s) _) => //= Hx2.
  rewrite /SF_belast /SF_last /SF_rcons /=.
  rewrite (Riemann_sum_cons phi (x0,y0) ({| SF_h := x1; SF_t := (SF_h s, y1) :: seq_cut_down' (SF_t s) lx1 y1 |})).
  rewrite (Riemann_sum_cons phi (x0,y0) ({|
  SF_h := x1;
  SF_t := rcons (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1))
               (lx1,
               (fst
                  (last (x1, y0)
                     (seq.belast (SF_h s, y1) (seq_cut_down' (SF_t s) lx1 y1))) +
                lx1) / 2) |})).
  move => <- /=.
  rewrite Rplus_assoc ;
  apply f_equal.
  rewrite -!(last_map (@fst R R)) -!unzip1_fst /=.
  ring.
  rewrite /Riemann_sum /= => _.
  rewrite /plus /zero /scal /= /mult /=.
  ring.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= _ ; case: Rle_dec => //= _.
  rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
  ring.

(* partie [lx1 ; b] *)

  set ptd_l_head := (SF_head a (SF_cut_up' ptd lx1 a)).
  set ptd_l_behead := (SF_behead (SF_cut_up' ptd lx1 a)).
  set ptd_l := SF_cons (lx1, (lx1 + fst (SF_head a ptd_l_behead))/2) ptd_l_behead.

  move: (IH ptd_l) => {IH} IH.

  replace (_-_) with ((Int_SF ly (RList.cons lx1 lx) - 1 * Riemann_sum phi ptd_l) -
    (phi ((lx1 + fst (SF_head 0 ptd_l_behead))/2) - phi (snd ptd_l_head))
      * (lx1 - fst (SF_head 0 ptd_l_behead))).
  rewrite (double_var (eps/2)) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
(* * hypothèse d'induction *)
  apply: IH.
(* ** ptd_l est une subdivision pointée *)
  case.
  move => _ ; move: (proj1 Hab0) ; rewrite -Ha => /= Hx0 ;
  case: Rle_dec => //= _.
  rewrite seq_cut_up_head'.
  move: Hx0 ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  split ; apply Req_le ; field.
  case: Rle_dec => //= Hx1.
  move: Hx1 (IH Hx1) => {IH}.
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] s] //= Hx1.
  case: Rle_dec => //= Hx2.
  lra.
  rewrite /ptd_l SF_lx_cons SF_ly_cons SF_size_cons => i Hi ;
  move: i {Hi} (lt_S_n _ _ Hi).
  revert ptd_l_behead ptd_l Hptd ;
  apply SF_cons_ind with (s := ptd)
    => /= [x0 | [x0 y0] s IH] /= Hptd.
  rewrite /SF_cut_up' /=.
  case: Rle_dec => //=.
  rewrite /SF_size /SF_behead /= => _ i Hi ; by apply lt_n_O in Hi.
  move: (IH (ptd_cons _ _ Hptd)) => {IH}.
  rewrite /SF_cut_up' /=.
  case: (Rle_dec x0 _) => //= Hx0.
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  rewrite !seq_cut_up_head'.
  move: Hx1 ; apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] //= Hx1.
  case: (Rle_dec (SF_h s) _) => //= Hx2.

(* * seq_step (SF_lx ptd_l) < alpha1 *)
  apply Rlt_le_trans with (2 := Rmin_l alpha1 alpha2).
  apply Rlt_le_trans with (2 := Rmin_l _ alpha3).
  apply Rle_lt_trans with (2 := Hstep).
  revert ptd_l_behead ptd_l ; move :(proj1 Hab0) ;
  rewrite -Ha ; apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] /= s IH] Hx0.
  rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
  rewrite /seq_step /= Rminus_eq_0 Rabs_R0 ; apply Rmax_case_strong ; by intuition.
  rewrite /SF_cut_up' /= ; case: (Rle_dec x0 _) => //= _.
  move: IH ; rewrite /SF_cut_up' /= ; case: (Rle_dec (SF_h s) _) => //= Hx1 ;
  rewrite ?seq_cut_up_head' => IH.
  move: Hx1 (IH Hx1) => {IH} ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx1 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  move: IH ; case: (Rle_dec (SF_h s) _) => //= Hx2 IH.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  apply Rle_trans with (1 := IH) => {IH} ; rewrite /seq_step /= ;
  exact: RmaxLess2.
  clear IH ; rewrite /seq_step /=.
  apply Rle_max_compat_r.
  apply Rle_trans with (2 := Rle_abs _) ; rewrite Rabs_right.
  by apply Rplus_le_compat_l, Ropp_le_contravar.
  by apply Rle_ge, (Rminus_le_0 lx1 _), Rlt_le, Rnot_le_lt.
  by rewrite /ptd_l /=.
  rewrite -Hb.
  move: (proj1 Hab0) ; rewrite -Ha /=;
  case: (Rle_dec (SF_h ptd) lx1) => //= _ _.
  rewrite seq_cut_up_head'.
  move: Hab0 ; rewrite -Ha -Hb ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= [Hx0 Hlx1].
  by apply Rle_antisym.
  move: (fun Hx1 => IH (conj Hx1 Hlx1)) => {IH} ;
  case: (Rle_dec (SF_h s) _) => //= Hx1.
  move => IH ; rewrite -(IH Hx1) => {IH}.
  move: Hx1 Hlx1 ;
  apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s ] Hx1 Hlx1.
  by [].
  case: (Rle_dec (SF_h s) _) => /= Hx2 ;
  by [].
(* ** transition 2 *)
  clear H IH.
  apply Rle_trans with ((fmax - fmin) * alpha3).
  rewrite Rabs_Ropp Rabs_mult ; apply Rmult_le_compat ; try apply Rabs_pos.
  apply Rabs_le_between.
  rewrite Ropp_minus_distr'.
  suff H0 : a <= (lx1 + fst (SF_head 0 ptd_l_behead)) / 2 <= b.
  suff H1 : a <= snd ptd_l_head <= b.
  split ; apply Rplus_le_compat, Ropp_le_contravar ;
  by apply Hff.
  revert ptd_l_head Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_up' /= ; case: Rle_dec => //= ;
  by intuition.
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s Hab0} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up' /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.
  rewrite /SF_cut_up' /SF_head /=.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; split.
  apply Rle_trans with (1 := proj1 Hx0), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (2 := proj2 Hx1), (Hptd O (lt_O_Sn _)).
  move => _ ; by intuition.

  cut (a <= fst (SF_head 0 ptd_l_behead) <= b).
  lra.
  split.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  rewrite /SF_cut_down' /= ; case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite /SF_cut_up' /SF_head /= -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite ?seq_cut_up_head'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  revert ptd_l_behead ptd_l Hab1 Hptd.
  apply SF_cons_ind with (s := ptd) => /= [ x0 | [x0 y0] s IH] // Hab1 Hptd.
  case: Rle_dec => //= Hx0.
  by apply Hab0.
  by apply (Hab1 O (le_O_n _)).
  rewrite SF_size_cons in Hab1.
  move: (IH (fun i Hi => Hab1 (S i) (le_n_S _ _ Hi)) (ptd_cons _ _ Hptd)) => {IH}.
  move: Hptd (Hab1 O (le_O_n _)) (Hab1 1%nat (le_n_S _ _ (le_0_n _))) => {Hab1}.
  apply SF_cons_dec with (s := s) => {s} /= [ x1 | [x1 y1] s] //= Hptd Hx0 Hx1.
  rewrite -?(head_map (@fst R R)) -?unzip1_fst.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  case: (Rle_dec x0 lx1) => //= Hx0'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  by rewrite !seq_cut_up_head'.
  case: (Rle_dec x1 lx1) => //= Hx1'.
  case: (Rle_dec _ lx1) => //= Hx2'.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.
  move => _ ; by apply Hx0.

  apply Rle_trans with (2 := Rmin_r (Rmin alpha1 alpha2) alpha3).
  apply Rle_trans with (2 := Rlt_le _ _ Hstep).
  rewrite -Rabs_Ropp Rabs_right ?Ropp_minus_distr'.
  rewrite -Ha -Hb in Hab0 ;
  revert ptd_l_behead ptd_l Hptd Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] //=.
  rewrite /seq_step /= => Hptd Hab0.
  move: (proj1 Hab0) ; case: Rle_dec => //= _ _.
  apply Req_le ; by ring.
  move => Hptd Hab0 ;
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (conj Hx1 (proj2 Hab0))) => {IH}.
  move: (proj1 Hab0) ; case: (Rle_dec x0 _) => //= _ _.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  move: (proj1 Hab0) Hx1 (IH Hx1) => {IH Hab0} Hx0.
  apply SF_cons_dec with (s := s) => {s Hptd} /= [x1 | [x1 y1] s] /= Hx1.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx2 IH.
  move: Hx2 IH ;
  apply SF_cons_dec with (s := s) => {s} /= [x2 | [x2 y2] s] /= Hx2.
  rewrite /seq_step /= => IH.
  apply Rle_trans with (1 := IH) ; by apply RmaxLess2.
  case: (Rle_dec (SF_h s)) => //= Hx3 IH.
  rewrite !seq_cut_up_head' in IH |-*.
  apply Rle_trans with (1 := IH).
  rewrite /seq_step /= ; by apply RmaxLess2.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Rle_trans with (2 := RmaxLess1 _ _).
  by apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar.
  rewrite /seq_step /=.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Rle_trans with (2 := Rle_abs _), Rplus_le_compat_l, Ropp_le_contravar, Hab0.

  apply Rle_ge, (Rminus_le_0 lx1).
  revert ptd_l_behead ptd_l ; rewrite -Ha -Hb in Hab0 ; move: Hab0 ;
  apply SF_cons_ind with (s := ptd) => /= [x0 | [x0 y0] s IH] /= Hx0.
  case: Rle_dec => /= _.
  exact: Rle_refl.
  exact: (proj2 Hx0).
  move: (proj1 Hx0) ; case: Rle_dec => //= _ _.
  move: (fun Hx1 => IH (conj Hx1 (proj2 Hx0))) => {IH}.
  case: (Rle_dec (SF_h s)) => //= Hx1 IH.
  rewrite !seq_cut_up_head' in IH |-* ; move: (IH Hx1) => {IH}.
  move: Hx0 Hx1 ; apply SF_cons_dec with (s := s) => {s} /= [x1 | [x1 y1] /= s] Hx0 Hx1 IH.
  exact: Rle_refl.
  move: IH ; case: (Rle_dec (SF_h s)) => /= Hx2.
  by [].
  by [].
  by apply Rlt_le, Rnot_le_lt, Hx1.

  rewrite /alpha3 /=.
  apply (Rmax_case_strong (fmax - fmin)) => H.
  apply Req_le ; field.
  apply Rgt_not_eq, Rlt_le_trans with 1 ; by intuition.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2/2)).
  apply Rmult_le_compat_r, H.
  apply Rlt_le, eps4.

  clear H IH.
  rewrite !Rmult_1_l {1 2}/Rminus Rplus_assoc -Ropp_plus_distr.
  apply (f_equal (Rminus _)) => /=.
  rewrite /ptd_l /ptd_l_behead /ptd_l_head /= /SF_cut_up' /= ;
  move: Hab0 ; rewrite -Ha -Hb /= ;
  case => [Hx0 Hlx1].
  case: (Rle_dec (SF_h ptd)) => //= _.
  rewrite ?seq_cut_up_head' /SF_ly /= Riemann_sum_cons /=.
  move: Hx0 Hlx1 ; apply SF_cons_ind with (s := ptd)
    => [x0 | [x0 y0] s /= IH] /= Hx0 Hlx1.
  rewrite /Riemann_sum /= /plus /zero /scal /= /mult /= ; ring.
  case: (Rle_dec (SF_h s)) => //= Hx1.
  move: (IH Hx1 Hlx1) => /= {IH}.
  move: Hx1 Hlx1 ; apply SF_cons_dec with (s := s)
    => {s} [x1 | [x1 y1] s /=] /= Hx1 Hlx1 IH.
  rewrite /Riemann_sum /= /plus /zero /scal /= /mult /= ; ring.
  move: IH ; case: (Rle_dec (SF_h s)) => //= Hx2.
  move => <- ; apply Rminus_diag_uniq ; ring_simplify.
  move: Hx2 Hlx1 y1 ; apply SF_cons_ind with (s := s)
    => {s} [x2 | [x2 y2] s /= IH] /= Hx2 Hlx1 y1.
  ring.
  case: (Rle_dec (SF_h s)) => //= Hx3.
  by apply IH.
  ring.
  rewrite /Riemann_sum /= /plus /zero /scal /= /mult /=.
  ring_simplify.
  repeat apply f_equal.
  by elim: (SF_t s) (0) (y0).

  replace (fst (last (SF_h ptd, SF_h ptd) (SF_t ptd)))
    with (last (SF_h ptd) (unzip1 (SF_t ptd))).
Focus 2.
pattern (SF_h ptd) at 1.
replace (SF_h ptd) with (fst (SF_h ptd, SF_h ptd)) by auto.
elim: (SF_t ptd) (SF_h ptd, SF_h ptd) => //=.
  by rewrite Hb Ha.

  replace lx1 with (pos_Rl (RList.cons lx0 (RList.cons lx1 lx)) 1) by reflexivity.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ;
  case: Rle_dec => // _ <- <-.
  rewrite -(seq2Rlist_bij (RList.cons lx0 _)) !nth_compat size_compat.
  split.
  rewrite nth0.
  apply (sorted_head (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.
  simpl ; rewrite -last_nth.
  apply (sorted_last (Rlist2seq (RList.cons lx0 (RList.cons lx1 lx))) 1) with (x0 := 0).
  apply sorted_compat ; rewrite seq2Rlist_bij ; apply Had.
  simpl ; by apply lt_n_S, lt_O_Sn.

  rewrite -Ha -Hb /SF_lx /= => i Hi.
  apply le_lt_n_Sm in Hi ; rewrite -SF_size_lx /SF_lx in Hi.
  split.
  exact: (sorted_head (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).
  exact: (sorted_last (SF_h ptd :: unzip1 (SF_t ptd)) i (ptd_sort _ Hptd) Hi).

  clear H IH.
  move => x Hx ; case: (sorted_dec ([:: lx0, lx1 & Rlist2seq lx]) 0 x).
  apply sorted_compat ; rewrite /= seq2Rlist_bij ; apply Had.
  move: (proj1 (proj2 Had)) (proj1 (proj2 (proj2 Had))) ; rewrite /Rmin /Rmax ;
  case: Rle_dec => // _.
  rewrite -nth0 -nth_last /= => -> Hb'.
  split.
  by apply Hx.
  elim: (lx) (lx1) Hb' => /= [ | h1 s IH] h0 Hb'.
  rewrite Hb' ; by apply Hx.
  by apply IH.
  case => i ; case ; case ; case => {Hx} Hx Hx' Hi.
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (S i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ;
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  have : (((size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat) <
    size [:: lx0, lx1 & Rlist2seq lx])%nat.
    by [].
  replace (size [:: lx0, lx1 & Rlist2seq lx] - 1)%nat with
    (S (size [:: lx0, lx1 & Rlist2seq lx] - 2)) by (simpl ; intuition).
  move: (size [:: lx0, lx1 & Rlist2seq lx] - 2)%nat => i Hi.
  case ; case => {Hx} Hx ; [ case => Hx' | move => _ ].
  rewrite (proj2 (proj2 (proj2 (proj2 Had))) i).
  suff H : fmin1 <= pos_Rl (RList.cons ly0 ly) i <= fmax1.
  split.
  apply Rle_trans with (1 := Rmin_l _ _), H.
  apply Rle_trans with (2 := RmaxLess1 _ _), H.
  rewrite -(seq2Rlist_bij (RList.cons ly0 _)) nth_compat /= /fmin1 /fmax1 .
  have : (i < size (ly0 :: Rlist2seq ly))%nat.
    move: (proj1 (proj2 (proj2 (proj2 Had)))) Hi.
    rewrite /= -{1}(seq2Rlist_bij lx) -{1}(seq2Rlist_bij ly) ?size_compat /=
      => -> ; exact: lt_S_n.
  move: i {Hx Hx' Hi}.
  elim: (ly0 :: Rlist2seq ly) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  simpl in Hi |-* ; rewrite -size_compat seq2Rlist_bij in Hi ;
  by intuition.
  split.
  rewrite -nth_compat /= seq2Rlist_bij in Hx ; exact: Hx.
  rewrite -nth_compat /= seq2Rlist_bij in Hx' ; exact: Hx'.
  rewrite Hx'.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] (S i)) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx Hx'}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: s IH Hi => /= [ | h1 s] IH Hi.
  by apply lt_S_n, lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ;
  [ apply Rle_trans with (1 := Rmin_r _ _) ; exact: Rmin_l
  | apply Rle_trans with (2 := RmaxLess2 _ _) ; exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.
  rewrite -Hx.
  suff H : fmin2 <= phi (nth 0 [:: lx0, lx1 & Rlist2seq lx] i) <= fmax2.
  split.
  apply Rle_trans with (1 := Rmin_r _ _), H.
  apply Rle_trans with (2 := RmaxLess2 _ _), H.
  rewrite /fmin2 /fmax2 .
  move: i Hi {Hx}.
  elim: ([:: lx0, lx1 & Rlist2seq lx]) => [ | h0 s IH] i Hi.
  by apply lt_n_O in Hi.
  case: i Hi => /= [ | i] Hi.
  split ; [exact: Rmin_l | exact: RmaxLess1].
  split ;
  [apply Rle_trans with (1 := Rmin_r _ _)
  | apply Rle_trans with (2 := RmaxLess2 _ _)] ;
  apply IH ; by apply lt_S_n.

(* preuve de H *)
  clear eps eps2 IH eps4 alpha1.
  move: (proj1 (proj2 Had)) => /= ; rewrite /Rmin ;
    case: Rle_dec => //= _ <-.
  move: (proj1 Had O (lt_O_Sn _)) => /= Hl0l1.
  move: (proj2 (proj2 (proj2 (proj2 Had))) O (lt_O_Sn _)) => /= Hval.
  clear a b Hab Had lx ly.
  rename lx0 into a ; rename lx1 into b ;
  rename ly0 into c ; rename Hl0l1 into Hab.

  set fmin := Rmin (Rmin (phi a) (phi b)) c.
  set fmax := Rmax (Rmax (phi a) (phi b)) c.

  move => eps ; set eps2 := pos_div_2 eps.
  have Halpha : 0 < eps2 / (Rmax (fmax - fmin) 1).
    apply Rdiv_lt_0_compat.
    apply eps2.
    apply Rlt_le_trans with (2 := RmaxLess2 _ _), Rlt_0_1.
  set alpha := mkposreal _ Halpha.
  exists alpha => ptd.
  apply SF_cons_ind with (s := ptd)
    => {ptd} [x0 | [x0 y0] ptd IH] Hptd Hstep Ha Hb ; simpl in Ha, Hb.
  rewrite -Ha -Hb /Riemann_sum  /= ;
  rewrite Rminus_eq_0 Rmult_0_r Rminus_0_r Rabs_R0.
  by apply Rlt_le, eps.
  move: (fun Ha => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep) Ha Hb)
    => {IH} IH.
  move: (proj1 (ptd_sort _ Hptd)) ;
  rewrite Ha in Hptd, Hstep |- * => {x0 Ha} ;
  case => /= Ha.
  rewrite Riemann_sum_cons /= /plus /zero /scal /= /mult /= => {IH}.
  replace (_-_) with ((c-phi y0) * (SF_h ptd - a)
    + (c * (b - SF_h ptd) - Riemann_sum phi ptd))
    by ring.
  rewrite (double_var eps) ;
  apply Rle_trans with (1 := Rabs_triang _ _), Rplus_le_compat.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ;
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  rewrite -Hb ;
  apply (sorted_last (SF_lx ptd) 0 (proj2 (ptd_sort _ Hptd)) (lt_O_Sn _))
    with (x0 := 0).
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ;
  rewrite /seq_step /= ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.

  move: (ptd_cons _ _ Hptd)
  (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep : seq_step (SF_lx ptd) < alpha)
  Ha Hb => {Hptd Hstep y0} Hptd Hstep Ha Hb.
  suff : SF_h ptd <= b.
  case => Hx0.
  move: Hptd Hstep Ha Hb Hx0.
  apply SF_cons_ind with (s := ptd) => {ptd}
    [x0 | [x0 y0] ptd IH] Hptd Hstep /= Ha Hb Hx0.
  contradict Hb ; apply Rlt_not_eq, Hx0.
  move: (fun Hx1 => IH (ptd_cons _ _ Hptd) (Rle_lt_trans _ _ _ (RmaxLess2 _ _) Hstep)
    (Rlt_le_trans _ _ _ Ha (proj1 (ptd_sort _ Hptd))) Hb Hx1) => {IH} IH.
  rewrite Riemann_sum_cons /=.
  have : SF_h ptd <= b.
    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
    apply lt_O_Sn.
  case => Hx1.
  rewrite Hval /plus /scal /= /mult /=.
  replace (_-_) with (c * (b - SF_h ptd) - Riemann_sum phi ptd) by ring.
  by apply IH.
  split.
  apply Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_lt_trans with (2 := Hx1), (Hptd O (lt_O_Sn _)).
  rewrite Hx1 Riemann_sum_zero.
  change zero with 0.
  rewrite /plus /scal /= /mult /=.
  replace (_ - _) with ((c - phi y0) * (b - x0)) by ring.
  apply Rle_trans with ((fmax - fmin) * alpha).
  rewrite Rabs_mult ; apply Rmult_le_compat ; try exact: Rabs_pos.
  suff : a <= y0 <= b.
  case ; case => Ha'.
  case => Hb'.
  rewrite Hval.
  rewrite Rminus_eq_0 Rabs_R0 -Rminus_le_0 /fmin /fmax.
  rewrite /Rmin /Rmax ; case: Rle_dec ; case: Rle_dec ;
  case: Rle_dec => // H0 H1 H2.
  by apply Rlt_le, Rnot_le_lt, H1.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by apply Rle_refl.
  by apply Rlt_le, Rnot_le_lt, H0.
  by split.
  rewrite Hb' ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess2.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_r.
  rewrite -Ha' => _ ;
  apply Rabs_le_between ; rewrite Ropp_minus_distr' ; split ;
  apply Rplus_le_compat, Ropp_le_contravar.
  by apply Rmin_r.
  by apply Rle_trans with (2 := RmaxLess1 _ _), RmaxLess1.
  by apply RmaxLess2.
  by apply Rle_trans with (1 := Rmin_l _ _), Rmin_l.
  split.
  apply Rlt_le, Rlt_le_trans with (1 := Ha), (Hptd O (lt_O_Sn _)).
  apply Rle_trans with (SF_h ptd).
  apply (Hptd O (lt_O_Sn _)).
  by apply Req_le.
  apply Rlt_le, Rle_lt_trans with (2 := Hstep) ;
  rewrite /seq_step /= -Hx1 ; apply RmaxLess1.
  rewrite /alpha /= ; apply (Rmax_case_strong (fmax-fmin)) => H.
  apply Req_le ; field.
  by apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1), H.
  rewrite Rdiv_1 -{2}(Rmult_1_l (eps/2)) ; apply Rmult_le_compat_r.
  apply Rlt_le, eps2.
  apply H.
  apply ptd_sort, (ptd_cons (x0,y0)), Hptd.
  by rewrite /SF_lx /= Hb.
  rewrite Hx0 Riemann_sum_zero.
  change zero with 0.
  replace (c * (b - b) - 0) with 0 by ring.
  rewrite Rabs_R0 ; apply Rlt_le, eps2.
  apply ptd_sort, Hptd.
  by rewrite /SF_lx /= Hb.

    rewrite -Hb ; apply (sorted_last ((SF_h ptd)::(unzip1 (SF_t ptd))) O) with (x0 := 0).
    apply ptd_sort, Hptd.
    apply lt_O_Sn.
  rewrite Riemann_sum_cons /= -Ha.
  rewrite Rminus_eq_0 scal_zero_l plus_zero_l.
  by apply IH.
Qed.

Lemma ex_RInt_Reals_1 (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> ex_RInt f a b.
Proof.
  move => pr ; exists (RiemannInt pr).
  exact: ex_RInt_Reals_aux_1.
Qed.


Lemma ex_RInt_Reals_0 (f : R -> R) (a b : R) :
  ex_RInt f a b -> Riemann_integrable f a b.
Proof.
  wlog: a b /(a < b) => [Hw | Hab ] Hex.
    case: (Rle_lt_dec a b) => Hab.
    case: (Rle_lt_or_eq_dec _ _ Hab) => {Hab} Hab.
    by apply Hw.
    rewrite -Hab.
    by apply RiemannInt_P7.
    apply ex_RInt_swap in Hex ;
    apply RiemannInt_P1 ;
    by apply Hw.
  assert ({If : R | is_RInt f a b If}).
    exists (RInt f a b).
    exact: RInt_correct.
  case: H => If HIf.
  generalize (proj1 (filterlim_locally _ If) HIf).
  clear HIf.
  intros HIf.
  set (E := fun eps : posreal =>
    (fun alpha => 0 < alpha <= b-a + 1 /\
      forall ptd : SF_seq,
        pointed_subdiv ptd ->
        seq_step (SF_lx ptd) < alpha ->
        SF_h ptd = Rmin a b ->
        last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
        Rabs (If - sign (b - a) * Riemann_sum f ptd) < eps)).
  have E_bnd : forall eps : posreal, bound (E eps).
    move => eps ; exists (b-a+1) => x [Hx _] ; by apply Hx.
  have E_ex : forall eps : posreal, exists x, (E eps x).
    move => eps ; case: (HIf eps) => {HIf} alpha HIf.
    exists (Rmin alpha (b-a + 1)) ; split.
    apply Rmin_case_strong => H.
    split.
    by apply alpha.
    exact: H.
    split.
    apply Rplus_le_lt_0_compat.
    by apply (Rminus_le_0 a b), Rlt_le.
    exact: Rlt_0_1.
    exact: Rle_refl.
    intros.
    rewrite Rabs_minus_sym.
    apply: HIf.
    move: H0 ; apply Rmin_case_strong.
    by [].
    move => Halp Hstep ; by apply Rlt_le_trans with (b-a+1).
    split.
    exact: H.
    split.
    exact: H1.
    exact: H2.
  set alpha := fun eps : posreal => proj1_sig (completeness (E eps) (E_bnd eps) (E_ex eps)).
  have Ealpha : forall eps : posreal, (E eps (alpha eps)).
    revert alpha ; move => /= eps.
    case: (E_ex eps) => alp H.
    case: completeness => alpha [ub lub] /= ; split.
    split.
    apply Rlt_le_trans with alp.
    by apply H.
    by apply ub.
    apply: lub => x [Hx _] ; by apply Hx.
    intros.
    apply Rnot_le_lt ; contradict H1.
    apply Rle_not_lt.
    apply: lub => x [Hx1 Hx2].
    apply Rnot_lt_le ; contradict H1.
    by apply Rlt_not_le, Hx2.
  have Hn : forall eps : posreal, {n : nat | (b-a)/(INR n + 1) < alpha eps}.
    move => eps.
    have Hn : 0 <= (b-a)/(alpha eps).
      apply Rdiv_le_0_compat.
      by apply Rlt_le, Rgt_minus.
      by apply Ealpha.
    set n := (nfloor _ Hn).
    exists n.
    apply Rlt_div_l.
    by apply INRp1_pos.
    rewrite Rmult_comm ; apply Rlt_div_l.
    by apply Ealpha.
    rewrite /n /nfloor ; case: nfloor_ex => /= n' Hn'.
    by apply Hn'.

  rewrite /Riemann_integrable.
  suff H : forall eps : posreal,
    {phi : StepFun a b &
    {psi : StepFun a b |
    (forall t : R, Rmin a b <= t <= Rmax a b -> Rabs (f t - phi t) <= psi t) /\
    Rabs (RiemannInt_SF psi) <= eps}}.
  move => eps ; set eps2 := pos_div_2 eps.
  case: (H eps2) => {H} phi [psi [H H0]].
  exists phi ; exists psi ; split.
  exact: H.
  apply Rle_lt_trans with (1 := H0).
  apply Rminus_gt ; simpl ; field_simplify ; rewrite Rdiv_1 ; by apply eps2.

  move => eps ; set eps2 := pos_div_2 eps.
  case: (Hn eps2) => {Hn} n Hn.
  case: (Ealpha eps2) => {HIf} Halpha HIf.

(* Construire phi *)
  set phi := sf_SF_val_fun f a b n.
  exists phi.
(* Construire psi *)
  set psi1 := SF_sup_r (fun t => Rabs (f t - phi t)) a b n.
  have Haux : forall x,
    {i : nat | x = nth 0 (unif_part a b n) i /\ (i < size (unif_part a b n))%nat}
    + {(forall i, (i < size (unif_part a b n))%nat -> x <> nth 0 (unif_part a b n) i)}.
    move => x.
    have : {n0 : nat | x = nth 0 (unif_part a b n) n0
      /\ (n0 < size (unif_part a b n))%nat} +
      {(forall n0 : nat,
      ~ (x = nth 0 (unif_part a b n) n0
      /\ (n0 < size (unif_part a b n))%nat))}.
    apply (LPO (fun i => x = nth 0 (unif_part a b n) i
      /\ (i < size (unif_part a b n))%nat)).
    move => i.
    case: (Req_EM_T x (nth 0 (unif_part a b n) i)) => Hx.
    case: (lt_dec i (size (unif_part a b n))) => Hi.
    left ; split ; by [].
    right ; contradict Hi ; by apply Hi.
    right ; contradict Hx ; by apply Hx.
    case => [[i Hi] | Hx].
    left ; by exists i.
    right => i Hi ;
    move: (Hx i) => {Hx} Hx ;
    contradict Hx ; by split.
  set psi2_aux := fun x => match Haux x with
    | inleft Hi => Rabs (f x - phi x) - psi1 x
    | inright _ => 0
  end.
  set psi2_ly := seq2Rlist (SF_ly (SF_seq_f1 (fun _ => 0) (unif_part a b n))).
  have psi2_ad : adapted_couple psi2_aux a b (seq2Rlist (unif_part a b n)) psi2_ly.
    split.
    by apply sorted_compat, unif_part_sort, Rlt_le.
    split.
    rewrite /Rmin ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    split.
    rewrite size_compat size_mkseq nth_compat nth_mkseq ?S_INR /=.
    rewrite /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ;
    field ; apply Rgt_not_eq ; by intuition.
    by [].
    split.
    by rewrite !size_compat SF_ly_f1 size_belast' size_map.
    rewrite size_compat => i Hi ;
    rewrite !nth_compat SF_ly_f1 => x Hx.
    rewrite /psi2_aux => {psi2_aux} ;
    case: Haux => [ [j [Hx' Hj]] | Hx' ].
    rewrite Hx' in Hx |- * ; case: Hx => Hxi Hxj.
    case: (lt_dec i j) => Hij.
    contradict Hxj ; apply Rle_not_lt.
    apply sorted_incr.
    by apply unif_part_sort, Rlt_le.
    by [].
    by [].
    contradict Hxi ; apply Rle_not_lt.
    apply sorted_incr.
    by apply unif_part_sort, Rlt_le.
    by apply not_lt.
    by intuition.
    move: i Hi {Hx} ;
    elim: (unif_part a b n) => /= [ i Hi | x0].
    by apply lt_n_O in Hi.
    case => /= [ | x1 s] IH i Hi.
    by apply lt_n_O in Hi.
    case: i Hi => /= [ | i] Hi.
    by [].
    by apply IH, lt_S_n.
  have psi2_is : IsStepFun psi2_aux a b.
    exists (seq2Rlist (unif_part a b n)).
    exists psi2_ly.
    by [].
  set psi2 := mkStepFun psi2_is.
  set psi := mkStepFun (StepFun_P28 1 psi1 psi2).

  exists psi.

have Hfin : forall i, (S i < size (unif_part a b n))%nat ->
  is_finite (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0))
    (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
  case: (ex_RInt_ub f a b Hex) => M HM.
  case: (StepFun_bound phi) => M' HM'.
  have : exists m, forall x : R, Rmin a b <= x <= Rmax a b -> m <= phi x.
    case: (StepFun_bound (mkStepFun (StepFun_P28 (-1) (mkStepFun (StepFun_P4 a b 0)) phi)))
    => /= m' Hm'.
    exists (-m') => x Hx.
    replace (phi x) with (- (fct_cte 0 x + -1 * phi x))
      by (rewrite /fct_cte /= ; ring).
    by apply Ropp_le_contravar, Hm'.
  case => m' Hm' i ;
  rewrite size_mkseq => Hi ;
  rewrite !nth_mkseq.
  rewrite /Sup_fct.
  have H : (a + INR i * (b - a) / (INR n + 1)) <
    (a + (INR (S i)) * (b - a) / (INR n + 1)).
    rewrite S_INR ; apply Rminus_gt ; field_simplify.
    rewrite Rdiv_1 Rplus_comm ; apply Rdiv_lt_0_compat.
    by apply Rgt_minus.
    by apply INRp1_pos.
    by apply Rgt_not_eq, INRp1_pos.
  move: (Rlt_not_eq _ _ H) ; case: Req_EM_T => // H0 _.
  rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ H) => // _ _.
  rewrite /Lub_Rbar ; case: ex_lub_Rbar ; case => [l | | ] [ub lub] /=.
  by [].
  case: (lub (Finite (Rmax (M - m') (-(-M - M'))))) => //.
  move => _ [x [-> Hx]].
  apply Rabs_le_between_Rmax.
  suff H2 : Rmin a b <= x <= Rmax a b.
  split ; apply Rplus_le_compat, Ropp_le_contravar.
  apply Ropp_le_cancel, Rle_trans with (Rabs (f x)).
  by apply Rabs_maj2.
  rewrite Ropp_involutive ; by apply HM.
  by apply HM'.
  apply Rle_trans with  (Rabs (f x)).
  by apply Rle_abs.
  by apply HM.
  by apply Hm'.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _ ; split ;
  apply Rlt_le.
  replace a with (a + INR O * (b - a) / (INR n + 1))
    by (simpl ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rle_lt_trans with (2 := proj1 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  replace b with (a + INR (S n) * (b - a) / (INR n + 1))
    by (rewrite S_INR ; field ; apply Rgt_not_eq, INRp1_pos).
  apply Rlt_le_trans with (1 := proj2 Hx).
  apply Rplus_le_compat_l, Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat ; by intuition.
  apply Rmult_le_compat_r.
  by apply Rlt_le, Rgt_minus.
  apply le_INR ; by intuition.
  move: (a + INR i * (b - a) / (INR n + 1)) (a + INR (S i) * (b - a) / (INR n + 1)) ub H.
  clear => a0 b0 ub H.
  specialize (ub (Rabs (f ((a0 + b0) / 2) - phi ((a0 + b0) / 2)))) ; simpl in ub.
  assert (exists x : R,
    Rabs (f ((a0 + b0) / 2) - phi ((a0 + b0) / 2)) = Rabs (f x - phi x) /\
    a0 < x < b0).
  eexists ; split => //.
  lra.
  by [].

  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.

have Hfin' : forall t, is_finite (SF_sup_fun (fun t : R => Rabs (f t - phi t)) a b n t).
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  case: (unif_part a b n) Hfin => [ | x0 sx] /=.
  move => _ t ; by case: Rle_dec.
  case: sx => [ | x1 sx] /=.
  move => _ t ; by case: Rle_dec.
  move => H t.
  case: Rlt_dec => Hx0.
  by [].
  elim: sx x0 x1 H Hx0 => [ | x2 sx IH] x0 x1 /= H Hx0.
  case: Rle_dec => Hx1.
  apply (H O) ; by intuition.
  by [].
  case: Rlt_dec => Hx1.
  apply (H O) ; by intuition.
  apply IH.
  move => i Hi ; apply (H (S i) (lt_n_S _ _ Hi)).
  exact: Hx1.

  split.
(* Partie 1 *)
  move => t Ht_ab.
  move: Ht_ab ; rewrite /Rmin /Rmax ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _ Ht_ab.
  rewrite /= /psi2_aux /= ; case: (Haux t) => [ [i Hi] | Hi ] ;
  ring_simplify.
  exact: Rle_refl.
  change (Rbar_le (Rabs (f t - phi t)) (real (SF_sup_fun (fun t0 : R => Rabs (f t0 - phi t0)) a b n t))).
  rewrite Hfin'.
  rewrite /SF_sup_fun ; case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite /SF_fun /SF_sup_seq.
  move: (unif_part_sort a b n (Rlt_le _ _ Hab)).
  move: Ht_ab.
  pattern b at 1 ; replace b with (last 0 (unif_part a b n)).
  pattern a at 1 ; replace a with (head 0 (unif_part a b n)).
  have : (0 < size (unif_part a b n))%nat.
    rewrite size_mkseq ; exact: lt_O_Sn.
  case: (unif_part a b n) Hi => [ | x0 sx] Hi Hsx Ht_ab Hsort /=.
  by apply lt_irrefl in Hsx.
  clear Hsx.
  case: sx Hsort Hi Ht_ab => [ | x1 sx] Hsort /= Hi [Ht_a Ht_b].
  move: (Rle_antisym _ _ Ht_b Ht_a) => Ht.
  contradict Ht ; apply (Hi O (lt_n_Sn _)).
  apply Rle_not_lt in Ht_a.
  case: Rlt_dec => // _.
  elim: sx x0 x1 Hsort Ht_a Ht_b Hi => [ | x2 sx IH] x0 x1 Hsort /= Ht_a Ht_b Hi.
  case: Rle_dec => // _.
  rewrite /Sup_fct /Lub_Rbar.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    case: Ht_b => Ht_b.
    by [].
    contradict Ht_b ; apply (Hi 1%nat).
    by apply lt_n_Sn.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  case: Ht_b => Ht_b.
  by [].
  contradict Ht_b ; apply (Hi 1%nat).
  by apply lt_n_Sn.
  case: Rlt_dec => Hx1.
   rewrite /Sup_fct /Lub_Rbar.
  have H : x0 < x1.
    apply Rlt_trans with t.
    apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
    by [].
    contradict Ht_a ; apply sym_not_eq, (Hi O).
    by apply lt_O_Sn.
    by apply Hx1.
  move: (Rlt_not_eq _ _ H) ;
  case: Req_EM_T => // H0 _.
  case: ex_lub_Rbar => l lub /=.
  apply lub ; exists t ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _ ;
  split.
  apply Rnot_lt_le in Ht_a ; case: Ht_a => Ht_a.
  by [].
  contradict Ht_a ; apply sym_not_eq, (Hi O).
  by apply lt_O_Sn.
  by [].
  apply IH.
  exact: (proj2 Hsort).
  exact: Hx1.
  exact: Ht_b.
  move => j Hj ; apply (Hi (S j) (lt_n_S _ _ Hj)).
  apply head_unif_part.
  apply last_unif_part.

(* Partie 2 *)
(* * SF_lx ptd = unif_part a b n *)
  assert (forall g : R -> R -> R,
    let ptd := SF_seq_f2 g (unif_part a b n) in
    pointed_subdiv ptd ->
    Rabs (If - sign (b-a) * Riemann_sum f ptd) < eps2).
  move => g ptd Hptd.
  apply HIf.
  exact: Hptd.
  rewrite SF_lx_f2.
  suff : forall i, (S i < size (unif_part a b n))%nat ->
    nth 0 (unif_part a b n) (S i) - nth 0 (unif_part a b n) i = (b-a)/(INR n + 1).
  elim: (unif_part a b n) => /= [ | h0 t IH].
  move => _ ; by apply Ealpha.
  case: t IH => /= [ | h1 t] IH Hnth.
  by apply Ealpha.
  replace (seq_step _) with (Rmax (Rabs (h1 - h0)) (seq_step (h1::t))) by auto.
  apply (Rmax_case_strong (Rabs (h1 - h0))) => /= _.
  rewrite (Hnth O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite Rabs_right.
  exact: Hn.
  apply Rle_ge, Rdiv_le_0_compat.
  by apply Rlt_le, Rgt_minus.
  by intuition.
  apply IH => i Hi.
  by apply (Hnth (S i)), lt_n_S.
  move => i ; rewrite size_mkseq => Hi ; rewrite !nth_mkseq.
  rewrite S_INR ; field ; apply Rgt_not_eq ; by intuition.
  apply SSR_leq ; by intuition.
  apply SSR_leq ; by intuition.
  by apply lt_0_Sn.
  rewrite -> Rmin_left by now apply Rlt_le.
  apply head_unif_part.
  rewrite -nth_last SF_lx_f2.
  change (head 0 (unif_part a b n) :: behead (unif_part a b n))
    with (unif_part a b n).
  rewrite -> Rmax_right by now apply Rlt_le.
  rewrite size_mkseq nth_mkseq.
  simpl ssrnat.predn ; rewrite S_INR ;
  field ; apply Rgt_not_eq ; by intuition.
  simpl ; apply SSR_leq, le_refl.
  by apply lt_O_Sn.
  move: H => {HIf} HIf.
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
    Rabs (Riemann_sum f ptd1 - Riemann_sum f ptd2) < eps).
  move => g1 g2 ptd1 ptd2 H1 H2.
  replace (Riemann_sum f ptd1 - Riemann_sum f ptd2) with
    ((If - sign (b - a) * Riemann_sum f ptd2) -
      (If - sign (b - a) * Riemann_sum f ptd1)).
  apply Rle_lt_trans with (1 := Rabs_triang _ _).
  rewrite Rabs_Ropp (double_var eps) ; apply Rplus_lt_compat ;
  by apply HIf.
  rewrite -> sign_eq_1 by exact: Rlt_Rminus.
  ring.
  move: H => {HIf} HIf.
  rewrite /Riemann_sum in HIf.
(* * oublier If *)
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      Rabs
        (Riemann_sum (fun x => x) (SF_seq_f2 (fun x y => f (g1 x y) - f (g2 x y))
          (unif_part a b n))) < eps).
  move => g1 g2 ptd1 pdt2 H1 H2.
  replace (Riemann_sum _ _ : R) with
    (Riemann_sum f (SF_seq_f2 g1 (unif_part a b n)) -
    Riemann_sum f (SF_seq_f2 g2 (unif_part a b n))).
  apply HIf.
  exact: H1.
  exact: H2.
  elim: (unif_part a b n) => /= [ | h0].
  rewrite /Riemann_sum /= /plus /zero /= ; ring.
  case => /= [ | h1 t] IH.
  rewrite /Riemann_sum /= /plus /zero /= ; ring.
  rewrite !(SF_cons_f2 _ h0) /= ; try by intuition.
  rewrite !Riemann_sum_cons /= -IH /plus /scal /= /mult /= ; ring.
  move:H => {HIf} HIf.
(* * faire rentrer Rabs dans l'intégrale *)
  assert (forall g1 g2 : R -> R -> R,
    let ptd1 := SF_seq_f2 g1 (unif_part a b n) in
    let ptd2 := SF_seq_f2 g2 (unif_part a b n) in
    pointed_subdiv ptd1 -> pointed_subdiv ptd2 ->
      Riemann_sum id
      (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
      (unif_part a b n)) < eps).
  move => g1 g2 ptd1 ptd2 H1 H2.
  set h1 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g2 x y | right _ => g1 x y end.
  set h2 := fun x y => match Rle_dec (f (g1 x y)) (f (g2 x y)) with
    | left _ => g1 x y | right _ => g2 x y end.
  replace (Riemann_sum id
    (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
    (unif_part a b n))) with
    (Riemann_sum id (SF_seq_f2 (fun x y : R => (f (h1 x y) - f (h2 x y)))
    (unif_part a b n))).
  apply Rle_lt_trans with (1 := Rle_abs _).
  apply HIf.
    revert ptd1 ptd2 H1 H2.
    elim: (unif_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h1 ; case: Rle_dec => //= _.
    apply (H2 O (lt_O_Sn _)).
    apply (H1 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
    revert ptd1 ptd2 H1 H2.
    elim: (unif_part a b n) (0) => [z /= _ _ | x0].
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    case => [ | x1 t] /= IH z H1 H2.
    move => i ; rewrite /SF_size /= => Hi ; by apply lt_n_O in Hi.
    move: H1 H2 ; rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    move => H1 H2 ; case => [ | i] /= Hi.
    rewrite /h2 ; case: Rle_dec => //= _.
    apply (H1 O (lt_O_Sn _)).
    apply (H2 O (lt_O_Sn _)).
    apply (IH x0 (ptd_cons _ _ H1) (ptd_cons _ _ H2)).
    apply lt_S_n, Hi.
  elim: (unif_part a b n) (0) => [x0 | x0].
  by rewrite /Riemann_sum /= .
  case => [ | x1 t] IH z.
  by rewrite /Riemann_sum /= .
  rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /h1 /h2 /id ; case: Rle_dec => H0.
  rewrite Rabs_left1.
  apply f_equal.
  simpl ; ring.
  by apply Rle_minus.
  rewrite Rabs_right.
  apply f_equal.
  simpl ; ring.
  by apply Rgt_ge, Rgt_minus, Rnot_le_lt.
  by apply IH.
  move: H => {HIf} HIf.
(* * phi (g x y) = f (h x y) *)
  assert (forall g : R -> R -> R,
    (forall i j, (S i < size (unif_part a b n))%nat ->
      (j < size (unif_part a b n))%nat ->
      g (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))
      <> nth 0 (unif_part a b n) j) ->
    let ptd := SF_seq_f2 g (unif_part a b n) in
    pointed_subdiv ptd ->
    Riemann_sum id
    (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
    (unif_part a b n)) < eps).
  move => g1 Hg1 ptd1 H1.
  rewrite /phi /sf_SF_val_fun ; case: Rle_dec (Rlt_le _ _ Hab) => //= _ _.
  move: (unif_part_nat a b n) => Hp.
  set h := fun t => match Rle_dec a t with
    | right _ => t
    | left Ha => match Rle_dec t b with
      | right _ => t
      | left Hb => match Hp t (conj Ha Hb) with
        | inleft H => (a + (INR (proj1_sig H) + /2) * (b - a) / (INR n + 1))
        | inright _ => (a + (INR n + /2) * (b - a) / (INR n + 1))
      end
    end
  end.
  set g2 := fun x y => h (g1 x y).
  set ptd2 := SF_seq_f2 g2 (unif_part a b n).
  have H2 : pointed_subdiv ptd2.
    move => i ; move: (H1 i) => {H1}.
    rewrite !SF_lx_f2 ; (try by apply lt_O_Sn) ;
    rewrite !SF_ly_f2 !SF_size_f2 size_mkseq.
    move => H1 Hi ; move: (H1 Hi) => {H1}.
    simpl in Hi.
    rewrite !nth_behead !(nth_pairmap 0).
    replace (nth 0 (0 :: unif_part a b n) (S i)) with
      (nth 0 (unif_part a b n) i) by auto.
    rewrite /g2 /h => {h g2 ptd2 ptd1} H1.
    case: Rle_dec => Ha.
    case: Rle_dec => Hb.
    case: Hp => [ [j [Ht Hj]] | Ht] ; simpl proj1_sig.
    suff Hij : j = i.
    rewrite Hij in Ht, Hj |- * => {j Hij}.
    rewrite !nth_mkseq.
    rewrite S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    generalize (pos_INR n) ; lra.
    apply Rgt_not_eq ; by intuition.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    generalize (pos_INR n) ; lra.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply SSR_leq ; rewrite size_mkseq in Hi, Hj ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (unif_part a b n) j < nth 0 (unif_part a b n) (S i).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply (Hg1 i (S i)).
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_S.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    by intuition.
    move: (Rle_lt_trans _ _ _ (proj1 H1) (proj2 Ht)) => Hij.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    suff : i = n.
    move => ->.
    rewrite !nth_mkseq ?S_INR.
    split ; simpl ; apply Rminus_le_0 ; field_simplify.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    generalize (pos_INR n) ; lra.
    apply Rgt_not_eq ; by intuition.
    rewrite Rdiv_1 ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm -Rminus_le_0 ; exact: (Rlt_le _ _ Hab).
    generalize (pos_INR n) ; lra.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
    apply le_antisym ; apply not_lt.
    have Hij : nth 0 (unif_part a b n) i < nth 0 (unif_part a b n) (S n).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply H1.
      case: (proj2 Ht) => {Ht} Ht.
      exact: Ht.
      contradict Ht ; apply Hg1.
      rewrite size_mkseq ; by apply lt_n_S.
      rewrite size_mkseq ; by apply lt_n_Sn.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le , Hab.
    by intuition.
    rewrite size_mkseq ; by intuition.
    have Hij : nth 0 (unif_part a b n) (n) < nth 0 (unif_part a b n) (S i).
      apply Rle_lt_trans with
        (g1 (nth 0 (unif_part a b n) i) (nth 0 (unif_part a b n) (S i))).
      by apply Ht.
      case: (proj2 H1) => {H1} H1.
      exact: H1.
      contradict H1 ; apply Hg1.
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq ; by intuition.
    contradict Hij.
    apply Rle_not_lt, sorted_incr.
    apply unif_part_sort, Rlt_le, Hab.
    by [].
    rewrite size_mkseq ; by intuition.
    exact: H1.
    exact: H1.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    apply SSR_leq ; rewrite size_mkseq ; by intuition.
    move: (HIf g1 g2 H1 H2).
    replace (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - SF_val_fun f a b n (g1 x y)))
     (unif_part a b n)) with
     (SF_seq_f2 (fun x y : R => Rabs (f (g1 x y) - f (g2 x y)))
     (unif_part a b n)).
    by [].
    have H0 : forall t, a <= t <= b -> SF_val_fun f a b n t = f (h t).
      move => t Ht.
      rewrite /h SF_val_fun_rw.
      case: Ht => Ha Hb.
      case: Rle_dec => // Ha'.
      case: Rle_dec => // Hb'.
      case: unif_part_nat => [ [i [Ht Hi]] | Ht] ;
      case: Hp {h g2 ptd2 H2} => [ [j [Ht' Hj]] | Ht'] ; simpl proj1_sig.
      apply (f_equal (fun i => f (a + (INR i + /2) * (b - a) / (INR n + 1)))).
      apply le_antisym ; apply not_lt.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      apply unif_part_sort, Rlt_le, Hab.
      by [].
      by intuition.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      by intuition.
      absurd (i < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht') (proj2 Ht)) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hi ; by intuition.
      absurd (j < n)%nat.
      move: (Rle_lt_trans _ _ _ (proj1 Ht) (proj2 Ht')) => Hij ;
      contradict Hij.
      apply Rle_not_lt, sorted_incr.
      by apply unif_part_sort, Rlt_le.
      by [].
      rewrite size_mkseq ; by intuition.
      rewrite size_mkseq in Hj ; by intuition.
      by [].
    rewrite /g2.
  have : forall i, (i < size (unif_part a b n))%nat ->
    a <= nth 0 (unif_part a b n) i <= b.
    move => i ; rewrite size_mkseq => Hi ; rewrite nth_mkseq.
    pattern b at 3 ; replace b with (a + (INR n + 1) * (b - a) / (INR n + 1)) by
      (field ; apply Rgt_not_eq ; intuition).
    pattern a at 1 ; replace a with (a + 0 * (b - a) / (INR n + 1)) by
      (field ; apply Rgt_not_eq ; intuition).
    apply Rgt_minus in Hab.
    split ; apply Rplus_le_compat_l ; repeat apply Rmult_le_compat_r ;
    try by intuition.
    rewrite -S_INR ; apply le_INR ; by intuition.
    by apply SSR_leq.
    revert ptd1 H1 ;
    elim: (unif_part a b n) => [ ptd1 H1 Hnth | x0 ].
    by [].
    case => [ | x1 s] IH ptd1 H1 Hnth.
    by [].
    revert ptd1 H1 ;
    rewrite !(SF_cons_f2 _ x0) /= ; try by intuition.
    intro ;
    apply (f_equal2 (fun x y => SF_cons (x0, Rabs (f (g1 x0 x1) - x)) y)).
    apply sym_equal, H0.
    move: (H1 O (lt_O_Sn _))
      (Hnth O (lt_O_Sn _)) (Hnth 1%nat (lt_n_S _ _ (lt_O_Sn _))) => /= ; intuition.
    by apply Rle_trans with x0.
    by apply Rle_trans with x1.
    apply (IH (ptd_cons _ _ H1)).
    move => i Hi ; apply (Hnth (S i)) ; simpl in Hi |- * ; by apply lt_n_S.

  move: H => {HIf} HIf.
  rewrite Rabs_right.

(* * dernière étape :-) *)
  replace (RiemannInt_SF psi) with
    (Riemann_sum id (SF_seq_f2 (fun x y : R => real (Sup_fct (fun t => Rabs (f t - phi t)) x y))
    (unif_part a b n))).
  set (F := fun s val => exists g : R -> R -> R,
    (forall (i j : nat),
    (S i < size s)%nat -> (j < size s)%nat
      -> g (nth 0 s i) (nth 0 s (S i)) <> nth 0 s j) /\
    (let ptd := SF_seq_f2 g s in pointed_subdiv ptd) /\
    Riemann_sum id (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y)))
      s) = val).
  cut (is_lub (F (unif_part a b n)) (Riemann_sum id (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (unif_part a b n)))) => [ Hlub | ].

  apply Hlub => val [g [Hnth [H0 Hval]]].
  apply Rlt_le ; rewrite -Hval.
  apply HIf.
  exact: Hnth.
  exact: H0.

  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (unif_part a b n) (unif_part_sort a b n (Rlt_le _ _ Hab))
  => [ Hsort | x0 ].
  by [].
  case => [ | x1 s] IH Hsort.
  by [].
  rewrite SF_cons_f2 /=.
  rewrite Riemann_sum_cons /=.
  rewrite Rmult_comm.
  by apply f_equal, IH, Hsort.
  exact: lt_O_Sn.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (unif_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.

  Focus 2.
  rewrite StepFun_P30.
  replace (RiemannInt_SF psi2) with 0.
  rewrite Rmult_0_r Rplus_0_r ;
  rewrite /RiemannInt_SF SF_sup_subdiv SF_sup_subdiv_val ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  elim: (unif_part a b n) (unif_part_sort a b n (Rlt_le _ _ Hab))
    => [ Hsort /= | x0].
  by apply Rge_refl.
  case => [ | x1 s] IH Hsort /=.
  by apply Rge_refl.
  apply Rle_ge, Rplus_le_le_0_compat.
  apply Rmult_le_pos.
  rewrite /Sup_fct /Lub_Rbar.
  case: Req_EM_T => Hx0.
  by apply Rle_refl.
  case: ex_lub_Rbar ;
  case => [l | | ] [ub lub] /=.
  apply Rle_trans with (Rabs (f ((x0+x1)/2) - phi ((x0+x1)/2))).
  apply Rabs_pos.
  apply ub.
  exists ((x0+x1)/2) ; split.
  by [].
  rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hsort) => // _ _.
  pattern x1 at 3 ; replace x1 with ((x1 + x1)/2) by field.
  pattern x0 at 1 ; replace x0 with ((x0 + x0)/2) by field.
  split ; apply Rmult_lt_compat_r.
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_l ; by case: (proj1 Hsort).
  by apply Rinv_0_lt_compat, Rlt_R0_R2.
  apply Rplus_lt_compat_r ; by case: (proj1 Hsort).
  apply Rle_refl.
  apply Rle_refl.
  apply -> Rminus_le_0 ; apply Hsort.
  apply Rge_le, IH, Hsort.
  rewrite /RiemannInt_SF ;
  case: Rle_dec (Rlt_le _ _ Hab) => // _ _.
  rewrite (StepFun_P17 (StepFun_P1 psi2) psi2_ad).
  clear psi2_ad.
  revert psi2_ly ; elim: (unif_part a b n) => /= [ | x0].
  by [].
  case => /= [ | x1 s] IH.
  by [].
  rewrite -IH ; ring.

(* ** c'est la bonne borne sup *)

  move: Hfin.
  have : sorted Rlt (unif_part a b n).
    apply sorted_nth => i.
    rewrite size_mkseq => Hi x0 ; rewrite !nth_mkseq.
    apply Rminus_gt ; rewrite S_INR ; field_simplify.
    rewrite Rdiv_1.
    apply Rdiv_lt_0_compat.
    rewrite Rplus_comm ; by apply Rgt_minus.
    by intuition.
    apply Rgt_not_eq ; by intuition.
    apply SSR_leq ; by intuition.
    apply SSR_leq ; by intuition.
  elim: (unif_part a b n) (unif_part_sort a b n (Rlt_le _ _ Hab))
    => [ Hle Hlt Hfin | x1].
  split ; rewrite /Riemann_sum /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj ; by apply lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  case => [ | x2 s] IH Hle Hlt Hfin.
  split ; rewrite /Riemann_sum /=.
  move => val [g [Hnth [Hptd Hval]]].
  rewrite -Hval ; by apply Rle_refl.
  move => ub Hub ; apply: Hub.
  exists (fun _ _ => 0).
  split.
  move => i j Hi Hj.
  simpl in Hi ; by apply lt_S_n, lt_n_O in Hi.
  split.
  move => ptd i Hi ; by apply lt_n_O in Hi.
  split.
  rewrite SF_cons_f2 /= ; last by apply lt_O_Sn.
  rewrite Riemann_sum_cons /=.
  set F0 := fun x =>
    exists t, x1 < t < x2 /\ x = Rabs (f t - phi t) * (x2 - x1).
  set set_plus := fun (F : R -> Prop) (G : R -> Prop) (x : R) =>
    exists y, exists z, x = y + z /\ F y /\ G z.
  suff H0 : forall (x : R), F [:: x1, x2 & s] x
    <-> (set_plus (F0) (F (x2::s))) x.
  cut (is_lub (set_plus (F0) (F (x2::s)))
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1) +
    Riemann_sum id
    (SF_seq_f2
    (fun x y : R => real (Sup_fct (fun t : R => Rabs (f t - phi t)) x y))
    (x2 :: s)))) => [H1 | ].
  split.
  move => x Hx.
  rewrite /plus /scal /= /mult /= Rmult_comm.
  by apply H1, H0.
  move => ub Hub.
  rewrite /plus /scal /= /mult /= Rmult_comm.
  apply H1 => x Hx ; by apply Hub, H0.
  suff H_F0 : is_lub (F0) (real (Sup_fct
    (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1)).
  have Hfin0 : (forall i : nat,
    (S i < size (x2 :: s))%nat ->
    is_finite
    (Sup_fct (fun t0 : R => Rabs (f t0 - phi t0)) (nth 0 (x2 :: s) i)
       (nth 0 (x2 :: s) (S i)))).
    move => i /= Hi ; move: (Hfin (S i) (lt_n_S _ _ Hi)) => /= {Hfin}.
    by [].

  move: H_F0 (IH (proj2 Hle) (proj2 Hlt) Hfin0).

  move: (F0 (pos_div_2 eps)) (F (x2::s) (pos_div_2 eps))
    (real (Sup_fct (fun t : R => Rabs (f t - phi t)) x1 x2) * (x2 - x1))
    (Riemann_sum id (SF_seq_f2 (fun x4 y : R =>
      real (Sup_fct (fun t : R => Rabs (f t - phi t)) x4 y)) (x2 :: s))).
  move => F1 F2 l1 l2 Hl1 Hl2.
    split.
    move => _ [y [z [-> Hx]]].
    apply Rplus_le_compat.
    by apply Hl1, Hx.
    by apply Hl2, Hx.
    move => ub Hub.
    replace ub with ((ub-l2) + l2) by ring.
    apply Rplus_le_compat_r.
    apply Hl1 => y Hy.
    replace y with (l2 + (y - l2)) by ring.
    replace (ub-l2) with ((ub - y) + (y - l2)) by ring.
    apply Rplus_le_compat_r.
    apply Hl2 => z Hz.
    replace z with ((y+z) - y) by ring.
    apply Rplus_le_compat_r.
    apply Hub.
    exists y ; exists z ; by intuition.
  move: (Hfin O (lt_n_S _ _ (lt_O_Sn _))).
  rewrite /Sup_fct /=.
  move: (Rlt_not_eq _ _ (proj1 Hlt)).
  case: Req_EM_T => // Hx1 _.
  rewrite /Lub_Rbar ; case: ex_lub_Rbar ;
    case => [l | | ] [ub lub] ; simpl.
    split.
    move => _ [t [Ht ->]].
    apply Rmult_le_compat_r.
    apply -> Rminus_le_0 ; apply Hle.
    apply ub ; exists t ; split.
    by [].
    rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => // _ _ ;
    by intuition.
    move => b0 Hb0.
    move: (Rgt_minus _ _ (proj1 Hlt)) => H1.
    replace b0 with ((b0 / (x2 - x1)) * (x2 - x1)) by
      (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le.
    change (Rbar_le l (b0 / (x2 - x1))).
    apply lub => _ [t [-> Ht]].
    replace (Rabs (f t - phi t)) with ((Rabs (f t - phi t) * (x2 - x1)) / (x2 - x1))
      by (field ; by apply Rgt_not_eq).
    apply Rmult_le_compat_r.
    by apply Rlt_le, Rinv_0_lt_compat.
    apply Hb0 ; exists t.
    split.
    move: Ht ; rewrite /Rmin /Rmax ; case: Rle_dec (proj1 Hle) => //.
    by [].


  by [].
  by [].

    move => val ; split => Hval.
    case: Hval => g [Hnth [Hptd <-]] {val}.
    rewrite SF_cons_f2 /=.
    rewrite Riemann_sum_cons /=.
    exists (Rabs (f (g x1 x2) - phi (g x1 x2)) * (x2 - x1)).
    exists (Riemann_sum id
      (SF_seq_f2 (fun x y : R => Rabs (f (g x y) - phi (g x y))) (x2 :: s))).
    split.
    rewrite Rmult_comm.
    by [].
    split.
    exists (g x1 x2) ; split.
    case: (Hptd O) => /=.
    rewrite SF_size_f2 /= ; exact: lt_O_Sn.
    case => Hx1.
    case => Hx2.
    by split.
    contradict Hx2 ; apply (Hnth O 1%nat).
    simpl ; by intuition.
    simpl ; by intuition.
    contradict Hx1 ; apply sym_not_eq, (Hnth O O).
    simpl ; by intuition.
    simpl ; by intuition.

    by [].
    exists g.
    split.
    move => i j Hi Hj.
    apply (Hnth (S i) (S j)).
    simpl ; apply lt_n_S, Hi.
    simpl ; apply lt_n_S, Hj.
    split.
    move: Hptd => /=.
    rewrite SF_cons_f2 /=.
    apply ptd_cons.
    apply lt_O_Sn.
    split.
    exact: lt_O_Sn.

    case: Hval => /= y Hy.
    case: Hy => /= z [-> [F0y Fz]].
    case: F0y => t [Ht ->].
    case: Fz => g [Hnth [Hpdt <-]].
    set g0 := fun x y => match Req_EM_T x x1 with
      | left _ => match Req_EM_T y x2 with
        | left _ => t
        | right _ => g x y
      end
      | right _ => g x y
    end.
    exists g0.
    split.
    move => {val y z} i j Hi Hj.
    rewrite /g0.
    case: Req_EM_T => Hx1'.
    case: Req_EM_T => Hx2'.
    case: j Hj => /= [ | j] Hj.
    by apply Rgt_not_eq, Ht.
    apply lt_S_n in Hj ; case: j Hj => /= [ | j] Hj.
    by apply Rlt_not_eq, Ht.
    move: (proj2 Hle : sorted Rle (x2 :: s)).
    apply lt_S_n in Hj ; move: (proj2 Ht) ;
    elim: j x2 s Hj {IH Hle Hlt Hfin Hnth Hpdt F0 Ht g0 Hx2' Hx1' i Hi}
      => [ | i IH] x0 ; case => {x1} [ | x1 s] Hi Ht Hle ; simpl.
    by apply lt_irrefl in Hi.
    apply Rlt_not_eq, Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply lt_n_O in Hi.
    apply (IH x1).
    by apply lt_S_n, Hi.
    apply Rlt_le_trans with (1 := Ht).
    by apply Hle.
    by apply Hle.
    case: i j Hi Hj Hx1' Hx2' => /= [ | i] j Hi Hj Hx1' Hx2'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    rewrite /SF_sorted SF_lx_f2 // ; by apply lt_O_Sn.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 ; (try by apply lt_O_Sn) ; rewrite SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
    simpl in Hi ; apply lt_S_n in Hi ;
    case: i Hi Hx1' => /= [ | i] Hi Hx1'.
    by [].
    case: j Hj => /= [ | j] Hj.
    apply Rgt_not_eq, Rlt_le_trans with x2.
    apply Rlt_trans with t ; by intuition.
    apply Rle_trans with (nth 0 (x2 :: s) i).
    apply (sorted_incr (x2 :: s) O i).
    move: (ptd_sort _ Hpdt).
    by rewrite /SF_sorted SF_lx_f2 // ; apply lt_O_Sn.
    by intuition.
    simpl ; by intuition.
    move: (Hpdt i).
    rewrite SF_size_f2 SF_lx_f2 ; (try by apply lt_O_Sn) ; rewrite SF_ly_f2 (nth_pairmap 0) /=.
    move => H ; apply H.
    by intuition.
    apply SSR_leq ; by intuition.
    apply Hnth.
    by intuition.
    by intuition.
  split.
  move => ptd i Hi.
  rewrite SF_size_f2 /= in Hi.
  rewrite SF_lx_f2 ; (try by apply lt_O_Sn) ; rewrite SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  case: i Hi => /= [ | i] Hi ; rewrite /g0.
  move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  split ; apply Rlt_le ; by intuition.
  suff : (nth 0 (x2 :: s) i) <> x1.
  case: Req_EM_T => // _ _.
  move: (Hpdt i).
  rewrite SF_size_f2 SF_lx_f2 ; (try by apply lt_O_Sn) ; rewrite SF_ly_f2 nth_behead (nth_pairmap 0) /=.
  move => H ; apply H ; by intuition.
  apply SSR_leq ; by intuition.
  apply Rgt_not_eq, Rlt_le_trans with x2.
  apply Rlt_trans with t ; by intuition.
  apply (sorted_incr (x2 :: s) O i).
  move: (ptd_sort _ Hpdt).
  by rewrite /SF_sorted SF_lx_f2 // ; apply lt_O_Sn.
  by intuition.
  simpl ; by intuition.
  apply SSR_leq ; by intuition.
  rewrite SF_cons_f2 /=.
  rewrite Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (refl_equal x1) ; case: Req_EM_T => // _ _.
  move: (refl_equal x2) ; case: Req_EM_T => // _ _.
  apply Rmult_comm.
  case: s Hlt {Hpdt IH Hle Hfin F0 Ht Hnth}
    => [ | x3 s] Hlt /=.
  apply refl_equal.
  rewrite !(SF_cons_f2 _ _ (x3 :: _)) /=.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 /id ; move: (Rgt_not_eq _ _ (proj1 Hlt)) ;
  by case: Req_EM_T.
  elim: s (x2) x3 Hlt => [ | x4 s IH] x2' x3 Hlt.
  exact: refl_equal.
  rewrite !(SF_cons_f2 _ _ (x4 :: _)) /=.
  rewrite !Riemann_sum_cons /=.
  apply f_equal2.
  rewrite /g0 ; move: (Rgt_not_eq _ _ (Rlt_trans _ _ _ (proj1 Hlt) (proj1 (proj2 Hlt)))) ;
  by case: Req_EM_T.
  apply (IH x3).
  split.
  apply Rlt_trans with x2' ; apply Hlt.
  apply Hlt.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
  exact: lt_O_Sn.
Qed.

Lemma RInt_Reals (f : R -> R) (a b : R) :
  forall pr, RInt f a b = @RiemannInt f a b pr.
Proof.
intros pr.
apply is_RInt_unique.
apply ex_RInt_Reals_aux_1.
Qed.

(** ** Theorems proved using standard library *)

Lemma ex_RInt_norm :
  forall (f : R -> R) a b, ex_RInt f a b ->
  ex_RInt (fun x => norm (f x)) a b.
Proof.
intros f a b If.
apply ex_RInt_Reals_1.
apply RiemannInt_P16.
now apply ex_RInt_Reals_0.
Qed.

Lemma abs_RInt_le :
  forall (f : R -> R) a b,
  a <= b -> ex_RInt f a b ->
  Rabs (RInt f a b) <= RInt (fun t => Rabs (f t)) a b.
Proof.
intros f a b H1 If.
apply: (norm_RInt_le f (fun t : R => norm (f t)) a b).
exact H1.
move => x _ ; by apply Rle_refl.
exact: RInt_correct.
apply: RInt_correct.
exact: ex_RInt_norm.
Qed.
