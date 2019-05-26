(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond
#<br />#
Copyright (C) 2014 Xavier Onfroy

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)

Require Import Reals mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.seq.
Require Import Rcomplements Hierarchy SF_seq RInt.

(** This file describes the definition and properties of the
Henstock–Kurzweil (KH) integral. *)

Definition ith_step (ptd : @SF_seq R) i := nth 0 (SF_lx ptd) (S i) - nth 0 (SF_lx ptd) i.

Definition fine (delta : R -> posreal) ptd :=
  forall i : nat, (i < SF_size ptd)%nat -> ith_step ptd i < delta (nth 0 (SF_ly ptd) i).

Definition KH_filter (P : SF_seq -> Prop) :=
  exists delta, forall ptd, fine delta ptd -> P ptd.

Global Instance KH_filter_filter : Filter KH_filter.
Proof.
split.
exists (fun x => {| pos := 1; cond_pos := Rlt_0_1 |}).
intros ptd H.
easy.
intros P Q HP HQ.
destruct HP as (deltaP, HP).
destruct HQ as (deltaQ, HQ).
exists (fun x => {| pos := Rmin (deltaP x) (deltaQ x) ; cond_pos := (Rmin_stable_in_posreal (deltaP x) (deltaQ x))|}).
intros ptd Hptd.
split.
apply HP.
intros i Hi.
eapply Rlt_le_trans.
now apply (Hptd i).
apply Rmin_l.
apply HQ.
intros i Hi.
eapply Rlt_le_trans.
now apply (Hptd i).
apply Rmin_r.
intros P Q HPQ HP.
destruct HP as (delta, HP).
exists delta.
intros ptd Hptd.
apply HPQ ; now apply HP.
Qed.

Definition KH_fine (a b : R) :=
  within (fun ptd => pointed_subdiv ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b) KH_filter.

Lemma lub_cara :
  forall E l, is_lub E l -> forall e : posreal, ~ ~ (exists x, E x /\ l - e < x).
Proof.
intros E l H e.
intro H0.
assert (forall x, ~ (E x /\ l - e < x)) as H1.
intros x Hx.
apply H0 ; now exists x.
clear H0.
unfold is_lub in H.
destruct H as (H, H0).
assert ( ~ is_upper_bound E (l-e)) as H2.
intro H2.
apply H0 in H2.
assert (0 < e) as H3.
apply (cond_pos e).
assert (l > l - e) as H4.
apply tech_Rgt_minus.
assumption.
unfold Rgt in H4.
destruct H2 as [H2 | H2].
assert (l < l) as H5.
now apply Rlt_trans with (l-e).
apply Rlt_irrefl in H5 ; contradiction.
rewrite <- H2 in H4.
apply Rlt_irrefl in H4 ; contradiction.
unfold is_upper_bound in H2.
assert (forall x : R, E x -> x <= l-e) as H3.
clear H0 ; clear H.
intro x.
assert (~ (E x /\ l - e < x)) as H.
apply H1.
clear H1.
intro H0.
assert ({l-e<x}+{l-e=x}+{l-e>x}).
apply total_order_T.
destruct H1 as [H1 | H1].
destruct H1 as [H1 | H1].
assert (E x /\ l-e < x).
now split.
contradiction.
right ; rewrite H1 ; trivial.
now left.
contradiction.
Qed.

Lemma cousin :
  forall a b delta, ~ ~ exists ptd,
  pointed_subdiv ptd /\ fine delta ptd /\
  SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b.
Proof.
intros a b delta H.
assert (forall ptd, ~ (pointed_subdiv ptd /\ fine delta ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b)) as Hdelta.
intros ptd Hptd.
apply H ; now exists ptd.
clear H.
set (M := fun y => Rmin a b <= y <= Rmax a b /\ exists ptd, (pointed_subdiv ptd /\
        fine delta ptd /\ SF_h ptd = Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = y)).
assert (exists b', is_lub M b') as Hb'.
apply completeness_weak.
exists (Rmax a b).
intros y Hy.
apply Hy.
exists (Rmin a b).
split.
split.
apply Rle_refl.
apply Rmin_Rmax.
exists (SF_nil (Rmin a b)).
simpl.
split.
intros i Hi.
apply lt_n_0 in Hi ; destruct Hi.
split.
intros i Hi.
apply lt_n_0 in Hi ; destruct Hi.
split ; easy.
destruct Hb' as (b', H).
assert (forall e : posreal, ~ ~ (exists y, M y /\ b' - e < y)) as H1.
now apply lub_cara.
apply (H1 (delta b')).
intro H2.
destruct H2 as (y, H2).
clear H1.
destruct H2 as (H2, H1).
assert (M y) as Hy.
assumption.
destruct H2 as (H3, H2).
destruct H2 as (s, H2).
destruct H2 as (H2,H4).
destruct H4 as (H4, H0).
destruct H0 as (H5, H0).
set (s' := SF_rcons s (b',b')).
assert (pointed_subdiv s' /\ SF_h s' = Rmin a b /\ last (SF_h s') (SF_lx s') = b') as HH.
split.
unfold pointed_subdiv ; unfold s'.
intros i Hi.
rewrite SF_size_rcons in Hi.
apply lt_n_Sm_le in Hi.
case (eq_nat_dec i (SF_size s)) => His.
rewrite His.
replace (nth 0 (SF_lx (SF_rcons s (b', b'))) (SF_size s)) with (last (SF_h s) (SF_lx s)).
replace (nth 0 (SF_ly (SF_rcons s (b', b'))) (SF_size s)) with b'.
replace (nth 0 (SF_lx (SF_rcons s (b', b'))) (S (SF_size s))) with b'.
split.
rewrite H0.
unfold is_lub in H.
apply H.
apply Hy.
apply Rle_refl.
rewrite SF_lx_rcons.
simpl fst.
replace (S (SF_size s)) with (Peano.pred (size (rcons (SF_lx s) b')) ).
rewrite nth_last.
rewrite last_rcons.
easy.
rewrite size_rcons.
rewrite <- SF_size_lx.
simpl ; easy.
rewrite SF_ly_rcons.
simpl snd.
replace (SF_size s) with (Peano.pred (size (rcons (SF_ly s) b'))).
rewrite nth_last.
rewrite last_rcons.
easy.
rewrite size_rcons.
simpl.
apply SF_size_ly.
rewrite <- nth_last.
rewrite SF_size_lx.
simpl.
rewrite SF_lx_rcons.
simpl fst.
rewrite nth_rcons.
case Hleq : ssrnat.leq.
assert (Peano.pred(size (SF_lx s)) = size (SF_t s)) as Hlxsize.
rewrite SF_size_lx.
simpl ; unfold SF_size ; simpl ; easy.
unfold SF_size.
rewrite <- Hlxsize.
rewrite nth_last.
rewrite nth_last.
unfold SF_lx.
rewrite last_cons.
rewrite last_cons.
easy.
rewrite SF_size_lx in Hleq.
by rewrite ssrnat.leqnn in Hleq.
rewrite SF_lx_rcons.
rewrite SF_ly_rcons.
simpl fst.
simpl snd.
assert (i < SF_size s)%nat as Hsi.
apply le_lt_eq_dec in Hi.
now destruct Hi.
split ; rewrite nth_rcons ; case Hcase : ssrnat.leq ; rewrite nth_rcons ; case Hcase2 : ssrnat.leq.
now apply (H2 i).
case Hcase3 : eqtype.eq_op.
apply Rle_trans with (last (SF_h s) (SF_lx s)).
replace (last (SF_h s) (SF_lx s)) with (last 0 (SF_lx s)).
apply sorted_last.
apply ptd_sort.
apply H2.
rewrite SF_size_lx.
unfold lt.
apply le_n_S.
apply Hi.
case Hs : (SF_lx s).
assert (size (SF_lx s) = 0%nat) as Hss.
rewrite Hs ; simpl ; easy.
rewrite SF_size_lx in Hss.
apply MyNat.neq_succ_0 in Hss ; destruct Hss.
rewrite last_cons ; rewrite last_cons ; easy.
rewrite H0.
destruct H as (H, H').
now apply H.
move :Hcase2 => /ssrnat.leP Hcase2.
apply not_le in Hcase2 ; unfold gt in Hcase2.
rewrite SF_size_ly in Hcase2.
unfold lt in Hcase2.
apply le_S_n in Hcase2.
unfold lt in Hsi.
assert (S i <= i)%nat as Hcase4.
now apply le_trans with (SF_size s).
apply le_Sn_n in Hcase4 ; destruct Hcase4.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_lx in Hcase.
apply le_n_S in Hi.
contradiction.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_lx in Hcase.
apply le_n_S in Hi.
contradiction.
now apply (H2 i).
move :Hcase2 => /ssrnat.leP Hcase2.
rewrite SF_size_lx in Hcase2.
unfold lt in Hsi.
apply le_n_S in Hsi.
contradiction.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_ly in Hcase.
unfold lt in Hsi.
contradiction.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_ly in Hcase.
unfold lt in Hsi.
contradiction.
unfold s'.
split.
unfold SF_rcons.
simpl.
apply H5.
rewrite SF_lx_rcons.
rewrite last_rcons.
easy.
apply (Hdelta s').
split.
apply HH.
split.
unfold fine, s'.
rewrite SF_size_rcons.
unfold lt.
intros i Hi.
apply le_S_n in Hi.
case (le_lt_eq_dec i (SF_size s)).
assumption.
intro Hi2.
unfold ith_step.
replace (nth 0 (SF_lx (SF_rcons s (b', b'))) (S i)) with (nth 0 (SF_lx s) (S i)).
replace (nth 0 (SF_lx (SF_rcons s (b', b'))) i) with (nth 0 (SF_lx s) i).
replace (nth 0 (SF_ly (SF_rcons s (b', b'))) i) with (nth 0 (SF_ly s) i).
now apply (H4 i).
rewrite SF_ly_rcons.
simpl.
rewrite nth_rcons.
case Hcase : ssrnat.leq.
easy.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_ly in Hcase.
contradiction.
rewrite SF_lx_rcons.
rewrite nth_rcons.
case Hcase : ssrnat.leq.
easy.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_lx in Hcase.
apply le_n_S in Hi.
contradiction.
rewrite SF_lx_rcons.
rewrite nth_rcons.
case Hcase : ssrnat.leq.
easy.
move :Hcase => /ssrnat.leP Hcase.
rewrite SF_size_lx in Hcase.
apply le_n_S in Hi2.
contradiction.
clear Hi ; intro Hi.
rewrite Hi.
unfold ith_step.
rewrite SF_lx_rcons.
rewrite SF_ly_rcons.
replace (nth 0 (rcons (SF_lx s) (fst (b', b'))) (S (SF_size s))) with (last 0 (rcons (SF_lx s) (fst (b', b')))).
replace (nth 0 (rcons (SF_lx s) (fst (b', b'))) (SF_size s)) with y.
replace (nth 0 (rcons (SF_ly s) (snd (b', b'))) (SF_size s)) with (last 0 (rcons (SF_ly s) (snd (b', b')))).
rewrite last_rcons ; rewrite last_rcons ; simpl.
apply Rplus_lt_reg_l with y.
rewrite Rplus_comm.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
apply Rplus_lt_reg_l with (- delta b').
rewrite Rplus_comm.
replace (- delta b' + (y + delta b')) with y.
assumption.
rewrite Rplus_comm ; rewrite Rplus_assoc ; rewrite Rplus_opp_r ; rewrite Rplus_0_r ; easy.
replace (SF_size s) with (Peano.pred (size (rcons (SF_ly s) (snd (b', b'))))).
rewrite nth_last ; easy.
rewrite size_rcons.
simpl ; rewrite SF_size_ly ; easy.
rewrite nth_rcons.
rewrite SF_size_lx.
case Hcase : ssrnat.leq.
rewrite <- H0.
replace (SF_size s) with (Peano.pred (size (SF_lx s))).
rewrite nth_last.
case Hs : (SF_lx s).
assert (size (SF_lx s) = S (SF_size s)) as Hss.
apply SF_size_lx.
rewrite Hs in Hss.
unfold size in Hss.
apply O_S in Hss ; destruct Hss.
rewrite last_cons ; rewrite last_cons ; easy.
rewrite SF_size_lx ; simpl ; easy.
move :Hcase => /ssrnat.leP Hcase.
absurd (S (SF_size s) <= S (SF_size s))%nat.
assumption.
apply le_refl.
replace (S (SF_size s)) with (Peano.pred (size (rcons (SF_lx s) (fst (b', b'))))).
rewrite nth_last ; easy.
rewrite size_rcons ; rewrite SF_size_lx ; simpl ; easy.
destruct HH as (HH1, HH) ; split.
apply HH.
replace (Rmax a b) with b'.
apply HH.
assert ({b' < Rmax a b} + {b' = Rmax a b} + {b' > Rmax a b}) as Hb'.
apply total_order_T.
destruct Hb' as [Hb'1 | Hb'2].
destruct Hb'1 as [Hb'1 | Hb'3].
set (e:= Rmin ((Rmax a b) - b') ((delta b')/2) ).
assert (0 < e) as He.
apply Rmin_pos.
now apply Rlt_Rminus.
apply Rmult_lt_0_compat.
apply (cond_pos (delta b')).
apply Rinv_0_lt_compat.
apply (Rlt_R0_R2).
assert (e <= (delta b')/2) as Hed.
apply Rmin_r.
assert (e <= (Rmax a b) - b') as Hebb'.
apply Rmin_l.
assert (M (b' + e)) as H42.
unfold M.
split.
split.
apply Rle_trans with b'.
apply Rle_trans with y.
apply H3.
now apply H.
apply Rplus_le_reg_l with (- b').
rewrite Rplus_opp_l.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
now apply Rlt_le.
apply Rplus_le_reg_l with (- b').
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite Rplus_comm.
assumption.
exists (SF_rcons s' (b'+e, b')).
split.
unfold pointed_subdiv.
rewrite SF_size_rcons ; rewrite SF_lx_rcons ; rewrite SF_ly_rcons.
intros i Hi.
case (le_lt_eq_dec i (SF_size s')).
apply le_S_n ; apply Hi.
intro Hi2.
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) i) with (nth 0 (SF_lx s') i).
replace (nth 0 (rcons (SF_ly s') (snd (b' + e, b'))) i) with (nth 0 (SF_ly s') i).
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (S i)) with (nth 0 (SF_lx s') (S i)).
now apply (HH1 i).
rewrite nth_rcons.
rewrite SF_size_lx.
rewrite ssrnat.ltnS.
by move /ssrnat.ltP :Hi2 => ->.
rewrite nth_rcons.
rewrite SF_size_ly.
by move /ssrnat.ltP :Hi2 => ->.
rewrite nth_rcons.
rewrite SF_size_lx.
by move /ssrnat.ltP :Hi => ->.
intro Hi2.
rewrite Hi2.
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (SF_size s')) with b'.
replace (nth 0 (rcons (SF_ly s') (snd (b' + e, b'))) (SF_size s')) with (nth 0 (rcons (SF_ly s') (snd (b' + e, b'))) (Peano.pred (size (rcons (SF_ly s') (snd (b' + e, b')))))).
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (S (SF_size s'))) with (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (Peano.pred (size (rcons (SF_lx s') (fst (b' + e, b')))))).
rewrite nth_last.
rewrite nth_last.
rewrite last_rcons.
rewrite last_rcons.
simpl.
split.
apply Rle_refl.
rewrite <- (Rplus_0_r b') at 1.
apply Rplus_le_compat_l.
now apply Rlt_le.
rewrite size_rcons ; rewrite SF_size_lx ; simpl ; easy.
rewrite size_rcons ; rewrite SF_size_ly ; simpl ; easy.
rewrite nth_rcons.
rewrite SF_size_lx.
rewrite ssrnat.leqnn.
unfold s'.
rewrite SF_lx_rcons ; rewrite SF_size_rcons.
rewrite -SF_size_lx.
rewrite nth_rcons.
rewrite ssrnat.ltnn.
by rewrite eqtype.eq_refl.
split.
intro i.
rewrite SF_size_rcons.
intro Hi.
case (le_lt_eq_dec i (SF_size s')).
apply le_S_n.
apply Hi.
intro Hi2.
replace (ith_step (SF_rcons s' (b' + e, b')) i) with (ith_step s' i).
replace (nth 0 (SF_ly (SF_rcons s' (b' + e, b'))) i) with (nth 0 (SF_ly s') i).
unfold s'.
case (le_lt_eq_dec i (SF_size s)).
unfold s' in Hi2 ; rewrite SF_size_rcons in Hi2.
now apply le_S_n.
intro Hi3.
replace (ith_step (SF_rcons s (b', b')) i) with (ith_step s i).
replace (nth 0 (SF_ly (SF_rcons s (b', b'))) i) with (nth 0 (SF_ly s) i).
now apply (H4 i).
rewrite SF_ly_rcons ; rewrite nth_rcons.
rewrite SF_size_ly.
by move /ssrnat.ltP :Hi3 => ->.
unfold ith_step.
rewrite SF_lx_rcons.
rewrite 2!nth_rcons.
rewrite SF_size_lx.
rewrite ssrnat.ltnS.
move /ssrnat.ltP :(Hi3) => ->.
rewrite ssrnat.ltnS.
apply lt_le_weak in Hi3.
by move /ssrnat.leP :Hi3 => ->.
intro Hi3.
rewrite Hi3.
unfold ith_step.
rewrite SF_lx_rcons.
replace (nth 0 (rcons (SF_lx s) (fst (b', b'))) (S (SF_size s))) with b'.
replace (nth 0 (rcons (SF_lx s) (fst (b', b'))) (SF_size s)) with y.
replace (nth 0 (SF_ly (SF_rcons s (b', b'))) (SF_size s)) with b'.
apply Rplus_lt_reg_l with (y - delta b').
replace (y - delta b' + (b' - y)) with (b' - delta b') by ring.
now replace (y - delta b' + delta b') with y by ring.
rewrite SF_ly_rcons.
replace (SF_size s) with (Peano.pred (size (rcons (SF_ly s) (snd (b', b'))))).
rewrite nth_last.
rewrite last_rcons.
easy.
rewrite size_rcons.
simpl.
apply SF_size_ly.
rewrite nth_rcons.
rewrite <- H0.
rewrite <- nth_last.
rewrite SF_size_lx.
rewrite ssrnat.leqnn.
simpl.
apply set_nth_default.
rewrite SF_size_lx.
apply ssrnat.leqnn.
replace (S (SF_size s)) with (Peano.pred (size (rcons (SF_lx s) (fst (b', b'))))).
rewrite nth_last.
rewrite last_rcons.
easy.
rewrite size_rcons ; rewrite SF_size_lx ; simpl ; easy.
unfold s'.
rewrite SF_ly_rcons.
rewrite SF_ly_rcons.
rewrite SF_ly_rcons.
case (le_lt_eq_dec i (SF_size s)).
unfold s' in Hi2 ; rewrite SF_size_rcons in Hi2 ; apply le_S_n ; apply Hi2.
intro Hi3.
rewrite nth_rcons ; rewrite nth_rcons ; rewrite nth_rcons.
rewrite SF_size_ly.
move /ssrnat.ltP :(Hi3) => ->.
rewrite size_rcons.
rewrite ssrnat.ltnS.
rewrite SF_size_ly.
apply lt_le_weak in Hi3.
by move /ssrnat.leP :Hi3 => ->.
intro Hi3 ; rewrite Hi3.
replace (nth 0 (rcons (SF_ly s) (snd (b', b'))) (SF_size s)) with b'.
rewrite nth_rcons.
rewrite size_rcons.
rewrite SF_size_ly.
rewrite ssrnat.leqnn.
replace (SF_size s) with (Peano.pred (size (rcons (SF_ly s) (snd (b', b'))))).
rewrite nth_last.
rewrite last_rcons ; easy.
rewrite size_rcons ; rewrite SF_size_ly ; simpl ; easy.
rewrite nth_rcons.
rewrite SF_size_ly.
rewrite ssrnat.ltnn.
by rewrite eqtype.eq_refl.
unfold ith_step.
rewrite SF_lx_rcons.
rewrite nth_rcons ; rewrite nth_rcons.
rewrite SF_size_lx.
rewrite ssrnat.ltnS.
move /ssrnat.ltP :(Hi2) => ->.
rewrite ssrnat.ltnS.
apply lt_le_weak in Hi2.
by move /ssrnat.leP :Hi2 => ->.
intro Hi2 ; rewrite Hi2.
unfold ith_step.
rewrite SF_lx_rcons.
rewrite SF_ly_rcons.
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (S (SF_size s'))) with (b' + e).
replace (nth 0 (rcons (SF_lx s') (fst (b' + e, b'))) (SF_size s')) with b'.
replace (nth 0 (rcons (SF_ly s') (snd (b' + e, b'))) (SF_size s')) with b'.
rewrite Rplus_comm.
unfold Rminus.
rewrite Rplus_assoc ; rewrite Rplus_opp_r ; rewrite Rplus_0_r.
apply Rle_lt_trans with (delta b' / 2).
assumption.
apply Rminus_lt_0 ; field_simplify ; rewrite Rdiv_1.
by apply is_pos_div_2.
replace (SF_size s') with (Peano.pred (size (rcons (SF_ly s') (snd (b' + e, b'))))).
rewrite nth_last.
rewrite last_rcons.
easy.
rewrite size_rcons ; rewrite SF_size_ly ; simpl ; easy.
rewrite nth_rcons.
rewrite SF_size_lx.
rewrite ssrnat.leqnn.
replace (SF_size s') with (Peano.pred (size (SF_lx s'))).
rewrite nth_last.
destruct HH as (HH, HH') ; rewrite <- HH'.
case Hcase2 : (SF_lx s').
assert (size (SF_lx s') = S (SF_size s')) as Hss.
apply SF_size_lx.
rewrite Hcase2 in Hss.
apply O_S in Hss ; destruct Hss.
rewrite last_cons ; rewrite last_cons ; easy.
rewrite SF_size_lx ; simpl ; easy.
replace (S (SF_size s')) with (Peano.pred (size (rcons (SF_lx s') (fst (b' + e, b'))))).
rewrite nth_last ; rewrite last_rcons ; easy.
rewrite size_rcons ; rewrite SF_size_lx ; simpl ; easy.
rewrite SF_lx_rcons ; rewrite last_rcons.
split.
unfold SF_rcons ; simpl.
apply H5.
easy.
apply H in H42.
assert (b' < b' + e) as H43.
rewrite <- (Rplus_0_r b') at 1.
now apply Rplus_lt_compat_l.
apply Rle_not_lt in H42.
contradiction.
apply Hb'3.
assert (b' <= Rmax a b) as Hb'3.
apply H.
intros x Hx.
apply Hx.
apply Rle_not_gt in Hb'3.
contradiction.
Qed.

Global Instance KH_fine_proper_filter a b : ProperFilter' (KH_fine a b).
Proof.
constructor.
unfold KH_fine ; unfold within ; unfold KH_filter.
intro H.
destruct H as (delta, Hdelta).
apply (cousin a b delta).
intro H.
destruct H as (ptd, Hptd).
apply (Hdelta ptd).
apply Hptd.
split.
apply Hptd.
split ; apply Hptd.
unfold KH_fine.
apply within_filter.
apply KH_filter_filter.
Qed.

Section is_KHInt.

Context {V : NormedModule R_AbsRing}.

Definition is_KHInt (f : R -> V) (a b : R) (If : V) :=
  filterlim (fun ptd => scal (sign (b-a)) (Riemann_sum f ptd)) (KH_fine a b) (locally If).

Definition ex_KHInt f a b :=
  exists If : V, is_KHInt f a b If.

Lemma is_KHInt_point :
  forall (f : R -> V) (a : R),
  is_KHInt f a a zero.
Proof.
intros f a.
unfold is_KHInt.
apply filterlim_ext with (fun ptd : @SF_seq R => @zero V).
intro ptd.
rewrite Rminus_eq_0 sign_0.
rewrite scal_zero_l ; easy.
intros P HP.
unfold filtermap.
destruct HP as (eps, HPeps).
exists (fun x : R => {| pos := 1 ; cond_pos := Rlt_0_1 |}).
intros ptd Hptd Hptd2.
apply HPeps.
apply ball_center.
Qed.

Lemma ex_KHInt_point :
  forall (f : R -> V) (a : R),
  ex_KHInt f a a.
Proof.
intros f a ; exists zero ; now apply is_KHInt_point.
Qed.

Lemma is_KHInt_const :
  forall (a b : R) (c : V),
  is_KHInt (fun x : R => c) a b (scal (b-a) c).
Proof.
intros a b c.
intros P HP.
destruct HP as (eps, HPeps).
exists (fun x : R => eps).
intros ptd Hptd Hptd2.
apply HPeps.
rewrite Riemann_sum_const.
destruct Hptd2 as (Hptd0, Hptd1).
destruct Hptd1 as (Hptd1, Hptd2).
rewrite Hptd2.
rewrite Hptd1.
rewrite scal_assoc.
replace (mult (sign (b - a)) (Rmax a b - Rmin a b)) with (b-a).
apply ball_center.
apply sym_eq, sign_min_max.
Qed.

Lemma ex_KHInt_const :
  forall (a b : R) (c : V),
  ex_KHInt (fun x : R => c) a b.
Proof.
intros a b c ; exists (scal (b-a) c) ; apply is_KHInt_const.
Qed.

End is_KHInt.

Section KHInt.

Context {V : CompleteNormedModule R_AbsRing}.

Definition KHInt (f : R -> V) (a b : R) :=
  iota (is_KHInt f a b).

Lemma KHInt_correct :
  forall (f : R -> V) (a b : R),
  ex_KHInt f a b -> is_KHInt f a b (KHInt f a b).
Proof.
intros f a b [v Hv].
unfold KHInt.
apply iota_correct.
exists v.
split.
exact Hv.
intros w Hw.
apply filterlim_locally_unique with (1 := Hv) (2 := Hw).
Qed.

Lemma is_KHInt_unique :
  forall (f : R -> V) (a b : R) (l : V),
  is_KHInt f a b l -> KHInt f a b = l.
Proof.
intros f a b l H.
apply filterlim_locally_unique with (2 := H).
apply KHInt_correct.
now exists l.
Qed.

Lemma KHInt_point :
  forall (f : R -> V) (a : R),
  KHInt f a a = zero.
Proof.
intros f a.
apply is_KHInt_unique.
apply: is_KHInt_point.
Qed.

Lemma KHInt_const :
  forall (a b : R) (v : V),
  KHInt (fun _ => v) a b = scal (b - a) v.
Proof.
intros a b v.
apply is_KHInt_unique.
apply: is_KHInt_const.
Qed.

Lemma is_RInt_KHInt :
  forall (f : R -> V) (a b : R) (l : V),
  is_RInt f a b l -> is_KHInt f a b l.
Proof.
intros f a b I.
unfold is_RInt, is_KHInt.
apply filterlim_filter_le_1.
unfold filter_le, Riemann_fine, KH_fine, within, KH_filter, locally_dist.
intros P [delta HPdelta].
exists (fun _ => delta).
intros ptd Hptd1 Hptd2.
apply HPdelta.
2: exact Hptd2.
clear -Hptd1 Hptd2.
unfold fine in Hptd1.
revert Hptd1 Hptd2.
assert ((forall i : nat, (i < SF_size ptd)%nat -> ith_step ptd i < delta) ->
pointed_subdiv ptd /\
SF_h ptd >= Rmin a b /\ last (SF_h ptd) (SF_lx ptd) = Rmax a b ->
seq_step (SF_lx ptd) < delta) as H0.
apply SF_cons_ind with (s := ptd) => {ptd} [x0 | h ptd IH] H.
intros H0.
apply cond_pos.
intro H0.
rewrite SF_lx_cons.
unfold seq_step ; simpl.
apply Rmax_case.
specialize (H 0%nat).
unfold ith_step in H.
rewrite SF_lx_cons in H.
simpl in H.
rewrite Rabs_right.
apply H.
rewrite SF_size_cons.
apply lt_0_Sn.
destruct H0 as (H0, H1).
unfold pointed_subdiv in H0.
apply Rge_minus.
apply Rle_ge.
specialize (H0 0%nat).
apply Rle_trans with (nth 0 (SF_ly (SF_cons h ptd)) 0) ; apply H0 ; rewrite SF_size_cons ; apply lt_0_Sn.
apply IH.
intros i Hi.
specialize (H (S i)).
unfold ith_step.
unfold ith_step in H.
change (nth 0 (SF_lx ptd) (S i)) with (nth 0 (SF_lx (SF_cons h ptd)) (S (S i))).
change (nth 0 (SF_lx ptd) i) with (nth 0 (SF_lx (SF_cons h ptd)) (S i)).
apply H.
rewrite SF_size_cons ; now apply lt_n_S.
split.
apply ptd_cons with h.
apply H0.
split.
apply Rge_trans with (SF_h (SF_cons h ptd)).
2:apply H0.
2:apply H0.
apply Rle_ge.
destruct H0 as (H0, H1).
unfold pointed_subdiv in H0.
specialize (H0 0%nat).
change (SF_h (SF_cons h ptd)) with (nth 0 (SF_lx (SF_cons h ptd)) 0).
change (SF_h ptd) with (nth 0 (SF_lx (SF_cons h ptd)) 1).
apply Rle_trans with (nth 0 (SF_ly (SF_cons h ptd)) 0) ; apply H0 ; rewrite SF_size_cons ; apply lt_0_Sn.
intros H1 H2.
apply H0.
apply H1.
split.
apply H2.
split.
destruct H2 as (H2, (H3, H4)).
rewrite H3.
apply Rge_refl.
apply H2.
Qed.

End KHInt.
