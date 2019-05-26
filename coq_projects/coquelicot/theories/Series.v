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
Require Import Rcomplements.
Require Import Lim_seq Rbar Hierarchy.

(** This file gives definitions and properties about series defined on
a normed module. An equivalence with the standard library and several
convergence criteria are provided. *)

Section Definitions.

(** * Definitions *)

Context {K : AbsRing} {V : NormedModule K}.

Definition is_series (a : nat -> V) (l : V) :=
   filterlim (sum_n a) (eventually) (locally l).

Definition ex_series (a : nat -> V) :=
   exists l : V, is_series a l.

Definition Cauchy_series (a : nat -> V) :=
  forall eps : posreal,
    exists N : nat, forall n m : nat,
      (N <= n)%nat -> (N <= m)%nat ->
      norm (sum_n_m a n m) < eps.

End Definitions.

Definition Series (a : nat -> R) : R :=
   real (Lim_seq (sum_n a)).

Lemma ex_series_dec (a : nat -> R) :
  {ex_series a} + {~ ex_series a}.
Proof.
  case: (ex_lim_seq_dec (sum_n a)) => H.
  apply Lim_seq_correct in H.
  case: (Lim_seq (sum_n a)) H => [l | | ] H.
  left ; by exists l.
  right ; case => l H0.
  absurd (p_infty = Finite l) => //.
  rewrite -(is_lim_seq_unique _ _ H).
  by apply is_lim_seq_unique.
  right ; case => l H0.
  absurd (m_infty = Finite l) => //.
  rewrite -(is_lim_seq_unique _ _ H).
  by apply is_lim_seq_unique.
  right ; case => l.
  contradict H.
  by exists l.
Qed.

Lemma is_series_unique (a : nat -> R) (l : R) :
  is_series a l -> Series a = l.
Proof.
  move => Ha.
  replace l with (real (Finite l)) by auto.
  apply (f_equal real).
  by apply is_lim_seq_unique.
Qed.
Lemma Series_correct (a : nat -> R) :
  ex_series a -> is_series a (Series a).
Proof.
  case => l Ha.
  by rewrite (is_series_unique a l).
Qed.

Lemma is_series_Reals (a : nat -> R) (l : R) :
  is_series a l <-> infinite_sum a l.
Proof.
  split => H.
  apply (is_lim_seq_spec _ l) in H.
  move => e He ; set eps := mkposreal e He.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  rewrite <- sum_n_Reals.
  by apply (H n Hn).
  apply (is_lim_seq_spec _ l).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  rewrite sum_n_Reals.
  by apply (H n Hn).
Qed.

Lemma ex_series_Reals_0 (a : nat -> R) :
  ex_series a -> { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l }.
Proof.
  move => H ;
  exists (Series a) ; case: H => l H.
  replace (Series a) with l.
  move => e He ; set eps := mkposreal e He.
  apply (is_lim_seq_spec _ l) in H.
  case: (H eps) => /= {H} N H.
  exists N => n Hn.
  rewrite <- sum_n_Reals.
  by apply (H n Hn).
  apply sym_eq.
  rewrite /Series.
  replace l with (real (Finite l)) by auto.
  apply f_equal.
  by apply is_lim_seq_unique.
Qed.

Lemma ex_series_Reals_1 (a : nat -> R) :
  { l:R | Un_cv (fun N:nat => sum_f_R0 a N) l } -> ex_series a.
Proof.
  case => l H.
  exists l.
  apply (is_lim_seq_spec _ l).
  move => eps.
  case: (H eps (cond_pos eps)) => {H} N H.
  exists N => n Hn.
  rewrite sum_n_Reals.
  by apply (H n Hn).
Qed.

(** Cauchy *)

Lemma Cauchy_ex_series {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) :
  ex_series a -> Cauchy_series a.
Proof.
intros [l Hl] eps.
set (eps' := eps / (norm_factor (V := V))).
assert (He: 0 < eps').
  apply Rdiv_lt_0_compat.
  apply eps.
  apply norm_factor_gt_0.
destruct (proj2 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n (fun k => a k)))
  (ex_intro _ l Hl) (mkposreal _ He)) as [P [[N HN] HP]].
exists (S N).
intros [|u] v Hu Hv.
elim le_Sn_O with (1 := Hu).
destruct (le_or_lt u v) as [Huv|Huv].
rewrite -> sum_n_m_sum_n with (1 := Huv).
replace (pos eps) with (norm_factor (V := V) * mkposreal _ He).
apply norm_compat2.
apply HP ; apply HN.
now apply le_S_n.
now apply le_Sn_le.
rewrite /eps' /=.
field.
apply Rgt_not_eq, norm_factor_gt_0.
rewrite sum_n_m_zero.
rewrite norm_zero.
apply cond_pos.
now apply lt_S.
Qed.

Lemma ex_series_Cauchy {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) :
  Cauchy_series a -> ex_series a.
Proof.
intros Ca.
destruct (proj1 (filterlim_locally_cauchy (U := V) (F := eventually) (sum_n a))) as [l Hl].
2: now exists l.
intros eps.
destruct (Ca eps) as [N HN].
exists (le N).
split.
now exists N.
intros u v.
wlog Huv: u v / (u <= v)%nat.
intros H.
destruct (le_or_lt u v) as [Huv|Huv].
now apply H.
intros Hu Hv.
apply ball_sym.
apply H => //.
now apply lt_le_weak.
intros Hu Hv.
apply: norm_compat1.
rewrite <- sum_n_m_sum_n with (1 := Huv).
apply HN => //.
now apply le_S.
Qed.

Section Properties1.

Context {K : AbsRing} {V : NormedModule K}.

(** Extensionality *)

Lemma is_series_ext (a b : nat -> V) (l : V) :
  (forall n, a n = b n) -> (is_series a l)
    -> is_series b l.
Proof.
  move => Heq.
  apply filterlim_ext.
  intros x; now apply sum_n_m_ext.
Qed.
Lemma ex_series_ext (a b : nat -> V) :
  (forall n, a n = b n) -> ex_series a
    -> ex_series b.
Proof.
  move => Heq [l Ha].
  exists l ; by apply is_series_ext with a.
Qed.
Lemma Series_ext (a b : nat -> R) :
  (forall n, a n = b n) -> Series a = Series b.
Proof.
  move => Heq.
  apply (f_equal real).
  apply Lim_seq_ext.
  intros n; now apply sum_n_m_ext.
Qed.

(** Index offset *)

Lemma is_series_incr_1 (a : nat -> V) (l : V) :
  is_series a (plus l  (a O))
    -> is_series (fun k => a (S k)%nat) l.
Proof.
  intros H.
  apply filterlim_ext with (fun k => plus (sum_n a (S k)) (opp (a 0%nat))).
  induction x; simpl.
  rewrite sum_Sn !sum_O (plus_comm _ (a 1%nat)); rewrite <- plus_assoc.
  now rewrite plus_opp_r plus_zero_r.
  rewrite !sum_Sn -IHx -!sum_Sn sum_Sn; simpl.
  rewrite <- plus_assoc, <- (plus_assoc _ _ (a (S (S x)))).
  apply f_equal; apply plus_comm.
  apply filterlim_comp with (G:=(locally (plus l (a 0%nat)))) (g:=fun x => plus x (opp (a 0%nat))).
  (* . *)
  apply filterlim_comp with (f:= fun x => S x) (2:=H).
  apply eventually_subseq; intros n; omega.
  (* . *)
  pattern l at 2; replace l with (plus (plus l (a 0%nat)) (opp (a 0%nat))).
  apply filterlim_comp_2 with (3 := filterlim_plus _ _).
  apply filterlim_id.
  apply filterlim_const.
  rewrite <- plus_assoc, plus_opp_r.
  apply plus_zero_r.
Qed.

Lemma is_series_incr_n (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series a (plus l (sum_n a (pred n)))
    -> is_series (fun k => a (n + k)%nat) l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n l Ha => [ | n IH] l Ha.
  rewrite sum_O in Ha.
  by apply is_series_incr_1.
  apply is_series_ext with (fun k : nat => a (S (n + S k))).
  move => k ; apply f_equal ; ring.
  apply (is_series_incr_1 (fun k : nat => a (S (n + k))) l).
  rewrite plus_0_r.
  apply IH.
  replace (plus (plus l (a (S n))) (sum_n a n)) with (plus l (sum_n a (S n))).
  assumption.
  rewrite <- plus_assoc, sum_Sn; apply f_equal; simpl; apply plus_comm.
Qed.

Lemma is_series_decr_1 (a : nat -> V) (l : V) :
  is_series (fun k => a (S k)%nat) (plus l (opp (a O))) -> is_series a l.
Proof.
  intros H.
  apply filterlim_ext_loc with (fun v => plus (a 0%nat) (sum_n (fun k : nat => a (S k)) (pred v))).
  exists 1%nat.
  intros n Hn; apply sym_eq.
  rewrite /sum_n sum_Sn_m.
  apply f_equal.
  rewrite sum_n_m_S.
  apply f_equal ; omega.
  by apply le_O_n.
  replace l with (plus (a 0%nat) (plus l (opp (a 0%nat)))).
  apply filterlim_comp_2 with (3 := filterlim_plus _ _).
  apply filterlim_id.
  apply filterlim_const.
  apply filterlim_comp with (f:= fun x => pred x) (2:=H).
  intros P (N1,HN1).
  exists (S N1).
  intros n Hn; apply HN1; omega.
  rewrite plus_comm; rewrite <- plus_assoc.
  rewrite (plus_comm _ (a 0%nat)); rewrite plus_opp_r.
  apply plus_zero_r.
Qed.


Lemma is_series_decr_n (a : nat -> V) (n : nat) (l : V) :
  (0 < n)%nat -> is_series (fun k => a (n + k)%nat) (plus l (opp (sum_n a (pred n))))
    -> is_series a l.
Proof.
  case: n => /= [ | n] Hn Ha.
  by apply lt_irrefl in Hn.
  clear Hn.
  elim: n a l Ha => [ | n IH] a l Ha.
  rewrite sum_O in Ha.
  by apply is_series_decr_1.
  apply is_series_decr_1.
  apply IH.
  replace (plus (plus l (opp (a 0%nat))) (opp (sum_n (fun k : nat => a (S k)) n)))
    with (plus l (opp (sum_n a (S n)))).
  by apply Ha.
  rewrite /sum_n sum_n_m_S sum_Sn_m /=.
  rewrite <- plus_assoc.
  apply f_equal.
  now rewrite opp_plus.
  by apply le_O_n.
Qed.

Lemma ex_series_incr_1 (a : nat -> V) :
  ex_series a <-> ex_series (fun k => a (S k)%nat).
Proof.
  split ; move => [la Ha].
  exists (plus la  (opp (a O))).
  apply is_series_incr_1.
  now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
  exists (plus la (a O)).
  apply is_series_decr_1.
  now rewrite <- plus_assoc, plus_opp_r, plus_zero_r.
Qed.

Lemma ex_series_incr_n (a : nat -> V) (n : nat) :
  ex_series a <-> ex_series (fun k => a (n + k)%nat).
Proof.
  case: n => [ | n].
  split ; apply ex_series_ext ; by intuition.
  split ; move => [la Ha].
  exists (plus la (opp (sum_n a (pred (S n))))).
  apply is_series_incr_n.
  by apply lt_O_Sn.
  now rewrite <- plus_assoc, plus_opp_l, plus_zero_r.
  exists (plus la (sum_n a (pred (S n)))).
  apply is_series_decr_n with (S n).
  by apply lt_O_Sn.
  now rewrite <- plus_assoc, plus_opp_r, plus_zero_r.
Qed.

End Properties1.

Lemma Series_incr_1 (a : nat -> R) :
  ex_series a -> Series a = a O + Series (fun k => a (S k)).
Proof.
  move => Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_1.
  rewrite /plus /opp /=.
  ring_simplify (Series (fun k : nat => a (S k)) + a 0%nat +- a 0%nat).
  apply Series_correct.
  by apply (ex_series_incr_1 a).
Qed.

Lemma Series_incr_n (a : nat -> R) (n : nat) :
  (0 < n)%nat -> ex_series a
    -> Series a = sum_f_R0 a (pred n)  + Series (fun k => a (n + k)%nat).
Proof.
  move => Hn Ha.
  apply is_series_unique.
  rewrite Rplus_comm.
  apply is_series_decr_n with n.
  by [].
  rewrite /plus /opp /= sum_n_Reals.
  ring_simplify (Series (fun k : nat => a (n+ k)%nat) + sum_f_R0 a (pred n) + - sum_f_R0 a (pred n)).
  apply Series_correct.
  by apply ex_series_incr_n.
Qed.

Lemma Series_incr_1_aux (a : nat -> R) :
  a O = 0 -> Series a = Series (fun k => a (S k)).
Proof.
  move => Ha.
  rewrite /Series.
  rewrite -Lim_seq_incr_1.
  apply f_equal, Lim_seq_ext => n.
  rewrite /sum_n sum_n_m_S sum_Sn_m.
  rewrite Ha ; by apply Rplus_0_l.
  by apply le_O_n.
Qed.
Lemma Series_incr_n_aux (a : nat -> R) (n : nat) :
   (forall k, (k < n)%nat -> a k = 0)
     -> Series a = Series (fun k => a (n + k)%nat).
Proof.
  elim: n => [ | n IH] Ha.
  by apply Series_ext => k.
  rewrite IH.
  rewrite Series_incr_1_aux.
  apply Series_ext => k.
  apply f_equal ; ring.
  intuition.
  move => k Hk ; intuition.
Qed.

(** * Convergence theorems *)

Lemma Cauchy_series_Reals (a : nat -> R) :
  Cauchy_series a <-> Cauchy_crit_series a.
Proof.
  split => Hcv.
  apply cv_cauchy_1, ex_series_Reals_0.
  by apply: ex_series_Cauchy.
  apply: Cauchy_ex_series.
  apply ex_series_Reals_1.
  apply cv_cauchy_2.
  by apply Hcv.
Qed.

Lemma ex_series_lim_0 (a : nat -> R) :
  ex_series a -> is_lim_seq a 0.
Proof.
  intros Hs.
  apply is_lim_seq_spec.
  intros eps.
  apply (Cauchy_ex_series (V := R_CompleteNormedModule)) in Hs.
  case: (Hs eps) => {Hs} N Hs.
  exists (S N) ; case => [ | n] Hn.
  by apply le_Sn_0 in Hn.
  apply le_S_n in Hn.
  replace (a (S n) - 0)
    with (sum_n_m a (S n) (S n)).
  apply Hs ; by intuition.
  by rewrite sum_n_n Rminus_0_r.
Qed.

Lemma ex_series_Rabs (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) -> ex_series a.
Proof.
  move => H.
  apply: ex_series_Cauchy.
  apply Cauchy_series_Reals.
  apply cauchy_abs.
  apply Cauchy_series_Reals.
  by apply: Cauchy_ex_series.
Qed.

Lemma Series_Rabs (a : nat -> R) :
  ex_series (fun n => Rabs (a n)) ->
    Rabs (Series a) <= Series (fun n => Rabs (a n)).
Proof.
  move => Hra.
  have Ha := (ex_series_Rabs a Hra).
  case: Hra => lra Hra.
  case: Ha => la Ha.
  rewrite /is_series in Hra Ha.
  rewrite /Series /=.
  replace (Lim_seq (sum_n a)) with (Finite la).
  replace (Lim_seq (sum_n (fun k : nat => Rabs (a k)))) with (Finite lra).
  simpl.
  apply (is_lim_seq_abs _ la) in Ha.
  change (Rbar_le (Rabs la) lra).
  eapply is_lim_seq_le with (2:=Ha).
  2: apply Hra.
  elim => [ | n IH] /=.
  rewrite !sum_O.
  by apply Rle_refl.
  rewrite !sum_Sn.
  apply Rle_trans with (1 := Rabs_triang _ _).
  apply Rplus_le_compat_r.
  by apply IH.
  by apply sym_eq, is_lim_seq_unique.
  by apply sym_eq, is_lim_seq_unique.
Qed.

(** Comparison *)

Lemma ex_series_le {K : AbsRing} {V : CompleteNormedModule K}
  (a : nat -> V) (b : nat -> R) :
   (forall n : nat, norm (a n) <= b n) ->
   ex_series b -> ex_series a.
Proof.
  move => H Hb.
  apply (Cauchy_ex_series (V := R_CompleteNormedModule)) in Hb.
  apply ex_series_Cauchy.
  move => e.
  case (Hb e) => {Hb} N Hb.
  exists N => n m Hn Hm.
  eapply Rle_lt_trans, (Hb _ _ Hn Hm) => //.
  eapply Rle_trans.
  apply norm_sum_n_m.
  apply Rle_trans with (sum_n_m b n m).
  by apply sum_n_m_le.
  right.
  assert (forall n, 0 <= b n).
    intros k.
    eapply Rle_trans, H.
    by apply norm_ge_0.
  clear -H0.
  apply sym_eq, Rabs_pos_eq.
  elim: n m b H0 => /= [ | n IH] m b Hb.
  elim: m => /= [ | m IH].
  rewrite sum_n_n.
  by apply Hb.
  rewrite sum_n_Sm.
  by apply Rplus_le_le_0_compat.
  by apply le_O_n.
  case: m => /= [ | m].
  by apply Rle_refl.
  rewrite -sum_n_m_S.
  apply IH => k.
  by apply Hb.
Qed.

Lemma Series_le (a b : nat -> R) :
  (forall n : nat, 0 <= a n <= b n) ->
   ex_series b -> Series a <= Series b.
Proof.
  move => Hn Hb.
  have Ha := (ex_series_le a b).
  apply Lim_seq_correct' in Ha.
  apply Lim_seq_correct' in Hb.
  move: Ha Hb ; apply is_lim_seq_le.
  elim => [ | n IH] /=.
  rewrite !sum_O.
  by apply Hn.
  rewrite !sum_Sn.
  apply Rplus_le_compat.
  by apply IH.
  by apply Hn.
  intros n.
  rewrite /norm /= /abs /= Rabs_pos_eq ; by apply Hn.
  by apply Hb.
Qed.


(** * Operations *)

(** Additive operators *)

Section Properties2.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_series_opp (a : nat -> V) (la : V) :
  is_series a la
    -> is_series (fun n => opp (a n)) (opp la).
Proof.
  move => Ha.
   apply filterlim_ext with (fun n => opp (sum_n a n)).
  elim => [ | n IH].
  rewrite !sum_O ; easy.
  rewrite !sum_Sn -IH.
  apply opp_plus.
  apply filterlim_comp with (1:=Ha).
  apply filterlim_opp.
Qed.

Lemma ex_series_opp (a : nat -> V) :
  ex_series a
    -> ex_series (fun n => opp (a n)).
Proof.
  move => [la Ha].
  exists (opp la).
  by apply is_series_opp.
Qed.
Lemma Series_opp (a : nat -> R) :
  Series (fun n => - a n) = - Series a.
Proof.
  rewrite /Series
    (Lim_seq_ext (sum_n (fun k : nat => - a k)) (fun n => - (sum_n (fun k => a k) n))).
  rewrite Lim_seq_opp.
  by rewrite Rbar_opp_real.
  elim => [ | n IH].
  rewrite !sum_O ; ring.
  rewrite !sum_Sn IH /plus /=.
  ring.
Qed.

Lemma is_series_plus (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n)  (b n)) (plus la  lb).
Proof.
  move => Ha Hb.
  apply filterlim_ext with (fun n => plus (sum_n a n) (sum_n b n)).
  elim => [ | n IH]; simpl.
  by rewrite !sum_O.
  rewrite !sum_Sn -IH; rewrite <- 2!plus_assoc; apply f_equal.
  rewrite 2!plus_assoc; apply f_equal2; try easy.
  apply plus_comm.
  now apply filterlim_comp_2 with (3 := filterlim_plus _ _).
Qed.
Lemma ex_series_plus (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (b n)).
Proof.
  move => [la Ha] [lb Hb].
  exists (plus la lb).
  by apply is_series_plus.
Qed.

Lemma is_series_minus (a b : nat -> V) (la lb : V) :
  is_series a la -> is_series b lb
    -> is_series (fun n => plus (a n) (opp (b n))) (plus la (opp lb)).
Proof.
  move => Ha Hb.
  apply is_series_plus => //.
  apply is_series_opp => //.
Qed.
Lemma ex_series_minus (a b : nat -> V) :
  ex_series a -> ex_series b
    -> ex_series (fun n => plus (a n) (opp (b n))).
Proof.
  move => Ha Hb.
  apply ex_series_plus => //.
  apply ex_series_opp => //.
Qed.

End Properties2.

Lemma Series_plus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n + b n) = Series a + Series b.
Proof.
  intros Ha Hb.
  replace (Series a + Series b) with (real (Series a + Series b)) by auto.
  apply (f_equal real), is_lim_seq_unique.
  apply: is_series_plus ;
  by apply Series_correct.
Qed.

Lemma Series_minus (a b : nat -> R) :
  ex_series a -> ex_series b
    -> Series (fun n => a n - b n) = Series a - Series b.
Proof.
  intros Ha Hb.
  rewrite Series_plus => //.
  rewrite Series_opp => //.
  apply ex_series_opp in Hb.
  now simpl in Hb.
Qed.

(** Multiplication by a scalar *)

Section Properties3.

Context {K : AbsRing} {V : NormedModule K}.

Lemma is_series_scal (c : K) (a : nat -> V) (l : V) :
  is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
Proof.
  move => Ha.
  apply filterlim_ext with (fun n => scal c (sum_n a n)).
  elim => [ | n IH]; simpl.
  by rewrite !sum_O.
  rewrite !sum_Sn -IH.
  apply: scal_distr_l.
  now apply filterlim_comp with (2 := filterlim_scal_r _ _).
Qed.
Lemma is_series_scal_l : forall (c : K) (a : nat -> V) (l : V),
  is_series a l -> is_series (fun n => scal c (a n)) (scal c l).
exact is_series_scal.
Qed.

Lemma ex_series_scal (c : K) (a : nat -> V) :
  ex_series a -> ex_series (fun n => scal c (a n)).
Proof.
  move => [l Ha].
  exists (scal c l).
  by apply: is_series_scal_l.
Qed.

Lemma ex_series_scal_l : forall (c : K) (a : nat -> V),
  ex_series a -> ex_series (fun n => scal c (a n)).
exact ex_series_scal.
Qed.

End Properties3.

Lemma Series_scal_l (c : R) (a : nat -> R) :
  Series (fun n => c * a n) = c * Series a.
Proof.
  rewrite /Series.
  have H0 : (forall x, c * Rbar.real x = Rbar.real (Rbar.Rbar_mult (Rbar.Finite c) x)).
  case: (Req_dec c 0) => [-> | Hk].
  case => [x | | ] //= ; rewrite Rmult_0_l.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case: Rle_dec (Rle_refl 0) => //= H0 _.
  case: Rle_lt_or_eq_dec (Rlt_irrefl 0) => //= _ _.
  case => [x | | ] //= ; rewrite Rmult_0_r.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  case: Rle_dec => //= H0.
  case: Rle_lt_or_eq_dec => //=.
  rewrite H0 -(Lim_seq_scal_l _ c).
  apply f_equal, Lim_seq_ext.
  elim => [ | n IH].
  rewrite !sum_O ; ring.
  rewrite !sum_Sn IH /plus /=.
  ring.
Qed.

Lemma is_series_scal_r (c : R) (a : nat -> R) (l : R) :
  is_series  a l -> is_series  (fun n => (a n) * c) (l * c).
Proof.
  move => Ha.
  rewrite Rmult_comm.
  apply is_series_ext with (fun n : nat => c * a n).
  move => n ; apply Rmult_comm.
  apply (is_series_scal_l _ _ _ Ha).
Qed.
Lemma ex_series_scal_r (c : R) (a : nat -> R) :
  ex_series  a -> ex_series  (fun n => a n * c).
Proof.
  intros [l Ha].
  exists (l * c).
  by apply is_series_scal_r.
Qed.

Lemma Series_scal_r (c : R) (a : nat -> R) :
  Series (fun n => a n * c) = Series a * c.
Proof.
  rewrite Rmult_comm -Series_scal_l.
  apply Series_ext.
  move => n ; apply Rmult_comm.
Qed.

Lemma is_series_mult_pos (a b : nat -> R) (la lb : R) :
  is_series  a la -> is_series  b lb ->
  (forall n, 0 <= a n) -> (forall n, 0 <= b n)
  -> is_series  (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  have H0 : forall n,
    sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) n
      <= sum_f_R0 a n * sum_f_R0 b n.
    case => [ | n].
    simpl ; apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    apply Rminus_le_0 ; ring_simplify.
    apply cond_pos_sum => m.
    apply cond_pos_sum => k.
    by apply Rmult_le_pos.
  have H1 : forall n, sum_f_R0 a n * sum_f_R0 b n
    <= sum_f_R0 (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k) ((2*n)%nat).
    case => [ /= | n].
    by apply Rle_refl.
    rewrite (cauchy_finite a b (S n) (lt_O_Sn n)).
    rewrite Rplus_comm ; apply Rle_minus_r.
    replace (pred (S n)) with n by auto.
    replace (2 * S n)%nat with (S n + S n)%nat by ring.
    rewrite -sum_f_rw.
    rewrite /sum_f.
    replace (S n + S n - S (S n))%nat with n.
    elim: {1 5 8}n (le_refl n) => [ | m IH] Hm ; rewrite /sum_f_R0 -/sum_f_R0.
    rewrite -minus_n_O plus_0_l ; simpl pred.
    rewrite -?sum_f_rw_0.
    replace (sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat))
      with ((sum_f 0 (S (S n)) (fun p : nat => a p * b (S (S n) - p)%nat) -
        (fun p : nat => a p * b (S (S n) - p)%nat) 0%nat)
        + a O * b (S (S n))) by (rewrite -minus_n_O ; ring).
    rewrite -(sum_f_Sn_m _ O (S (S n))) ; [ | by apply lt_O_Sn].
    rewrite sum_f_u_Sk ; [ | by apply le_O_n].
    rewrite sum_f_n_Sm ; [ | by apply le_O_n].
    apply Rle_trans with (sum_f 0 n (fun l0 : nat => a (S (l0 + 0)) * b (S n - l0)%nat) +
      a (S (S n)) * b (S (S n) - S (S n))%nat + a 0%nat * b (S (S n))).
      apply Rminus_le_0 ; ring_simplify.
      apply Rplus_le_le_0_compat ; by apply Rmult_le_pos.
      repeat apply Rplus_le_compat_r.
      apply Req_le.
      rewrite ?sum_f_rw_0.
      elim: {1 4 6}n (le_refl n) => [ | k IH] Hk // ;
      rewrite /sum_f_R0 -/sum_f_R0.
      rewrite IH ; try by intuition.
      apply f_equal.
      by rewrite plus_0_r /=.
    apply Rplus_le_compat.
    apply IH ; intuition.
    rewrite -?sum_f_rw_0.
    rewrite MyNat.sub_succ_l ; try by intuition.
    replace (pred (S (n - S m))) with (n - S m)%nat by auto.
    rewrite plus_Sn_m -?plus_n_Sm.
    replace (sum_f 0 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat))
      with (sum_f 1 (S (S (S (m + n))))
      (fun p : nat => a p * b (S (S (S (m + n))) - p)%nat) + a O * b (S (S (S (m + n))))).
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite (sum_f_chasles _ O (S m) (S (S (S (m + n))))) ; try by intuition.
    rewrite -(Rplus_0_l (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite /sum_f.
    elim: (S m - 1)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat.
    by apply IH.
    by apply Rmult_le_pos.
    replace (S (S m)) with (1 + S m)%nat by ring.
    replace (S (S (S (m + n)))) with (S (S n) + S m )%nat by ring.
    rewrite sum_f_u_add.
    rewrite (sum_f_chasles _ O (S (n - S m)) (S (S n))) ; try by intuition.
    rewrite -(Rplus_0_r (sum_f O _ _)).
    apply Rplus_le_compat.
    rewrite sum_f_u_Sk.
    rewrite ?sum_f_rw_0.
    apply Req_le.
    elim: (n - S m)%nat => {IH} [ | k IH] ; rewrite /sum_f_R0 -/sum_f_R0 //.
    apply f_equal2 ; apply f_equal ; intuition.
    rewrite IH ; apply f_equal, f_equal2 ; apply f_equal.
    ring.
    rewrite ?(Coq.Arith.Plus.plus_comm _ (S m)) -minus_plus_simpl_l_reverse //=.
    apply le_O_n.
    rewrite /sum_f.
    elim: (S (S n) - S (S (n - S m)))%nat => {IH} [ | k IH] ;
    rewrite /sum_f_R0 -/sum_f_R0 //.
    by apply Rmult_le_pos.
    apply Rplus_le_le_0_compat => // ; by apply Rmult_le_pos.
    by apply le_n_S, le_O_n.
    by apply Rmult_le_pos.
    rewrite sum_f_Sn_m -?minus_n_O ; try by intuition.
    ring.
    replace (S (S n)) with (S n + 1)%nat.
    rewrite -minus_plus_simpl_l_reverse.
    simpl; apply minus_n_O.
    now rewrite Coq.Arith.Plus.plus_comm.
    elim: n => [ | n IH] //.
    rewrite -plus_n_Sm plus_Sn_m.
    apply lt_n_S ; intuition.
    have H2 : forall n, sum_f_R0 a (Div2.div2 n)%nat * sum_f_R0 b (Div2.div2 n)%nat <=
      sum_f_R0
      (fun k : nat => sum_f_R0 (fun p : nat => a p * b (k - p)%nat) k)
      n.
      move => n.
      case: (even_odd_cor n) => k ; case => -> {n}.
      rewrite div2_double.
      by apply H1.
      rewrite div2_S_double.
      apply Rle_trans with (1 := H1 _).
      apply Rminus_le_0 ; rewrite -sum_f_rw ; try by intuition.
      rewrite /sum_f minus_diag /sum_f_R0 -/sum_f_R0.
      apply cond_pos_sum => l ; by apply Rmult_le_pos.

    change (is_lim_seq (sum_n (fun n : nat => sum_f_R0 (fun k : nat => a k * b (n - k)%nat) n)) (Finite (la * lb))).
    apply is_lim_seq_le_le with (u := fun n => sum_f_R0 a (Div2.div2 n) * sum_f_R0 b (Div2.div2 n))
    (w := fun n => sum_f_R0 a n * sum_f_R0 b n).
    intros n; rewrite sum_n_Reals.
    by split.
    replace (Finite (la * lb)) with (Rbar_mult la lb) by auto.
    suff H : is_lim_seq
      (fun n : nat => sum_f_R0 a n * sum_f_R0 b n)
      (Rbar_mult la lb).
    apply is_lim_seq_spec in H.
    apply is_lim_seq_spec.
    move => eps.
    case: (H eps) => {H} N H.
    exists (S (2 * N))%nat => n Hn.
    apply H.
    apply le_double.
    apply le_S_n.
    apply le_trans with (1 := Hn).
    apply (Div2.ind_0_1_SS (fun n => (n <= S (2 * Div2.div2 n))%nat)).
    by apply le_O_n.
    by apply le_refl.
    move => k Hk.
    replace (Div2.div2 (S (S k))) with (S (Div2.div2 k)) by auto.
    replace (2 * S (Div2.div2 k))%nat with (S (S (2 * Div2.div2 k))) by ring.
    by repeat apply le_n_S.

    apply is_lim_seq_mult'.
    apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
    apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
    apply is_lim_seq_mult'.
    apply filterlim_ext with (2:=Hla); apply sum_n_Reals.
    apply filterlim_ext with (2:=Hlb); apply sum_n_Reals.
Qed.

Lemma is_series_mult (a b : nat -> R) (la lb : R) :
  is_series  a la -> is_series  b lb
  -> ex_series  (fun n => Rabs (a n)) -> ex_series  (fun n => Rabs (b n))
  -> is_series  (fun n => sum_f_R0 (fun k => a k * b (n - k)%nat) n) (la * lb).
Proof.
  move => Hla Hlb Ha Hb.

  set ap := fun n => (a n + Rabs (a n)) / 2.
  set am := fun n => - (a n - Rabs (a n)) / 2.
  set bp := fun n => (b n + Rabs (b n)) / 2.
  set bm := fun n => - (b n - Rabs (b n)) / 2.

  have Hap : forall n, 0 <= ap n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  assert (Sap : ex_series  ap).
    apply ex_series_scal_r.
    apply (@ex_series_plus ) => //.
    by exists la.
  have Ham : forall n, 0 <= am n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (a _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sam : ex_series  am).
    apply ex_series_scal_r.
    apply @ex_series_opp.
    apply @ex_series_minus => //.
    by exists la.
  have Hbp : forall n, 0 <= bp n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Rplus_comm ; apply Rle_minus_l ; rewrite Rminus_0_l.
    apply Rabs_maj2.
    by apply Rlt_0_2.
  assert (Sbp : ex_series  bp).
    apply ex_series_scal_r.
    apply @ex_series_plus => //.
    by exists lb.
  have Hbm : forall n, 0 <= bm n.
    move => n ; apply Rdiv_le_0_compat.
    rewrite Ropp_minus_distr'.
    apply (Rminus_le_0 (b _)).
    by apply Rle_abs.
    by apply Rlt_0_2.
  assert (Sbm : ex_series  bm).
    apply ex_series_scal_r.
    apply @ex_series_opp.
    apply @ex_series_minus => //.
    by exists lb.

  apply is_series_ext with (fun n => sum_f_R0 (fun k : nat => ap k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => am k * bp (n - k)%nat) n
    - sum_f_R0 (fun k : nat => ap k * bm (n - k)%nat) n
    + sum_f_R0 (fun k : nat => am k * bm (n - k)%nat) n).
  move => n.
  rewrite -?minus_sum -plus_sum.
  apply sum_eq => k _.
  rewrite /ap /am /bp /bm ; field.
  replace (la*lb) with ((Series ap*Series bp-Series am*Series bp-Series ap*Series bm)+Series am*Series bm).
  apply @is_series_plus.
  apply @is_series_minus.
  apply @is_series_minus.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  apply is_series_mult_pos => // ; by apply Series_correct.
  replace (la) with (Series ap - Series am).
  replace (lb) with (Series bp - Series bm).
  ring.
  rewrite -Series_minus // -(is_series_unique _ _ Hlb) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
  rewrite -Series_minus // -(is_series_unique _ _ Hla) ; apply Series_ext => n.
  rewrite /ap /am /bp /bm ; field.
Qed.

(** * D'Alembert criterion *)

Lemma ex_series_DAlembert (a : nat -> R) (k : R) :
  k < 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) k
      -> ex_series  (fun n => Rabs (a n)).
Proof.
  move => Hk Ha H.
  have : exists N, forall n, (N <= n)%nat -> Rabs (a (S n) / a n) <= (k+1)/2.
    apply is_lim_seq_spec in H.
    case: (fun He => H (mkposreal ((1-k)/2) He)).
      move: (fun He => is_pos_div_2 (mkposreal (1-k) He)) => /= He ;
      apply: He.
      by apply -> Rminus_lt_0.
    move => {H} /= Hk1 N H.
    exists N => n Hn.
    move: (H n Hn) => {H} H.
    apply Rabs_lt_between' in H ; case: H => _ H ;
    field_simplify in H ; rewrite Rdiv_1 in H ; by apply Rlt_le.
  case => {H} N H.
  apply ex_series_incr_n with N.
  apply @ex_series_le with (fun n => Rabs (a N) * ((k+1)/2)^n).
  move => n.
  rewrite /norm /= /abs /= Rabs_Rabsolu.
  rewrite Rmult_comm ; apply Rle_div_l.
  by apply Rabs_pos_lt.
  rewrite -Rabs_div.
  elim: n => [ | n IH].
  rewrite plus_0_r /Rdiv Rinv_r.
  rewrite Rabs_R1 ; by apply Rle_refl.
  by apply Ha.
  replace (Rabs (a (N + S n)%nat / a N))
    with (Rabs (a (S (N + n))/a (N+n)%nat) * Rabs (a (N + n)%nat / a N)).
  simpl ; apply Rmult_le_compat.
  by apply Rabs_pos.
  by apply Rabs_pos.
  apply H, le_plus_l.
  by apply IH.
  rewrite -Rabs_mult ; apply f_equal.
  rewrite plus_n_Sm ; field ; split ; by apply Ha.
  by apply Ha.
  apply @ex_series_scal_l.
  set k0 := ((k + 1) / 2).
  exists (/(1-k0) * (1-k0*0)).
  apply filterlim_ext with (fun N => / (1 - k0) * (1 - k0 ^ S N)).
  move => n ; rewrite sum_n_Reals; rewrite tech3.
  by apply Rmult_comm.
  unfold k0 ; lra.
  apply (is_lim_seq_scal_l (fun N0 => (1 - k0 ^ S N0)) (/ (1 - k0)) (Finite (1-k0*0))).
  apply (is_lim_seq_minus _ _ (Finite 1) (Finite (k0*0))).
  by apply is_lim_seq_const.
  simpl pow ; apply (is_lim_seq_scal_l _ _ (Finite 0)).
  apply (is_lim_seq_geom k0).
  rewrite Rabs_pos_eq.
  unfold k0 ; lra.
  apply Rle_trans with (2 := H N (le_refl _)) ; by apply Rabs_pos.
  easy.
Qed.

Lemma not_ex_series_DAlembert (a : nat -> R) (l : R) :
  l > 1 -> (forall n, a n <> 0)
    -> is_lim_seq (fun n => Rabs (a (S n) / a n)) l
      -> ~ is_lim_seq a 0.
Proof.
  move => Hl Ha Hda Ha0.
  set k := (l+1)/2.
  have Hk1 : 1 < k.
    unfold k ; lra.
  have : exists N, forall n, (N <= n)%nat -> k <= Rabs (a (S n) / a n).
    apply is_lim_seq_spec in Hda.
    case: (fun H => Hda (mkposreal ((l-1)/2) H)) => [ | /= {Hda} H N Hda].
    apply Rdiv_lt_0_compat.
    by apply -> Rminus_lt_0.
    by apply Rlt_R0_R2.
    exists N => n Hn.
    move: (Hda n Hn) => {Hda} Hda.
    apply Rabs_lt_between' in Hda.
    replace (k) with (l - (l - 1) / 2) by (unfold k ; field).
    by apply Rlt_le, Hda.
  case => N H.
  apply is_lim_seq_abs_0, (is_lim_seq_incr_n _ N) in Ha0.
  have : forall n, Rabs (a N) * k ^ n <= Rabs (a (n + N)%nat).
    elim => /= [ | n IH].
    rewrite Rmult_1_r ; by apply Rle_refl.
    replace (Rabs (a (S (n + N))))
      with (Rabs (a (S (n+N)) / a (n+N)%nat) * Rabs (a (n+N)%nat))
      by (rewrite -Rabs_mult ; apply f_equal ; by field).
    replace (Rabs (a N) * (k * k ^ n)) with (k * (Rabs (a N) * k ^ n)) by ring.
    apply Rmult_le_compat.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H, le_plus_r.
    by apply IH.
  move => {H} H.
  have : Finite 0 = p_infty.
    rewrite -(Lim_seq_geom_p k Hk1).
    apply sym_equal.
    apply is_lim_seq_unique.
    apply is_lim_seq_ext with (fun n => / Rabs (a N) * (Rabs (a N) * k ^ n)).
    move => n ; field ; by apply Rabs_no_R0.
    rewrite -(Rmult_0_r (/Rabs (a N))).
    apply (is_lim_seq_scal_l _ _ (Finite 0)).
    apply is_lim_seq_le_le with (fun _ => 0) (fun n => Rabs (a (n + N)%nat)).
    move => n ; split.
    apply Rmult_le_pos.
    by apply Rabs_pos.
    apply pow_le.
    by apply Rlt_le, Rlt_trans with (1 := Rlt_0_1).
    by apply H.
    by apply is_lim_seq_const.
    by apply Ha0.
  by [].
Qed.

Lemma partial_summation_R (a b : nat -> R) :
  (exists M, forall n, norm (sum_n b n) <= M)
  -> filterlim a eventually (locally 0)
  -> ex_series (fun n => norm (minus (a (S n)) (a n)))
  -> ex_series (fun n => scal (a n) (b n)).
Proof.
  set B := fun n => sum_n b n.
  intros Hb Ha0 Ha.
  eexists.
  unfold is_series.
  replace (@locally R_NormedModule)
    with (fun x => Rbar_locally (Finite x)) by auto.
  apply is_lim_seq_ext with (fun N =>
    plus (scal (a N) (B N))
    (match N with | O => zero | S N => sum_n (fun n => scal (minus (a n) (a (S n))) (B n)) N end)).
  case => /= [ | N].
    rewrite /B /= !sum_O ; by apply plus_zero_r.
  rewrite sum_Sn plus_comm.
  elim: N => /= [ | N IH].
    rewrite /B /= !sum_Sn !sum_O /minus !scal_distr_r !scal_distr_l !scal_opp_l.
    rewrite -!plus_assoc.
    apply f_equal.
    rewrite plus_comm -!plus_assoc.
    rewrite plus_comm -!plus_assoc.
    rewrite plus_opp_l.
    by apply plus_zero_r.
  rewrite !sum_Sn -IH ; clear IH.
  rewrite /B /= /minus !sum_Sn.
  generalize (sum_n (fun n : nat => scal (plus (a n) (opp (a (S n)))) (sum_n b n)) N) => /= c.
  generalize (sum_n b N) => b'.
  rewrite !scal_distr_r !scal_distr_l -!plus_assoc !scal_opp_l.
  repeat apply f_equal.
  repeat rewrite (plus_comm (scal (a (S (S N))) b')) -!plus_assoc.
  rewrite plus_comm -!plus_assoc plus_opp_r plus_zero_r.
  by rewrite plus_assoc plus_opp_l plus_zero_l.
  apply is_lim_seq_plus'.
  instantiate (1 := 0).
  apply filterlim_locally => eps.
  destruct Hb as [M Hb].
  eapply filter_imp.
  intros n Hn.
  apply @norm_compat1.
  rewrite /minus opp_zero plus_zero_r.
  eapply Rle_lt_trans.
  apply @norm_scal.
  eapply Rle_lt_trans.
  apply Rmult_le_compat_l.
  by apply abs_ge_0.
  eapply Rle_trans.
  by apply Hb.
  apply (Rmax_r 1).
  apply Rlt_div_r.
  eapply Rlt_le_trans, Rmax_l.
  by apply Rlt_0_1.
  apply Hn.
  assert (0 < eps / Rmax 1 M).
  apply Rdiv_lt_0_compat.
  by apply eps.
  eapply Rlt_le_trans, Rmax_l.
  by apply Rlt_0_1.
  destruct (proj1 (filterlim_locally _ _) Ha0 (mkposreal _ H)) as [N HN].
  exists N => n Hn.
  eapply Rle_lt_trans, HN, Hn.
  rewrite /minus opp_zero plus_zero_r.
  by apply Rle_refl.
  apply is_lim_seq_incr_1.
  apply (Lim_seq_correct' (fun n : nat =>
    sum_n (fun n0 : nat => scal (minus (a n0) (a (S n0))) (B n0)) n)).
  case: Hb => M Hb.
  eapply @ex_series_le.
  intros n.
  eapply Rle_trans.
  apply @norm_scal.
  apply Rmult_le_compat_l.
  by apply abs_ge_0.
  by apply Hb.
  apply ex_series_scal_r.
  move: Ha ; apply ex_series_ext => n.
  by rewrite -norm_opp /minus opp_plus opp_opp plus_comm.
Qed.

(** * Geometric series *)

Lemma is_series_geom (q : R) :
  Rabs q < 1 -> is_series  (fun n => q ^ n) (/ (1-q)).
Proof.
  move => Hq.
  apply filterlim_ext with (fun n => (1-q^(S n)) / (1-q)).
  move => n.
  rewrite sum_n_Reals; rewrite tech3.
  reflexivity.
  apply Rlt_not_eq.
  apply Rle_lt_trans with (2 := Hq).
  apply Rle_abs.
  change (is_lim_seq (fun n : nat => (1 - q ^ S n) / (1 - q)) (/(1-q))).
  replace ((/ (1 - q))) with (real (Rbar_mult (Rbar_minus 1 0) (/ (1 - q)))).
  unfold Rdiv.
  apply (is_lim_seq_scal_r (fun n : nat => (1 - q ^ S n)) (/ (1 - q)) (Rbar_minus 1 0)).
  apply is_lim_seq_minus'.
  by apply is_lim_seq_const.
  apply (is_lim_seq_incr_1 (fun n => q^n)).
  by apply is_lim_seq_geom.
  simpl; ring.
Qed.
Lemma ex_series_geom (q : R) :
  Rabs q < 1 -> ex_series  (fun n => q ^ n).
Proof.
  move => Hq.
  exists (/(1-q)).
  by apply is_series_geom.
Qed.
Lemma Series_geom (q : R) :
  Rabs q < 1 -> Series (fun n => q ^ n) = / (1-q).
Proof.
  move => Hq.
  apply is_series_unique.
  by apply is_series_geom.
Qed.
