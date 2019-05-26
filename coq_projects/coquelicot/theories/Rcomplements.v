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

(** * This file describes basic missing facts about the standard library of reals and a few concerning ssreflect.seq. It also contains a definition of the [sign] function. *)

(** Tactic for changing the last argument of a property to an evar,
    in order to apply theorems modulo equality. *)

Ltac evar_last :=
  match goal with
  | |- ?f ?x =>
    let tx := type of x in
    let tx := eval simpl in tx in
    let tmp := fresh "tmp" in
    evar (tmp : tx) ;
    refine (@eq_ind tx tmp f _ x _) ;
    unfold tmp ; clear tmp
  end.

Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Psatz.

Module MyNat.

Lemma neq_succ_0 (n : nat) : S n <> 0.
Proof.  move=> contrad.  exact: (le_Sn_0 n).  Qed.

Lemma sub_succ (n m : nat) : S n - S m = n - m.
Proof.  done.  Qed.

Lemma sub_succ_l (n m : nat) : n <= m -> S m - n = S (m - n).
Proof.  move=> h.  by rewrite minus_Sn_m.  Qed.

Lemma lt_neq (n m : nat) : n < m -> n <> m.
Proof.
intros H ->.
exact (lt_irrefl m H).
Qed.

Lemma minus_0_le (n m : nat) : n <= m -> n - m = 0.
Proof.
case: (eq_nat_dec n m) => [-> _ | h h'].
  by rewrite minus_diag.
apply: not_le_minus_0.
move=> h''.
apply: h.
exact: le_antisym.
Qed.

Lemma sub_succ_r (n m : nat) : n - S m = pred (n - m).
Proof.
case: n => [// | n ].
case: (le_le_S_dec m n) => h; rewrite sub_succ.
  rewrite -minus_Sn_m //=.
move: (le_S (S n) m h) => /le_S_n h'.
by rewrite (minus_0_le n m h') (minus_0_le (S n) m h).
Qed.

Lemma sub_add (n m : nat) : n <= m -> m - n + n = m.
Proof.
elim: m => [/le_n_0_eq // | m ih h].
by rewrite plus_comm le_plus_minus_r.
Qed.

Lemma le_pred_le_succ (n m : nat) : pred n <= m <-> n <= S m.
Proof.
case: n m => /= [ | n m].
  split=> _; exact: le_0_n.
split.
  exact: le_n_S.
exact: le_S_n.
Qed.

End MyNat.

Require Import Even Div2.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool.

Open Scope R_scope.

(** * Integers *)

(** Integer part in Z *)

Lemma floor_ex : forall x : R, {n : Z | IZR n <= x < IZR n + 1}.
Proof.
  intros.
  exists (up (x-1)) ; split.
  assert (Rw : x = 1 + (x-1)) ; [ring | rewrite {2}Rw => {Rw}].
  assert (Rw :IZR (up (x - 1))  = (IZR (up (x - 1)) - (x - 1)) + (x-1)) ;
    [ring | rewrite Rw ; clear Rw].
  apply Rplus_le_compat_r, (proj2 (archimed _)).
  assert (Rw : x = (x-1) + 1) ; [ring | rewrite {1}Rw ; clear Rw].
  apply Rplus_lt_compat_r, (proj1 (archimed _)).
Qed.
Definition floor x := proj1_sig (floor_ex x).

Lemma floor1_ex : forall x : R, {n : Z | IZR n < x <= IZR n + 1}.
Proof.
  intros.
  destruct (floor_ex x) as (n,(Hn1,Hn2)).
  destruct (Rle_lt_or_eq_dec (IZR n) x Hn1).
  exists n ; split.
  apply r.
  apply Rlt_le, Hn2.
  exists (Zpred n) ; rewrite <- e ; split.
  apply IZR_lt, Zlt_pred.
  rewrite <- (succ_IZR), <-Zsucc_pred ; apply Rle_refl.
Qed.
Definition floor1 x := proj1_sig (floor1_ex x).

(** Interger part in nat *)

Lemma nfloor_ex : forall x : R, 0 <= x -> {n : nat | INR n <= x < INR n + 1}.
Proof.
  intros.
  destruct (floor_ex x) as (m,Hm).
  destruct (Z_lt_le_dec m 0) as [z|z].
  apply Zlt_le_succ in z.
  contradict z.
  apply Zlt_not_le.
  apply lt_IZR.
  apply Rle_lt_trans with (1 := H).
  rewrite succ_IZR ; apply Hm.
  destruct m.
  exists O ; apply Hm.
  exists (nat_of_P p).
  rewrite INR_IZR_INZ.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  apply Hm.
  contradict z.
  apply Zlt_not_le.
  apply Zlt_neg_0.
Qed.
Definition nfloor x pr := proj1_sig (nfloor_ex x pr).

Lemma nfloor1_ex : forall x : R, 0 < x -> {n : nat | INR n < x <= INR n + 1}.
Proof.
  intros.
  destruct (nfloor_ex x (Rlt_le _ _ H)) as (n,(Hn1,Hn2)).
  destruct (Rle_lt_or_eq_dec (INR n) x Hn1).
  exists n ; split.
  apply r.
  apply Rlt_le, Hn2.
  destruct n.
  contradict H.
  rewrite <- e ; simpl ; apply Rlt_irrefl.
  exists n ; rewrite <- e ; split.
  apply lt_INR, lt_n_Sn.
  rewrite <- (S_INR) ; apply Rle_refl.
Qed.
Definition nfloor1 x pr := proj1_sig (nfloor1_ex x pr).

(** More theorems about INR *)

Lemma INRp1_pos : forall n, 0 < INR n + 1.
Proof.
intros N.
rewrite <- S_INR.
apply lt_0_INR.
apply lt_0_Sn.
Qed.

Lemma Rlt_nat (x : R) : (exists n : nat, x = INR (S n)) -> 0 < x.
Proof.
  intro H ; destruct H.
  rewrite H S_INR.
  apply INRp1_pos.
Qed.

Lemma Rle_pow_lin (a : R) (n : nat) :
  0 <= a -> 1 + INR n * a <= (1 + a) ^ n.
Proof.
  intro Ha.
  induction n.
  apply Req_le ; simpl ; ring.
  rewrite S_INR.
  replace (1 + (INR n + 1) * a) with ((1 + INR n * a) + a) by ring.
  apply Rle_trans with ((1 + a) ^ n + a).
  apply Rplus_le_compat_r.
  exact IHn.
  replace ((1+a)^(S n)) with ((1+a)^n + a * (1+a)^n) by (simpl ; ring).
  apply Rplus_le_compat_l.
  pattern a at 1.
  rewrite <- (Rmult_1_r a).
  apply Rmult_le_compat_l.
  exact Ha.
  clear IHn.
  apply pow_R1_Rle.
  pattern 1 at 1.
  rewrite <- (Rplus_0_r 1).
  apply Rplus_le_compat_l.
  exact Ha.
Qed.

Lemma C_n_n: forall n, C n n = 1.
Proof.
intros n; unfold C.
rewrite minus_diag.
simpl.
field.
apply INR_fact_neq_0.
Qed.

Lemma C_n_0: forall n, C n 0 = 1.
Proof.
intros n; unfold C.
rewrite - minus_n_O.
simpl.
field.
apply INR_fact_neq_0.
Qed.

Fixpoint pow2 (n : nat) : nat :=
  match n with
    | O => 1%nat
    | S n => (2 * pow2 n)%nat
  end.

Lemma pow2_INR (n : nat) : INR (pow2 n) = 2^n.
Proof.
  elim: n => //= n IH ;
  rewrite ?plus_INR ?IH /= ; field.
Qed.

Lemma pow2_pos (n : nat) : (0 < pow2 n)%nat.
Proof.
  apply INR_lt ; rewrite pow2_INR.
  apply pow_lt, Rlt_0_2.
Qed.

(** * Rinv *)

Lemma Rinv_le_contravar :
  forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.
intros x y H1 [H2|H2].
apply Rlt_le.
apply Rinv_lt_contravar with (2 := H2).
apply Rmult_lt_0_compat with (1 := H1).
now apply Rlt_trans with x.
rewrite H2.
apply Rle_refl.
Qed.

Lemma Rinv_lt_cancel (x y : R) :
  0 < y -> / y < / x -> x < y.
Proof.
  intro Hy ; move/Rlt_not_le => Hxy.
  apply Rnot_le_lt ; contradict Hxy.
  by apply Rinv_le_contravar.
Qed.

(** * Rdiv *)
(** Rewritings *)

Lemma Rdiv_1 : forall x : R, x / 1 = x.
Proof.
  intros.
  unfold Rdiv ;
  rewrite Rinv_1 Rmult_1_r.
  reflexivity.
Qed.

Lemma Rdiv_plus : forall a b c d : R, b <> 0 -> d <> 0 ->
  a / b + c / d = (a * d + c * b) / (b * d).
Proof.
  intros.
  field.
  split.
  apply H0.
  apply H.
Qed.

Lemma Rdiv_minus : forall a b c d : R, b <> 0 -> d <> 0 ->
  a / b - c / d = (a * d - c * b) / (b * d).
Proof.
  intros.
  field.
  split.
  apply H0.
  apply H.
Qed.

(** Order *)

Lemma Rplus_lt_reg_l (x y z : R) : x + y < x + z -> y < z.
Proof.
first [
  (* 8.4 *)
  exact: Rplus_lt_reg_r
|
  (* 8.5 *)
  exact: Rplus_lt_reg_l
].
Qed.

Lemma Rplus_lt_reg_r (x y z : R) : y + x < z + x -> y < z.
Proof.
first [
  (* 8.4 *)
  intro H ;
  apply Rplus_lt_reg_r with x ;
  now rewrite 2!(Rplus_comm x)
|
  (* 8.5 *)
  exact: Rplus_lt_reg_r
].
Qed.

Lemma Rle_div_l : forall a b c, c > 0 -> (a / c <= b <-> a <= b * c).
Proof.
  split ; intros.
  replace a with ((a/c) * c) by (field ; apply Rgt_not_eq, H).
  apply Rmult_le_compat_r.
  apply Rlt_le, H.
  apply H0.

  replace b with ((b*c)/c)  by (field ; apply Rgt_not_eq, H).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, H.
  apply H0.
Qed.

Lemma Rle_div_r : forall a b c, c > 0 -> (a * c <= b <-> a <= b / c).
Proof.
  split ; intros.
  replace a with ((a * c) / c) by (field ; apply Rgt_not_eq, H).
  apply Rmult_le_compat_r.
  apply Rlt_le, Rinv_0_lt_compat, H.
  apply H0.

  replace b with ((b / c) * c)  by (field ; apply Rgt_not_eq, H).
  apply Rmult_le_compat_r.
  apply Rlt_le, H.
  apply H0.
Qed.

Lemma Rlt_div_l : forall a b c, c > 0 -> (a / c < b <-> a < b*c).
Proof.
  split ; intros.
  replace a with ((a/c) * c) by (field ; apply Rgt_not_eq, H).
  apply Rmult_lt_compat_r.
  apply H.
  apply H0.

  replace b with ((b*c)/c)  by (field ; apply Rgt_not_eq, H).
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat, H.
  apply H0.
Qed.

Lemma Rlt_div_r : forall a b c, c > 0 -> (a * c < b <-> a < b / c).
Proof.
  split ; intros.
  replace a with ((a * c) / c) by (field ; apply Rgt_not_eq, H).
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat, H.
  apply H0.

  replace b with ((b / c) * c)  by (field ; apply Rgt_not_eq, H).
  apply Rmult_lt_compat_r.
  apply H.
  apply H0.
Qed.

Lemma Rdiv_lt_0_compat : forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 0 < r1 / r2.
Proof.
  intros r1 r2 H1 H2.
  apply Rlt_div_r.
  apply H2.
  rewrite Rmult_0_l.
  apply H1.
Qed.

Lemma Rdiv_le_0_compat : forall r1 r2 : R, 0 <= r1 -> 0 < r2 -> 0 <= r1 / r2.
Proof.
 intros.
 apply Rle_div_r.
 apply H0.
 rewrite Rmult_0_l.
 apply H.
Qed.

Lemma Rdiv_lt_1 : forall r1 r2, 0 < r2 -> (r1 < r2 <-> r1 / r2 < 1).
Proof.
  intros.
  pattern r2 at 1.
  rewrite <- (Rmult_1_l r2).
  split ; apply Rlt_div_l ; apply H.
Qed.

Lemma Rdiv_le_1 : forall r1 r2, 0 < r2 -> (r1 <= r2 <-> r1/r2 <= 1).
Proof.
  intros.
  pattern r2 at 1.
  rewrite <- (Rmult_1_l r2).
  split ; apply Rle_div_l ; apply H.
Qed.

(** * Rmult *)

Lemma Rle_mult_Rlt : forall c a b : R, 0 < b -> c < 1 -> a <= b*c -> a < b.
Proof.
  intros.
  apply Rle_lt_trans with (1 := H1).
  pattern b at 2 ; rewrite <-(Rmult_1_r b).
  apply Rmult_lt_compat_l ; auto.
Qed.

Lemma Rmult_le_0_r : forall a b, a <= 0 -> 0 <= b -> a * b <= 0.
Proof.
  intros ;
  rewrite <-(Rmult_0_r a) ;
  apply (Rmult_le_compat_neg_l a 0 b) with (1 := H) ; auto.
Qed.

Lemma Rmult_le_0_l : forall a b, 0 <= a -> b <= 0 -> a * b <= 0.
Proof.
  intros ; rewrite Rmult_comm ; apply Rmult_le_0_r ; auto.
Qed.

Lemma pow2_gt_0 (x : R) : x <> 0 -> 0 < x ^ 2.
Proof.
  destruct (pow2_ge_0 x) => // Hx.
  contradict Hx.
  apply sym_eq, Rmult_integral in H ;
  case: H => // H.
  apply Rmult_integral in H ;
  case: H => // H.
  contradict H ; apply Rgt_not_eq, Rlt_0_1.
Qed.

(** * Rminus *)
(** Rewritings *)

Lemma Rminus_eq_0 : forall r : R, r - r = 0.
Proof.
  intros.
  ring.
Qed.

Lemma Rdiv_minus_distr : forall a b c, b <> 0 -> a / b - c = (a - b * c) / b.
Proof.
    intros.
    field.
    apply H.
Qed.

Lemma Rmult_minus_distr_r: forall r1 r2 r3 : R, (r1 - r2) * r3 = r1 * r3 - r2 * r3.
Proof.
  intros.
  unfold Rminus.
  rewrite <- Ropp_mult_distr_l_reverse.
  apply Rmult_plus_distr_r.
Qed.

Lemma Rminus_eq_compat_l : forall r r1 r2 : R, r1 = r2 <-> r - r1 = r - r2.
Proof.
  split ; intros.
  apply Rplus_eq_compat_l.
  rewrite H.
  reflexivity.

  replace r1 with (r-(r-r1)) by ring.
  replace r2 with (r-(r-r2)) by ring.
  apply Rplus_eq_compat_l.
  rewrite H.
  reflexivity.
Qed.

Lemma Ropp_plus_minus_distr : forall r1 r2 : R, - (r1 + r2) = - r1 - r2.
Proof.
  intros.
  unfold Rminus.
  apply Ropp_plus_distr.
Qed.

(** Order *)

Lemma Rle_minus_l : forall a b c,(a - c <= b <-> a <= b + c).
Proof.
  split ; intros.
  replace a with ((a-c)+c) by ring.
  apply Rplus_le_compat_r.
  apply H.

  replace b with ((b+c)-c) by ring.
  apply Rplus_le_compat_r.
  apply H.
Qed.

Lemma Rlt_minus_r : forall a b c,(a < b - c <-> a + c < b).
Proof.
  split ; intros.
  replace b with ((b-c)+c) by ring.
  apply Rplus_lt_compat_r.
  apply H.

  replace a with ((a+c)-c) by ring.
  apply Rplus_lt_compat_r.
  apply H.
Qed.

Lemma Rlt_minus_l : forall a b c,(a - c < b <-> a < b + c).
Proof.
  split ; intros.
  replace a with ((a-c)+c) by ring.
  apply Rplus_lt_compat_r.
  apply H.

  replace b with ((b+c)-c) by ring.
  apply Rplus_lt_compat_r.
  apply H.
Qed.

Lemma Rle_minus_r : forall a b c,(a <= b - c <-> a + c <= b).
Proof.
  split ; intros.
  replace b with ((b-c)+c) by ring.
  apply Rplus_le_compat_r.
  apply H.

  replace a with ((a+c)-c) by ring.
  apply Rplus_le_compat_r.
  apply H.
Qed.

Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a.
Proof.
  intros.
  pattern a at 1.
  rewrite <- (Rplus_0_l a).
  split ; apply Rle_minus_r.
Qed.

Lemma Rminus_lt_0 : forall a b, a < b <-> 0 < b - a.
Proof.
Proof.
  intros.
  pattern a at 1.
  rewrite <- (Rplus_0_l a).
  split ; apply Rlt_minus_r.
Qed.

(** * Rplus *)
(** Sums *)

Lemma sum_f_rw (a : nat -> R) (n m : nat) :
  (n < m)%nat -> sum_f (S n) m a = sum_f_R0 a m - sum_f_R0 a n.
Proof.
  intro Hnm ; unfold sum_f.
  revert  a n Hnm.
  induction m ; intros a n Hnm.
  apply lt_n_O in Hnm ; intuition.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl.
  revert Hnm ;
  destruct n ; intro Hnm.
  rewrite <- minus_n_O ; simpl ; ring_simplify.
  clear Hnm IHm.
  induction m ; simpl.
  reflexivity.
  rewrite <- plus_n_Sm, plus_0_r, IHm ; reflexivity.
  rewrite (decomp_sum _ _ (lt_O_Sn _)) ; simpl ; ring_simplify.
  apply lt_S_n in Hnm.
  rewrite <- (IHm _ _ Hnm).
  clear IHm.
  induction (m - S n)%nat ; simpl.
  reflexivity.
  rewrite <- plus_n_Sm, IHn0 ; reflexivity.
Qed.

Lemma sum_f_rw_0 (u : nat -> R) (n : nat) :
  sum_f O n u = sum_f_R0 u n.
Proof.
  rewrite /sum_f -minus_n_O.
  elim: n => [ | n IH] //.
  rewrite /sum_f_R0 -/sum_f_R0 //.
  by rewrite plus_0_r IH.
Qed.

Lemma sum_f_n_Sm (u : nat -> R) (n m : nat) :
  (n <= m)%nat -> sum_f n (S m) u = sum_f n m u + u (S m).
Proof.
  move => H.
  rewrite /sum_f -minus_Sn_m // /sum_f_R0 -/sum_f_R0.
  rewrite plus_Sn_m.
  by rewrite MyNat.sub_add.
Qed.
Lemma sum_f_u_Sk (u : nat -> R) (n m : nat) :
  (n <= m)%nat -> sum_f (S n) (S m) u = sum_f n m (fun k => u (S k)).
Proof.
  move => H ; rewrite /sum_f.
  simpl minus.
  elim: (m - n)%nat => [ | k IH] //=.
  rewrite IH ; repeat apply f_equal.
  by rewrite plus_n_Sm.
Qed.
Lemma sum_f_u_add (u : nat -> R) (p n m : nat) :
  (n <= m)%nat -> sum_f (n + p)%nat (m + p)%nat u = sum_f n m (fun k => u (k + p)%nat).
Proof.
  move => H ; rewrite /sum_f.
  rewrite ?(plus_comm _ p) -minus_plus_simpl_l_reverse.
  elim: (m - n)%nat => [ | k IH] //=.
  by rewrite plus_comm.
  rewrite IH ; repeat apply f_equal.
  ring.
Qed.


Lemma sum_f_Sn_m (u : nat -> R) (n m : nat) :
  (n < m)%nat -> sum_f (S n) m u = sum_f n m u - u n.
Proof.
  move => H.
  elim: m n H => [ | m IH] // n H.
  by apply lt_n_O in H.
  rewrite sum_f_u_Sk ; try by intuition.
  rewrite sum_f_n_Sm ; try by intuition.
  replace (sum_f n m u + u (S m) - u n)
    with ((sum_f n m u - u n) + u (S m)) by ring.
  apply lt_n_Sm_le, le_lt_eq_dec in H.
  case: H => [ H | -> {n} ] //.
  rewrite -IH => //.
  rewrite /sum_f ; simpl.
  rewrite MyNat.sub_succ_r.
  apply lt_minus_O_lt in H.
  rewrite -{3}(MyNat.sub_add n m) ; try by intuition.
  case: (m-n)%nat H => {IH} [ | k] //= H.
  by apply lt_n_O in H.
  apply (f_equal (fun y => y + _)).
  elim: k {H} => [ | k IH] //.
  rewrite /sum_f_R0 -/sum_f_R0 IH ; repeat apply f_equal ; intuition.
  rewrite /sum_f minus_diag /= ; ring.
Qed.

Lemma sum_f_R0_skip (u : nat -> R) (n : nat) :
  sum_f_R0 (fun k => u (n - k)%nat) n = sum_f_R0 u n.
Proof.
  suff H : forall n m, (n < m)%nat
    -> sum_f n m (fun k => u ((m - k) + n)%nat) = sum_f n m u.

  case: n => [ | n] //.
  move: (H _ _ (lt_O_Sn n)) => {H} H.
  rewrite /sum_f in H.
  transitivity (sum_f_R0 (fun x : nat => u (S n - (x + 0) + 0)%nat) (S n - 0)).
    replace (S n - 0)%nat with (S n) by auto.
    elim: {2 4}(S n) => [ | m IH] //.
    simpl ; by rewrite plus_0_r.
    rewrite /sum_f_R0 -/sum_f_R0 -IH.
    apply f_equal.
    by rewrite ?plus_0_r.
  rewrite H.
  replace (S n - 0)%nat with (S n) by auto.
  elim: (S n) => [ | m IH] //.
  rewrite /sum_f_R0 -/sum_f_R0 -IH.
  apply f_equal.
  by rewrite plus_0_r.

  move => {n} n m H.
  elim: m u H => [ | m IH] u H //.
  apply lt_n_Sm_le, le_lt_eq_dec in H ; case: H IH => [H IH | -> _ {n}] //.
  rewrite sum_f_n_Sm ; try by intuition.
  replace (sum_f n (S m) u) with (sum_f n (S m) u - u n + u n) by ring.
  rewrite -sum_f_Sn_m ; try by intuition.
  rewrite sum_f_u_Sk ; try by intuition.
  rewrite -(IH (fun k => u (S k))) => {IH} ; try by intuition.
  apply f_equal2.
  rewrite /sum_f.
  elim: {1 3 4}(m - n)%nat (le_refl (m-n)%nat) => [ | k IH] // Hk ;
  rewrite /sum_f_R0 -/sum_f_R0.
  apply f_equal.
  rewrite plus_0_l MyNat.sub_add ; intuition.
  rewrite IH ; try by intuition.
  by rewrite minus_diag plus_0_l.

  rewrite /sum_f.
  rewrite -minus_Sn_m ; try by intuition.
  rewrite minus_diag.
  rewrite /sum_f_R0 -/sum_f_R0.
  replace (1+m)%nat with (S m) by ring.
  rewrite plus_0_l minus_diag MyNat.sub_add ; intuition.
Qed.

Lemma sum_f_chasles (u : nat -> R) (n m k : nat) :
  (n < m)%nat -> (m < k)%nat ->
  sum_f (S n) k u = sum_f (S n) m u + sum_f (S m) k u.
Proof.
  move => Hnm Hmk.
  rewrite ?sum_f_rw //.
  ring.
  by apply lt_trans with m.
Qed.

(** * Rmin and Rmax *)
(** Rewritings *)

Lemma Rplus_max_distr_l :
  forall a b c, a + Rmax b c = Rmax (a + b) (a + c).
Proof.
intros a b c.
unfold Rmax.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
apply Rplus_le_reg_l with (1 := H').
Qed.

Lemma Rplus_max_distr_r :
  forall a b c, Rmax b c + a = Rmax (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
apply Rplus_max_distr_l.
Qed.

Lemma Rplus_min_distr_l :
  forall a b c, a + Rmin b c = Rmin (a + b) (a + c).
Proof.
intros a b c.
unfold Rmin.
case Rle_dec ; intros H ; case Rle_dec ; intros H' ; try easy.
elim H'.
apply Rplus_le_compat_l with (1 := H).
elim H.
apply Rplus_le_reg_l with (1 := H').
Qed.

Lemma Rplus_min_distr_r :
  forall a b c, Rmin b c + a = Rmin (b + a) (c + a).
Proof.
intros a b c.
rewrite <- 3!(Rplus_comm a).
apply Rplus_min_distr_l.
Qed.

Lemma Rmult_max_distr_l :
  forall a b c, 0 <= a -> a * Rmax b c = Rmax (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmax.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha  ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmax ; assert (H := Rle_refl 0).
case Rle_dec ; intuition.
Qed.

Lemma Rmult_max_distr_r :
  forall a b c, 0 <= a -> Rmax b c * a = Rmax (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
apply Rmult_max_distr_l.
Qed.

Lemma Rmult_min_distr_l :
  forall a b c, 0 <= a -> a * Rmin b c = Rmin (a * b) (a * c).
Proof.
intros a b c Ha.
destruct Ha as [Ha|Ha].
unfold Rmin.
case Rle_dec ; intros H.
apply (Rmult_le_compat_l _ _ _ (Rlt_le _ _ Ha)) in H.
case Rle_dec ; intuition.
apply Rnot_le_lt, (Rmult_lt_compat_l _ _ _ Ha), Rlt_not_le in H.
case Rle_dec ; intuition.
rewrite <- Ha  ; clear a Ha.
repeat rewrite Rmult_0_l.
unfold Rmin ; assert (H := Rle_refl 0).
case Rle_dec ; intuition.
Qed.

Lemma Rmult_min_distr_r :
  forall a b c, 0 <= a -> Rmin b c * a = Rmin (b * a) (c * a).
Proof.
intros a b c.
rewrite <- 3!(Rmult_comm a).
apply Rmult_min_distr_l.
Qed.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) =
  Rmin (Rmin x y) z.
intros x y z; unfold Rmin.
destruct (Rle_dec y z);
destruct (Rle_dec x y);
destruct (Rle_dec x z);
destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
apply Rlt_not_le, Rlt_trans with y ; apply Rnot_le_lt ; auto.
Qed.

Lemma Rmax_assoc : forall x y z, Rmax x (Rmax y z) =
  Rmax (Rmax x y) z.
intros x y z; unfold Rmax.
destruct (Rle_dec y z);
destruct (Rle_dec x y);
destruct (Rle_dec x z);
destruct (Rle_dec y z) ; try intuition.
contradict n.
apply Rle_trans with y ; auto.
contradict r.
apply Rlt_not_le, Rlt_trans with y ; apply Rnot_le_lt ; auto.
Qed.

(** Order *)

Lemma Rmax_le_compat : forall a b c d, a <= b -> c <= d -> Rmax a c <= Rmax b d.
Proof.
  intros.
  unfold Rmax.
  destruct (Rle_dec a c).
  destruct (Rle_dec b d).
    apply H0.
    apply Rnot_le_lt in n.
    apply (Rle_trans _ d).
    apply H0.
    apply (Rlt_le _ _ n).
  destruct (Rle_dec b d).
    apply (Rle_trans _ b).
    apply H.
    apply r.
    apply H.
Qed.

Lemma Rmax_opp_Rmin : forall a b, Rmax (-a) (-b) = - Rmin a b.
Proof.
  intros.
  destruct (Rle_or_lt a b).

  rewrite Rmax_left.
  rewrite Rmin_left.
  reflexivity.
  apply H.
  apply Ropp_le_contravar.
  apply H.

  rewrite Rmax_right.
  rewrite Rmin_right.
  reflexivity.
  apply Rlt_le, H.
  apply Ropp_le_contravar.
  apply Rlt_le.
  apply H.
Qed.
Lemma Rmin_opp_Rmax : forall a b, Rmin (-a) (-b) = - Rmax a b.
Proof.
  intros.
  rewrite Rmax_comm.
  unfold Rmin ; case Rle_dec ; intro Hab.
  apply Ropp_le_cancel in Hab.
  unfold Rmax ; case Rle_dec ; intuition.
  apply Rnot_le_lt, Ropp_lt_cancel, Rlt_not_le in Hab.
  unfold Rmax ; case Rle_dec ; intuition.
Qed.


Lemma Rmax_mult : forall a b c, 0 <= c -> Rmax a b * c = Rmax (a * c) (b * c).
Proof.
  intros.
  repeat rewrite (Rmult_comm _ c).
  apply sym_eq.
  apply RmaxRmult.
  apply H.
Qed.

Lemma Rmax_le_Rplus : forall a b : R, 0 <= a -> 0 <= b -> Rmax a b <= a + b.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  rewrite <- (Rplus_0_l (Rmax a b)).
  rewrite Rmax_right.
  apply Rplus_le_compat_r.
  apply H.
  apply r.
  rewrite <- (Rplus_0_r (Rmax a b)).
  rewrite Rmax_left.
  apply Rplus_le_compat_l.
  apply H0.
  apply Rlt_le, r.
Qed.

Lemma Rplus_le_Rmax : forall a b : R, a + b <= 2*Rmax a b.
Proof.
  intros.
  rewrite RIneq.double.
  destruct (Rle_lt_dec a b).
  rewrite Rmax_right.
  apply Rplus_le_compat_r.
  apply r.
  apply r.
  rewrite Rmax_left.
  apply Rplus_le_compat_l.
  apply Rlt_le.
  apply r.
  apply Rlt_le, r.
Qed.



Lemma Rmin_Rmax_l : forall a b, Rmin a b <= a <= Rmax a b.
Proof.
  split.
  apply Rmin_l.
  apply RmaxLess1.
Qed.

Lemma Rmin_Rmax_r : forall a b, Rmin a b <= b <= Rmax a b.
Proof.
  split.
  apply Rmin_r.
  apply RmaxLess2.
Qed.

Lemma Rmin_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros.
  apply Rle_trans with a; apply Rmin_Rmax_l.
Qed.


(** * Rabs *)
(** Rewritings *)

Lemma Rabs_div : forall a b : R, b <> 0 -> Rabs (a/b) = (Rabs a) / (Rabs b).
Proof.
  intros.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite Rabs_Rinv.
  reflexivity.
  apply H.
Qed.

Lemma Rabs_eq_0 : forall x, Rabs x = 0 -> x = 0.
Proof.
  intros.
  unfold Rabs in H.
  destruct Rcase_abs.
  rewrite <- (Ropp_involutive x).
  apply Ropp_eq_0_compat.
  apply H.
  apply H.
Qed.

(** Order *)

Lemma Rabs_le_between : forall x y, (Rabs x <= y <-> -y <= x <= y).
Proof.
  split.

  split.
  rewrite <-(Ropp_involutive x).
  apply Ropp_le_contravar.
  apply (Rle_trans _ (Rabs x)).
  rewrite <-Rabs_Ropp.
  apply RRle_abs.
  apply H.
  apply (Rle_trans _ (Rabs x)).
  apply RRle_abs.
  apply H.

  intros.
  unfold Rabs.
  destruct (Rcase_abs x).
  rewrite <-(Ropp_involutive y).
  apply Ropp_le_contravar.
  apply H.
  apply H.
Qed.

Lemma Rabs_le_between' : forall x y z, Rabs (x - y) <= z <-> y-z <= x <= y+z.
Proof.
  split ; intros.
  cut (-z <= x-y <= z).
  intros ; split.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  apply H0.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite Rplus_comm.
  apply H0.
  apply (Rabs_le_between (x-y) z).
  apply H.

  apply (Rabs_le_between (x-y) z).
  split.
  rewrite <- (Rplus_0_r (-z)).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rplus_comm.
  apply H.
  rewrite <- (Rplus_0_r z).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_le_compat_r.
  rewrite Rplus_comm.
  apply H.
Qed.

Lemma Rabs_lt_between : forall x y, (Rabs x < y <-> -y < x < y).
Proof.
  split.
  intros; split; now apply Rabs_def2.
  intros (H1,H2); now apply Rabs_def1.
Qed.

Lemma Rabs_lt_between' : forall x y z, Rabs (x - y) < z <-> y-z < x < y+z.
Proof.
  split ; intros.
  cut (-z < x-y < z).
  intros ; split.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_lt_compat_l.
  rewrite Rplus_comm.
  apply H0.
  rewrite <- (Rplus_0_l x).
  rewrite <-(Rplus_opp_r y).
  rewrite Rplus_assoc.
  apply Rplus_lt_compat_l.
  rewrite Rplus_comm.
  apply H0.
  apply (Rabs_lt_between (x-y) z).
  apply H.

  apply (Rabs_lt_between (x-y) z).
  split.
  rewrite <- (Rplus_0_r (-z)).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  rewrite Rplus_comm.
  apply H.
  rewrite <- (Rplus_0_r z).
  rewrite <-(Rplus_opp_r y).
  rewrite <- Rplus_assoc.
  apply Rplus_lt_compat_r.
  rewrite Rplus_comm.
  apply H.
Qed.

Lemma Rabs_le_between_min_max : forall x y z, Rmin x y <= z <= Rmax x y -> Rabs (z - y) <= Rabs (x - y).
Proof.
 intros x y z H.
 case (Rle_or_lt x y); intros H'.
 (* *)
 rewrite Rmin_left in H;[idtac|exact H'].
 rewrite Rmax_right in H;[idtac|exact H'].
 rewrite Rabs_left1.
 rewrite Rabs_left1.
 apply Ropp_le_contravar.
 apply Rplus_le_compat_r.
 apply H.
 apply Rle_minus; exact H'.
 apply Rle_minus; apply H.
 (* *)
 rewrite Rmin_right in H;[idtac|left; exact H'].
 rewrite Rmax_left in H;[idtac|left; exact H'].
 rewrite Rabs_right.
 rewrite Rabs_right.
 apply Rplus_le_compat_r.
 apply H.
 apply Rge_minus; left; apply H'.
 apply Rge_minus, Rle_ge; apply H.
 Qed.

Lemma Rabs_le_between_Rmax : forall x m M,
  m <= x <= M -> Rabs x <= Rmax M (-m).
Proof.
  intros x m M Hx.
  unfold Rabs ;
  destruct Rcase_abs as [H|H].
  apply Rle_trans with (2 := RmaxLess2 _ _).
  apply Ropp_le_contravar, Hx.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  apply Hx.
Qed.

Lemma Rabs_lt_between_Rmax : forall x m M,
  m < x < M -> Rabs x < Rmax M (-m).
Proof.
  intros x m M Hx.
  unfold Rabs ;
  destruct Rcase_abs as [H|H].
  apply Rlt_le_trans with (2 := RmaxLess2 _ _).
  apply Ropp_lt_contravar, Hx.
  apply Rlt_le_trans with (2 := RmaxLess1 _ _).
  apply Hx.
Qed.


Lemma Rabs_maj2 : forall x, -x <= Rabs x.
Proof.
  intros.
  rewrite <- Rabs_Ropp.
  apply Rle_abs.
Qed.


(** * Req *)

Lemma Req_lt_aux : forall x y, (forall eps : posreal, Rabs (x - y) < eps) -> x = y.
Proof.
  intros.
  apply Rminus_diag_uniq.
  apply Rabs_eq_0.
  apply Rle_antisym.
  apply le_epsilon.
  intros.
  rewrite Rplus_0_l.
  apply Rlt_le.
  apply (H (mkposreal eps H0)).
  apply Rabs_pos.
Qed.

Lemma Req_le_aux : forall x y, (forall eps : posreal, Rabs (x - y) <= eps) -> x = y.
Proof.
  intros.
  apply Rminus_diag_uniq.
  apply Rabs_eq_0.
  apply Rle_antisym.
  apply le_epsilon.
  intros.
  rewrite Rplus_0_l.
  apply (H (mkposreal eps H0)).
  apply Rabs_pos.
Qed.


(** * posreal *)

Lemma is_pos_div_2 (eps : posreal) : 0 < eps / 2.
Proof.
  unfold Rdiv ; apply Rmult_lt_0_compat ;
  [apply eps | apply Rinv_0_lt_compat, Rlt_0_2].
Qed.
Definition pos_div_2 (eps : posreal) := mkposreal _ (is_pos_div_2 eps).

(** * The sign function *)

Definition sign (x : R) :=
  match total_order_T 0 x with
  | inleft (left _) => 1
  | inleft (right _) => 0
  | inright _ => -1
  end.

Lemma sign_0 : sign 0 = 0.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
elim (Rlt_irrefl _ H).
exact H.
elim (Rlt_irrefl _ H).
Qed.

Lemma sign_opp (x : R) : sign (-x) = - sign x.
Proof.
unfold sign.
case total_order_T as [[H|H]|H] ;
  case total_order_T as [[H'|H']|H'] ;
  lra.
Qed.

Lemma sign_eq_1 (x : R) : 0 < x -> sign x = 1.
Proof.
intros Hx.
unfold sign.
case total_order_T as [[H|H]|H] ; lra.
Qed.

Lemma sign_eq_m1 (x : R) : x < 0 -> sign x = -1.
Proof.
intros Hx.
unfold sign.
case total_order_T as [[H|H]|H] ; lra.
Qed.

Lemma sign_le (x y : R) : x <= y -> sign x <= sign y.
Proof.
intros Hx.
unfold sign.
case total_order_T as [[H|H]|H] ;
  case total_order_T as [[H'|H']|H'] ;
  lra.
Qed.

Lemma sign_ge_0 (x : R) : 0 <= x -> 0 <= sign x.
Proof.
intros Hx.
rewrite <- sign_0.
now apply sign_le.
Qed.

Lemma sign_le_0 (x : R) : x <= 0 -> sign x <= 0.
Proof.
intros Hx.
rewrite <- sign_0.
now apply sign_le.
Qed.

Lemma sign_neq_0 (x : R) : x <> 0 -> sign x <> 0.
Proof.
intros Hx.
unfold sign.
case total_order_T as [[H|H]|H] ; lra.
Qed.

Lemma sign_mult (x y : R) : sign (x * y) = sign x * sign y.
Proof.
  wlog: x / (0 < x) => [Hw | Hx].
    case: (Rle_lt_dec 0 x) => Hx.
    case: Hx => Hx.
    by apply Hw.
    rewrite -Hx Rmult_0_l.
    rewrite sign_0.
    by rewrite Rmult_0_l.
    rewrite -(Ropp_involutive x).
    rewrite sign_opp Ropp_mult_distr_l_reverse sign_opp Hw.
    ring.
    by apply Ropp_0_gt_lt_contravar.
  wlog: y / (0 < y) => [Hw | Hy].
    case: (Rle_lt_dec 0 y) => Hy.
    case: Hy => Hy.
    by apply Hw.
    rewrite -Hy Rmult_0_r.
    rewrite sign_0.
    by rewrite Rmult_0_r.
    rewrite -(Ropp_involutive y).
    rewrite sign_opp Ropp_mult_distr_r_reverse sign_opp Hw.
    ring.
    by apply Ropp_0_gt_lt_contravar.
  have Hxy : 0 < x * y.
    by apply Rmult_lt_0_compat.
  rewrite -> 3!sign_eq_1 by easy.
  by rewrite Rmult_1_l.
Qed.

Lemma sign_min_max (a b : R) :
  sign (b - a) * (Rmax a b - Rmin a b) = b - a.
Proof.
unfold sign.
case total_order_T as [[H|H]|H].
assert (K := proj2 (Rminus_le_0 a b) (Rlt_le _ _ H)).
rewrite (Rmax_right _ _ K) (Rmin_left _ _ K).
apply Rmult_1_l.
rewrite -H.
apply Rmult_0_l.
assert (K : b <= a).
apply Rnot_lt_le.
contradict H.
apply Rle_not_lt.
apply -> Rminus_le_0.
now apply Rlt_le.
rewrite (Rmax_left _ _ K) (Rmin_right _ _ K).
ring.
Qed.

Lemma sum_INR : forall n, sum_f_R0 INR n = INR n * (INR n + 1) / 2.
Proof.
  elim => [ | n IH] ; rewrite /sum_f_R0 -/sum_f_R0 ?S_INR /=.
  rewrite /Rdiv ; ring.
  rewrite IH ; field.
Qed.

(** * ssreflect.seq *)
(** Finite subdivision *)

Lemma interval_finite_subdiv (a b : R) (eps : posreal) : (a <= b) ->
  {l : seq R | head 0 l = a /\ last 0 l = b /\
    forall i, (S i < size l)%nat -> nth 0 l i < nth 0 l (S i) <= nth 0 l i + eps}.
Proof.
  move => Hab.
  suff Hn : 0 <= (b - a) / eps.
  set n : nat := nfloor ((b - a) / eps) Hn.

  case: (Req_EM_T (INR n) ((b - a) / eps)) => Hdec.

  set l : seq R := mkseq (fun k => a + INR k * eps) (S n).
  exists l.
  split.
  simpl ; rewrite /Rdiv ; ring.
  split.
  replace b with (a + INR n * eps).
  simpl.
  rewrite (last_map (fun k => a + INR k * eps) _ O) /=.
  rewrite (last_nth O) size_iota /=.
  case H : n => [ | m].
  by simpl.
  by rewrite /nth -/(nth _ _ m) nth_iota.
  rewrite Hdec ; field.
  by apply Rgt_not_eq, eps.
  move => i Hi ;
  rewrite size_mkseq in Hi.
  split.
  rewrite ?nth_mkseq //.
  rewrite S_INR Rminus_lt_0 ; ring_simplify.
  by apply eps.
  elim: (S n) (S i) Hi => /= [ | m IH] ;
  case => /= [ | j] Hj //.
  by apply lt_irrefl in Hj.
  by apply lt_n_O in Hj.
  by apply IH, lt_S_n.
  elim: (S n) (S i) Hi => /= [ | m IH] ;
  case => /= [ | j] Hj //.
  by apply lt_n_O in Hj.
  by apply IH, lt_S_n.
  rewrite ?nth_mkseq //.
  rewrite S_INR Rminus_le_0 ; ring_simplify.
  by apply Rle_refl.
  elim: (S n) (S i) Hi => /= [ | m IH] ;
  case => /= [ | j] Hj //.
  by apply lt_n_O in Hj.
  by apply IH, lt_S_n.
  elim: (S n) (S i) Hi => /= [ | m IH] ;
  case => /= [ | j] Hj //.
  by apply lt_n_O in Hj.
  by apply lt_n_O in Hj.
  by apply IH, lt_S_n.

  set l : seq R := rcons (mkseq (fun k => a + INR k * eps) (S n)) b.
  exists l.
  split.
  simpl ; rewrite /Rdiv ; ring.
  split.
  simpl ; by rewrite last_rcons.
  move => i Hi ;
  rewrite size_rcons size_mkseq in Hi ;
  apply lt_n_Sm_le, le_S_n in Hi.
  split.
  rewrite ?nth_rcons size_mkseq.
  have H : ssrnat.leq (S i) (S n) = true.
    apply le_n_S in Hi ;
    elim: (S i) (S n) Hi => //= j IH ;
    case => //= [ | m] Hi.
    by apply le_Sn_O in Hi.
    apply IH ; by apply le_S_n.
  case: (ssrnat.leq (S i) (S n)) (H) => // _.
  case H0 : (ssrnat.leq (S (S i)) (S n)) => //.
  rewrite ?nth_mkseq //.
  rewrite S_INR Rminus_lt_0 ; ring_simplify.
  by apply eps.
  apply (f_equal negb) in H0 ; simpl in H0.
  rewrite -ssrnat.leqNgt in H0.
  case H1 : (@eqtype.eq_op ssrnat.nat_eqType (S i) (S n)) => //.
  rewrite ssrnat.eqSS /= in H1.
  replace i with n.
  rewrite nth_mkseq => //.
  move: Hdec ; rewrite /n /nfloor.
  case: nfloor_ex => {n Hn l Hi H H0 H1} n Hn /= Hdec.
  rewrite Rplus_comm ; apply Rlt_minus_r.
  apply Rlt_div_r.
  by apply eps.
  case: Hn => Hn _ ; case: Hn => // Hn.
  elim: n i H1 {Hi H H0 l Hdec} => [ | n IH] ;
  case => [ | i] // H.
  apply f_equal, IH ; intuition.
  by rewrite ssrnat.eqn_leq H H0 in H1.

  rewrite ?nth_rcons size_mkseq.
  have H : ssrnat.leq (S i) (S n) = true.
    apply le_n_S in Hi ;
    elim: (S i) (S n) Hi => //= j IH ;
    case => //= [ | m] Hi.
    by apply le_Sn_O in Hi.
    apply IH ; by apply le_S_n.
  case: (ssrnat.leq (S i) (S n)) (H) => // _.
  case H0 : (ssrnat.leq (S (S i)) (S n)) => //.
  rewrite ?nth_mkseq //.
  rewrite S_INR Rminus_le_0 ; ring_simplify.
  by apply Rle_refl.
  apply (f_equal negb) in H0 ; simpl in H0.
  rewrite -ssrnat.leqNgt in H0.
  case H1 : (@eqtype.eq_op ssrnat.nat_eqType (S i) (S n)) => //.
  rewrite ssrnat.eqSS /= in H1.
  replace i with n.
  rewrite nth_mkseq => //.
  move: Hdec ;
  rewrite /n /nfloor.
  case: nfloor_ex => {n Hn l Hi H H0 H1} n Hn /= Hdec.
  rewrite Rplus_assoc Rplus_comm ; apply Rle_minus_l.
  replace (INR n * eps + eps) with ((INR n + 1) * eps) by ring.
  apply Rle_div_l.
  by apply eps.
  by apply Rlt_le, Hn.
  elim: n i H1 {Hi H H0 l Hdec} => [ | n IH] ;
  case => [ | i] // H.
  apply f_equal, IH ; intuition.
  by rewrite ssrnat.eqn_leq H H0 in H1.
  apply Rdiv_le_0_compat.
  by apply Rminus_le_0 in Hab.
  by apply eps.
Qed.

Lemma interval_finite_subdiv_between (a b : R) (eps : posreal) (Hab : a <= b) :
  let l := proj1_sig (interval_finite_subdiv a b eps Hab) in
  forall i, (i < size l)%nat -> a <= nth 0 l i <= b.
Proof.
  case: interval_finite_subdiv => l Hl /= i Hi.
  case: Hl => <- ; case => <- Hl.
  move: (fun i Hi => proj1 (Hl i Hi)) => {Hl} Hl.
  rewrite -nth0 (last_nth 0).

  suff : forall n m, (n <= m)%nat -> (m < size l)%nat
    -> nth 0 l n <= nth 0 l m.
  move => {Hl} Hl ; split.
  apply Hl ; by intuition.
  case: l Hi Hl => /= [ | x0 l] Hi Hl.
  by apply lt_n_O in Hi.
  apply Hl ; by intuition.

  elim: l Hl {i Hi} => [ | x0 l IH] Hl n m Hnm Hm.
  by apply lt_n_O in Hm.
  case: n m Hnm Hm => [ | n] m //= Hnm Hm.
  clear Hnm ; elim: m Hm => {IH} /= [ | m IH] Hm.
  by apply Rle_refl.
  apply Rle_trans with (nth 0 (x0 :: l) m).
  apply IH ; intuition.
  by apply Rlt_le, Hl.
  case: m Hnm Hm => /= [ | m] Hnm Hm.
  by apply le_Sn_O in Hnm.
  apply IH ; try by intuition.
  move => i Hi.
  apply (Hl (S i)).
  by apply lt_n_S.
Qed.

(** Notations *)
Lemma SSR_leq (n m : nat) : is_true (ssrnat.leq n m) <-> (n <= m)%nat.
Proof.
  set H := (@ssrnat.leP n m) ; case: H => H //=.
Qed.
Lemma SSR_minus (n m : nat) : ssrnat.subn n m = (n - m)%nat.
Proof.
  elim: m n => //.
Qed.
(** rcons *)
Lemma rcons_ind {T : Type} (P : seq T -> Type) :
  P [::] -> (forall (s : seq T) (t : T), P s -> P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 Hr s ; move: (refl_equal (size s)).
  move: {1}(size s) => n ; elim: n s => // [| n IH] s Hn ;
  case: s Hn => [| h s] Hn //.
  have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ;
    [| case => s0 [t0 H]].
    elim: (s) (h) => {s h Hn IH} [| h s IH] h0.
      exists [::] ; by exists h0.
    case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ;
    by rewrite rcons_cons -H.
  rewrite H ; apply Hr, IH, eq_add_S ; by rewrite -(size_rcons s0 t0) -H.
Qed.
Lemma rcons_dec {T : Type} (P : seq T -> Type) :
  (P [::]) -> (forall s t, P (rcons s t)) -> forall s, P s.
Proof.
  move => H0 Hr ; case => [| h s] //.
  have: ({s0 : _&{ t0 | h::s = rcons s0 t0}}) ;
    [| case => s0 [t0 H]].
    elim: s h => [| h s IH] h0.
      exists [::] ; by exists h0.
    case: (IH h) => s0 [t0 H] ; exists (h0::s0) ; exists t0 ;
    by rewrite rcons_cons -H.
  by rewrite H.
Qed.
Lemma size_rcons_pos {T : Type} (s : seq T) (t : T) : (0 < size (rcons s t))%nat.
Proof.
  rewrite size_rcons /= ; apply lt_O_Sn.
Qed.

Lemma foldr_rcons {T T0 : Type} : forall (f : T0 -> T -> T) x0 s t,
  foldr f x0 (rcons s t) = foldr f (f t x0) s.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.
Lemma foldl_rcons {T T0 : Type} : forall (f : T -> T0 -> T) x0 s t,
  foldl f x0 (rcons s t) = f (foldl f x0 s) t.
Proof.
  move => f x0 s ; elim: s x0 => //= t s IH x0 t0 ;
  by rewrite IH.
Qed.

(* head, last, behead and belast *)
Lemma head_rcons {T : Type} (x0 : T) (s : seq T) (t : T) : head x0 (rcons s t) = head t s.
Proof.
  case: s x0 t => //.
Qed.
Lemma behead_rcons {T : Type} (s : seq T) (t : T) :
  (0 < size s)%nat ->  behead (rcons s t) = rcons (behead s) t.
Proof.
  case: s t => // t Hi ; contradict Hi ; apply lt_n_O.
Qed.
Definition belast {T : Type} (s : seq T) :=
  match s with
    | [::] => [::]
    | h :: s => belast h s
  end.
Lemma behead_rev {T : Type} (s : seq T) : behead (rev s) = rev (belast s).
Proof.
  case: s => // t s ; elim: s t => // t s IHs t0.
  rewrite rev_cons behead_rcons ?IHs ?size_rev -?rev_cons //= ; by apply lt_0_Sn.
Qed.

Lemma pairmap_rcons {T T0 : Type} (f : T -> T -> T0) (s : seq T) h0 h x0 :
  pairmap f x0 (rcons (rcons s h0) h) = rcons (pairmap f x0 (rcons s h0)) (f h0 h).
Proof.
  elim: s x0 h h0 => [| h1 s IH] x0 h h0 //= ; by rewrite IH.
Qed.
Lemma map_pairmap {T T0 T1 : Type} (f : T0 -> T1) (g : T -> T -> T0) (s : seq T) (x0 : T) :
  map f (pairmap g x0 s) = pairmap (fun x y => f (g x y)) x0 s.
Proof.
  elim: s x0 => [| h s IH] x0 //=.
  by rewrite IH.
Qed.
Lemma pairmap_map {T T0 T1 : Type} (f : T0 -> T0 -> T1) (g : T -> T0) (s : seq T) (x0 : T) :
  pairmap f (g x0) (map g s) = pairmap (fun x y => f (g x) (g y)) x0 s.
Proof.
  elim: s x0 => [| h s IH] x0 //=.
  by rewrite IH.
Qed.
(** zip and unzip *)
Lemma size_unzip1 {T T0 : Type} (s : seq (T * T0)) : size (unzip1 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma size_unzip2 {T T0 : Type} (s : seq (T * T0)) : size (unzip2 s) = size s.
Proof.
  by elim: s => //= _ s0 ->.
Qed.
Lemma zip_cons {S T : Type} hs ht (s : seq S) (t : seq T) :
  zip (hs :: s) (ht :: t) = (hs,ht) :: zip s t.
Proof.
  by [].
Qed.
Lemma zip_rcons {S T : Type} (s : seq S) (t : seq T) hs ht : size s = size t ->
  zip (rcons s hs) (rcons t ht) = rcons (zip s t) (hs,ht).
Proof.
  elim: s t hs ht => [| hs s IHs] ; case => //= ht t hs' ht' Hs.
  rewrite IHs => // ; by apply eq_add_S.
Qed.
Lemma unzip1_rcons {S T : Type} (s : seq (S*T)) (h : S*T) :
  unzip1 (rcons s h) = rcons (unzip1 s) (fst h).
Proof.
  elim: s => [ | h0 s IH] //= ; by rewrite IH.
Qed.
Lemma unzip2_rcons {S T : Type} (s : seq (S*T)) (h : S*T) :
  unzip2 (rcons s h) = rcons (unzip2 s) (snd h).
Proof.
  elim: s => [ | h0 s IH] //= ; by rewrite IH.
Qed.
Lemma unzip1_belast {S T : Type} (s : seq (S*T)) :
  unzip1 (belast s) = belast (unzip1 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip2_belast {S T : Type} (s : seq (S*T)) :
  unzip2 (belast s) = belast (unzip2 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip1_behead {S T : Type} (s : seq (S*T)) :
  unzip1 (behead s) = behead (unzip1 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip2_behead {S T : Type} (s : seq (S*T)) :
  unzip2 (behead s) = behead (unzip2 s).
Proof.
  elim: s => //= h0 ; case => //= h1 s -> //.
Qed.
Lemma unzip1_fst {S T : Type} (s : seq (S*T)) :
  unzip1 s = map (@fst S T) s.
Proof.
  by elim: s.
Qed.
Lemma unzip2_snd {S T : Type} (s : seq (S*T)) :
  unzip2 s = map (@snd S T) s.
Proof.
  by elim: s.
Qed.
Lemma size_belast' {T : Type} (s : seq T) :
  size (belast s) = Peano.pred (size s).
Proof.
  case: s => /= [ | x0 s] //.
  by rewrite size_belast.
Qed.
Lemma head_map {T1 T2 : Type} (f : T1 -> T2) (s : seq T1) (x : T1) :
  head (f x) (map f s) = f (head x s).
Proof.
  by case: s.
Qed.

(** * Operations on the Riemann integral *)

Lemma StepFun_bound {a b : R} (f : StepFun a b) :
  exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  case: f => /= f [lx [ly [Hsort [Hhead [Hlast [Hsize Hval]]]]]];
  rename a into a0 ; rename b into b0 ; set a := Rmin a0 b0 ; set b := Rmax a0 b0 ;
  set Rl_max := fun x0 => fix f l := match l with
    | RList.nil => x0
    | RList.cons h t => Rmax h (f t)
  end ;
  set f_lx := (fix app l := match l with
    | RList.nil => RList.nil
    | RList.cons h t => RList.cons (f h) (app t)
  end) lx ;
  set M_f_lx := Rl_max (f 0) f_lx ;
  set M_ly := Rl_max 0 ly.
  exists (Rmax M_f_lx M_ly) => x [Hx Hx'].
  rewrite /M_f_lx /f_lx ;
  case: lx Hsort Hhead Hlast Hsize Hval {f_lx M_f_lx}.
(* lx = [::] *)
  move => _ _ _ H ; contradict H ; apply O_S.
  move => h l ; case: l h.
(* lx = [:: h] *)
  move => h _ Ha Hb _ _ ; simpl in Ha, Hb.
  rewrite /a -Ha in Hx ; rewrite /b -Hb in Hx'.
  rewrite (Rle_antisym _ _ Hx Hx') /= ; apply Rle_trans with (2 := RmaxLess1 _ _) ;
  apply RmaxLess1.
(* lx = [:: h,h'::l] *)
  move => h l h' Hsort Hhead Hlast Hsize Hval.
  apply Rle_lt_or_eq_dec in Hx' ; case: Hx' => Hx'.
  have H : exists i : nat, (i < S (Rlength l))%nat /\
    (pos_Rl (RList.cons h' (RList.cons h l)) i) <= x
    < (pos_Rl (RList.cons h' (RList.cons h l)) (S i)).
    rewrite /a -Hhead in Hx ; rewrite /b -Hlast in Hx'.
    elim: l h' h Hx Hx' Hsort {Hhead Hlast Hsize Hval} => [| h'' l IH] h' h Hx Hx' Hsort ; simpl in Hx, Hsort.
    case: (Rlt_le_dec x h) => H.
    exists O ; intuition.
    exists O => /= ; intuition.
    case: (Rlt_le_dec x h) => H.
    exists O => /= ; intuition.
    have H0 : ordered_Rlist (RList.cons h (RList.cons h'' l)).
    move => i Hi ; apply (Hsort (S i)) => /= ; apply lt_n_S, Hi.
    case: (IH _ _ H Hx' H0) => {IH} i Hi.
    exists (S i) ; split.
    simpl ; apply lt_n_S, Hi => /=.
    apply Hi.
  case: H => i [Hi [Ht Ht']].
  apply Rle_lt_or_eq_dec in Ht ; case: Ht => Ht.
  rewrite (Hval i Hi x).
  apply Rle_trans with (2 := RmaxLess2 _ _).
  rewrite /M_ly ; case: (ly).
  apply Rle_refl.
  move => y ly' ; elim: ly' (i) y.
  move => i0 y ; case: i0 => //=.
  apply RmaxLess1.
  move => _; apply RmaxLess2.
  move => y ly' IH i0 y' ; case: i0.
  apply RmaxLess1.
  move => n ; apply Rle_trans with (1 := IH n y) ; apply RmaxLess2.
  split => //.
  rewrite -Ht ; apply Rle_trans with (2 := RmaxLess1 _ _).
  case: (i).
  apply RmaxLess1.
  move => n ; elim: n (h) (h') (l).
  move => h0 h'0 l0 ; apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  move => n IH h0 h'0 l0.
  case: l0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess2.
  move => h''0 l0 ; apply Rle_trans with (1 := IH h''0 h0 l0), RmaxLess2.
  rewrite Hx' /b -Hlast.
  apply Rle_trans with (2 := RmaxLess1 _ _).
  elim: (l) (h') (h) => [| h''0 l0 IH] h'0 h0.
  apply Rle_trans with (2 := RmaxLess2 _ _), RmaxLess1.
  apply Rle_trans with (1 := IH h0 h''0), RmaxLess2.
Qed.

Lemma Riemann_integrable_bound (f : R -> R) (a b : R) :
  Riemann_integrable f a b -> exists s : R, forall x, Rmin a b <= x <= Rmax a b -> f x <= s.
Proof.
  move => pr ;
  case (pr (mkposreal _ Rlt_0_1)) => {pr} phi [psi [pr _]] ;
  case: (StepFun_bound phi) => M_phi H_phi ;
  case: (StepFun_bound psi) => M_psi H_psi ;
  exists (M_psi + M_phi) => x Hx.
  apply Rle_trans with (2 := Rplus_le_compat _ _ _ _ (H_psi _ Hx) (H_phi _ Hx)).
  have: (f x = (f x - phi x) + phi x) ; first by ring.
  move => -> ; apply Rplus_le_compat_r, Rle_trans with (1 := Rle_abs _), pr, Hx.
Qed.

(** Extensionality *)

Lemma Riemann_integrable_ext : forall (f g : R -> R) (a b : R),
  (forall x, Rmin a b <= x <= Rmax a b -> f x = g x)
    -> Riemann_integrable f a b -> Riemann_integrable g a b.
Proof.
  intros f g a b Heq pr_f.
  intro eps.
  elim (pr_f eps) ; clear pr_f ; intros phi (psi, pr_f).
  exists phi.
  exists psi.
  split ; intros.
  rewrite <- (Heq t H).
  apply (proj1 pr_f t H).
  apply pr_f.
Qed.

Lemma RiemannInt_ext : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (Heq : forall x, Rmin a b <= x <= Rmax a b -> f x = g x),
    RiemannInt pr_f = RiemannInt pr_g.
Proof.
  intros.
  destruct (Rle_lt_dec a b).
  apply RiemannInt_P18.
  apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_left _ _ r).
  apply Rlt_le ; apply H.
  rewrite (Rmax_right _ _ r).
  apply Rlt_le ; apply H.
  rewrite (RiemannInt_P8 pr_f (RiemannInt_P1 pr_f)).
  rewrite (RiemannInt_P8 pr_g (RiemannInt_P1 pr_g)).
  apply Ropp_eq_compat.
  apply RiemannInt_P18.
  apply Rlt_le ; apply r.
  intros.
  apply Heq.
  split.
  rewrite (Rmin_right _ _ (Rlt_le _ _ r)).
  apply Rlt_le ; apply H.
  rewrite (Rmax_left _ _ (Rlt_le _ _ r)).
  apply Rlt_le ; apply H.
Qed.

(** Constant function *)

Lemma Riemann_integrable_const : forall (c a b : R),
  Riemann_integrable (fun x => c) a b.
Proof.
  intros.
  apply RiemannInt_P14.
Qed.

Lemma RiemannInt_const : forall (c a b : R) (pr : Riemann_integrable (fun x => c) a b),
  RiemannInt pr = c * (b-a).
Proof.
  intros.
  apply RiemannInt_P15.
Qed.

(** Addition *)

Lemma Riemann_integrable_plus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x + g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_ext (fun x => f x + 1 * g x)).
  intros ; ring.
  apply (RiemannInt_P10 1 pr_f pr_g).
Qed.

Lemma RiemannInt_plus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x + g x) a b),
  RiemannInt pr = RiemannInt pr_f + RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  rewrite <- (RiemannInt_P13 pr_f pr_g (RiemannInt_P10 1 pr_f pr_g)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Subtraction *)

Lemma Riemann_integrable_minus : forall (f g : R -> R) (a b : R),
  Riemann_integrable f a b -> Riemann_integrable g a b ->
    Riemann_integrable (fun x => f x - g x) a b.
Proof.
  intros f g a b pr_f pr_g.
  apply (Riemann_integrable_ext (fun x => f x + (-1) * g x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) pr_f pr_g).
Qed.

Lemma RiemannInt_minus : forall (f g : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b) (pr_g : Riemann_integrable g a b)
  (pr : Riemann_integrable (fun x => f x - g x) a b),
  RiemannInt pr = RiemannInt pr_f - RiemannInt pr_g.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_g)).
  unfold Rminus. rewrite <- Ropp_mult_distr_l_reverse.
  rewrite -(RiemannInt_P13 pr_f pr_g (RiemannInt_P10 (-1) pr_f pr_g)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Opposite *)

Lemma Riemann_integrable_opp : forall (f : R -> R) (a b : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => - f x) a b.
Proof.
  intros f a b pr_f.
  apply (Riemann_integrable_ext (fun x => 0 + (-1) * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (-1) (Riemann_integrable_const _ _ _) pr_f).
Qed.

Lemma RiemannInt_opp : forall (f : R -> R) (a b : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => - f x) a b),
  RiemannInt pr = - RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rmult_1_l (RiemannInt pr_f)).
  rewrite <- Ropp_mult_distr_l_reverse.
  rewrite -(Rplus_0_l (-1 * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (-1) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** Multiplication by a scalar *)

Lemma Riemann_integrable_scal : forall (f : R -> R) (a b c : R),
  Riemann_integrable f a b ->
    Riemann_integrable (fun x => c * f x) a b.
Proof.
  intros f a b c pr_f.
  apply (Riemann_integrable_ext (fun x => 0 + c * f x)).
  intros ; ring.
  apply (RiemannInt_P10 (c) (Riemann_integrable_const _ _ _) pr_f).
Qed.

Lemma RiemannInt_scal : forall (f : R -> R) (a b c : R)
  (pr_f : Riemann_integrable f a b)
  (pr : Riemann_integrable (fun x => c * f x) a b),
  RiemannInt pr = c * RiemannInt pr_f.
Proof.
  intros.
  rewrite <- (Rplus_0_l (c * RiemannInt pr_f)).
  assert (0 = RiemannInt (Riemann_integrable_const 0 a b)).
    rewrite RiemannInt_const.
    ring.
    rewrite H ; clear H.
  rewrite <- (RiemannInt_P13 (Riemann_integrable_const 0 _ _) pr_f (RiemannInt_P10 (c) (Riemann_integrable_const 0 a b) pr_f)).
  apply RiemannInt_ext.
  intros ; ring.
Qed.

(** * Natural logarithm *)

Lemma ln_pow x n : 0 < x -> ln (x^n) = INR n * ln x.
  intro Hx ;
  induction n as [ | n IH].
  rewrite pow_O ln_1 ; simpl ; ring.
  rewrite S_INR ; simpl ; rewrite ln_mult ; try intuition.
  rewrite IH ; ring.
Qed.

Lemma ln_le x y : 0 < x -> x <= y -> ln x <= ln y.
Proof.
  intros Hx Hxy ; destruct Hxy.
  left ; apply ln_increasing.
  exact Hx.
  exact H.
  rewrite H ; exact (Rle_refl _).
Qed.

Lemma ln_div x y : 0 < x -> 0 < y -> ln (x / y) = ln x - ln y.
Proof.
  intros Hx Hy ; unfold Rdiv.
  rewrite ln_mult.
  rewrite ln_Rinv.
  ring.
  exact Hy.
  exact Hx.
  apply Rinv_0_lt_compat ; exact Hy.
Qed.

(** * Other *)

Lemma derivable_pt_lim_atan :
  forall x, derivable_pt_lim atan x (/(1 + x^2)).
Proof.
intros x.
apply derive_pt_eq_1 with (derivable_pt_atan x).
replace (x ^ 2) with (x * x) by ring.
rewrite -(Rmult_1_l (Rinv _)).
apply derive_pt_atan.
Qed.
