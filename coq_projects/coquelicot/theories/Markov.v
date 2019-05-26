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

Require Import RIneq Rcomplements Omega.

(** This file proves the Limited Principle of Omniscience: given a
decidable property P on [nat], either P never holds or we can construct
a witness for which P holds. Several variants are given. *)

Open Scope R_scope.

(** * Limited Principle of Omniscience *)

Theorem LPO_min :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n /\ forall i, (i < n)%nat -> ~ P i} + {forall n, ~ P n}.
Proof.
assert (Hi: forall n, 0 < INR n + 1).
  intros N.
  rewrite <- S_INR.
  apply lt_0_INR.
  apply lt_0_Sn.
intros P HP.
set (E y := exists n, (P n /\ y = / (INR n + 1)) \/ (~ P n /\ y = 0)).
assert (HE: forall n, P n -> E (/ (INR n + 1))).
  intros n Pn.
  exists n.
  left.
  now split.
assert (BE: is_upper_bound E 1).
  intros x [y [[_ ->]|[_ ->]]].
  rewrite <- Rinv_1 at 2.
  apply Rinv_le_contravar.
  exact Rlt_0_1.
  rewrite <- S_INR.
  apply (le_INR 1), le_n_S, le_0_n.
  exact Rle_0_1.
destruct (completeness E) as [l [ub lub]].
  now exists 1.
  destruct (HP O) as [H0|H0].
  exists 1.
  exists O.
  left.
  apply (conj H0).
  rewrite Rplus_0_l.
  apply sym_eq, Rinv_1.
  exists 0.
  exists O.
  right.
  now split.
destruct (Rle_lt_dec l 0) as [Hl|Hl].
  right.
  intros n Pn.
  apply Rle_not_lt with (1 := Hl).
  apply Rlt_le_trans with (/ (INR n + 1)).
  now apply Rinv_0_lt_compat.
  apply ub.
  now apply HE.
left.
set (N := Zabs_nat (up (/l) - 2)).
exists N.
assert (HN: INR N + 1 = IZR (up (/ l)) - 1).
  unfold N.
  rewrite INR_IZR_INZ.
  rewrite inj_Zabs_nat.
  replace (IZR (up (/ l)) - 1) with (IZR (up (/ l) - 2) + 1).
  apply (f_equal (fun v => IZR v + 1)).
  apply Zabs_eq.
  apply Zle_minus_le_0.
  apply (Zlt_le_succ 1).
  apply lt_IZR.
  apply Rle_lt_trans with (/l).
  apply Rmult_le_reg_r with (1 := Hl).
  rewrite Rmult_1_l, Rinv_l by now apply Rgt_not_eq.
  apply lub.
  exact BE.
  apply archimed.
  rewrite minus_IZR.
  simpl.
  ring.
assert (H: forall i, (i < N)%nat -> ~ P i).
  intros i HiN Pi.
  unfold is_upper_bound in ub.
  refine (Rle_not_lt _ _ (ub (/ (INR i + 1)) _) _).
  now apply HE.
  rewrite <- (Rinv_involutive l) by now apply Rgt_not_eq.
  apply Rinv_1_lt_contravar.
  rewrite <- S_INR.
  apply (le_INR 1).
  apply le_n_S.
  apply le_0_n.
  apply Rlt_le_trans with (INR N + 1).
  apply Rplus_lt_compat_r.
  now apply lt_INR.
  rewrite HN.
  apply Rplus_le_reg_r with (-/l + 1).
  ring_simplify.
  apply archimed.
destruct (HP N) as [PN|PN].
  now split.
elimtype False.
refine (Rle_not_lt _ _ (lub (/ (INR (S N) + 1)) _) _).
  intros x [y [[Py ->]|[_ ->]]].
  destruct (eq_nat_dec y N) as [HyN|HyN].
  elim PN.
  now rewrite <- HyN.
  apply Rinv_le_contravar.
  apply Hi.
  apply Rplus_le_compat_r.
  apply Rnot_lt_le.
  intros Hy.
  refine (H _ _ Py).
  apply INR_lt in Hy.
  clear -Hy HyN.
  omega.
  now apply Rlt_le, Rinv_0_lt_compat.
rewrite S_INR, HN.
ring_simplify (IZR (up (/ l)) - 1 + 1).
rewrite <- (Rinv_involutive l) at 2 by now apply Rgt_not_eq.
apply Rinv_1_lt_contravar.
rewrite <- Rinv_1.
apply Rinv_le_contravar.
exact Hl.
now apply lub.
apply archimed.
Qed.

Theorem LPO :
  forall P : nat -> Prop, (forall n, P n \/ ~ P n) ->
  {n : nat | P n} + {forall n, ~ P n}.
Proof.
intros P HP.
destruct (LPO_min P HP) as [[n [Pn _]]|Pn].
left.
now exists n.
now right.
Qed.

Lemma LPO_bool :
  forall f : nat -> bool,
  {n | f n = true} + {forall n, f n = false}.
Proof.
intros f.
destruct (LPO (fun n => f n = true)) as [H|H].
simpl.
intros n.
case (f n).
now left.
now right.
now left.
right.
intros n.
now apply Bool.not_true_is_false.
Qed.

(** ** Corollaries *)

Lemma LPO_notforall : forall P : nat -> Prop, (forall n, P n \/ ~P n) ->
  (~ forall n : nat, ~ P n) -> exists n : nat, P n.
Proof.
  intros.
  destruct (LPO P H).
  destruct s as (n,H1) ; exists n ; apply H1.
  contradict H0 ; apply n.
Qed.

Lemma LPO_notnotexists : forall P : nat -> Prop, (forall n, P n \/ ~P n) ->
  ~~ (exists n : nat, P n) -> exists n : nat, P n.
Proof.
  intros.
  apply LPO_notforall.
  apply H.
  contradict H0.
  intros (n,H1).
  contradict H1 ; apply H0.
Qed.

Lemma LPO_ub_dec : forall (u : nat -> R),
  {M : R | forall n, u n <= M} + {forall M : R, exists n, M < u n}.
Proof.
  intros u.
  destruct (LPO (fun M => forall n, u n <= (INR M))) as [ [M MHM] | HM ].
  intros M.
  destruct (LPO (fun n => INR M < u n)) as [[n Hn] | Hn].
  intros n.
  destruct (Rlt_dec (INR M) (u n)) as [H|H].
  now left.
  now right.
  right ; contradict Hn.
  now apply Rle_not_lt.
  left ; intro n.
  now apply Rnot_lt_le.
  left ; now exists (INR M).
  right ; intros M.
  destruct (nfloor_ex (Rbasic_fun.Rmax 0 M)) as [m Hm].
  now apply Rbasic_fun.Rmax_l.
  specialize (HM (S m)).
  apply LPO_notforall.
  intros n.
  destruct (Rlt_dec M (u n)) as [H|H].
  now left.
  now right.
  contradict HM ; intros n.
  rewrite S_INR.
  eapply Rle_trans, Rlt_le, Hm.
  eapply Rle_trans, Rbasic_fun.Rmax_r.
  now apply Rnot_lt_le.
Qed.

(** * Excluded-middle and decidability *)

Lemma EM_dec :
  forall P : Prop, {not (not P)} + {not P}.
Proof.
intros P.
set (E := fun x => x = 0 \/ (x = 1 /\ P)).
destruct (completeness E) as [x H].
- exists 1.
  intros x [->|[-> _]].
  apply Rle_0_1.
  apply Rle_refl.
- exists 0.
  now left.
destruct (Rle_lt_dec 1 x) as [H'|H'].
- left.
  intros HP.
  elim Rle_not_lt with (1 := H').
  apply Rle_lt_trans with (2 := Rlt_0_1).
  apply H.
  intros y [->|[_ Hy]].
  apply Rle_refl.
  now elim HP.
- right.
  intros HP.
  apply Rlt_not_le with (1 := H').
  apply H.
  right.
  now split.
Qed.

Lemma EM_dec' :
  forall P : Prop, P \/ not P -> {P} + {not P}.
Proof.
intros P HP.
destruct (EM_dec P) as [H|H].
- left.
  now destruct HP.
- now right.
Qed.
