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
Require Import Rcomplements.
Require Import List Omega.
Require Import mathcomp.ssreflect.seq mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype.

(** This file describes iterators on lists. This is mainly used for
Riemannn sums. *)

Section Iter.

Context {I T : Type}.

Context (op : T -> T -> T).
Context (x0 : T).
Context (neutral_l : forall x, op x0 x = x).
Context (neutral_r : forall x, op x x0 = x).
Context (assoc : forall x y z, op x (op y z) = op (op x y) z).

Fixpoint iter (l : list I) (f : I -> T) :=
  match l with
  | nil => x0
  | cons h l' => op (f h) (iter l' f)
  end.

Definition iter' (l : list I) (f : I -> T) :=
  fold_right (fun i acc => op (f i) acc) x0 l.

Lemma iter_iter' l f :
  iter l f = iter' l f.
Proof.
  elim: l => [ | h l IH] //=.
  by rewrite IH.
Qed.

Lemma iter_cat l1 l2 f :
  iter (l1 ++ l2) f = op (iter l1 f) (iter l2 f).
Proof.
  elim: l1 => [ | h1 l1 IH] /=.
  by rewrite neutral_l.
  by rewrite IH assoc.
Qed.
Lemma iter_ext l f1 f2 :
  (forall x, In x l -> f1 x = f2 x) ->
  iter l f1 = iter l f2.
Proof.
  elim: l => [ | h l IH] /= Heq.
  by [].
  rewrite IH.
  rewrite Heq //.
  by left.
  intros x Hx.
  apply Heq.
  by right.
Qed.

Lemma iter_comp (l : list I) f (g : I -> I) :
  iter l (fun x => f (g x)) = iter (map g l) f.
Proof.
  elim: l => [ | s l IH] //=.
  by rewrite IH.
Qed.

End Iter.

Lemma iter_const {I} (l : list I) (a : R) :
  iter Rplus 0 l (fun _ => a) = INR (length l) * a.
Proof.
  elim: l => /= [ | h l ->].
  by rewrite /= Rmult_0_l.
  case: (length l) => [ | n] ; simpl ; ring.
Qed.

Lemma In_mem {T : eqType} (x : T) l :
  reflect (In x l) (in_mem x (mem l)).
Proof.
apply iffP with (P := x \in l).
by case: (x \in l) => // ; constructor.

elim: l => [ | h l IH] //= E.
rewrite in_cons in E.
case/orP: E => E.
now left ; apply sym_eq ; apply / eqP.
right ; by apply IH.

elim: l => [ | h l IH] E //=.
simpl in E.
case : E => E.
rewrite E ; apply mem_head.
rewrite in_cons.
rewrite IH.
apply orbT.
by [].
Qed.

Lemma In_iota (n m k : nat) :
  (n <= m <= k)%nat <-> In m (iota n (S k - n)).
Proof.
  generalize (mem_iota n (S k - n) m).
  case: In_mem => // H H0.
  apply sym_eq in H0.
  case/andP: H0 => H0 H1.
  apply Rcomplements.SSR_leq in H0.
  apply SSR_leq in H1.
  change ssrnat.addn with Peano.plus in H1.
  split => // _.
  split => //.
  case: (le_dec n (S m)).
  intro ; omega.
  intro H2.
  rewrite not_le_minus_0 in H1 => //.
  contradict H2.
  by eapply le_trans, le_n_Sn.
  contradict H2.
  by eapply le_trans, le_n_Sn.
  change ssrnat.addn with Peano.plus in H0.
  split => // H1.
  case: H1 => /= H1 H2.
  apply sym_eq in H0.
  apply Bool.andb_false_iff in H0.
  case: H0 => //.
  move/SSR_leq: H1 ; by case: ssrnat.leq.
  rewrite -le_plus_minus ; try omega.
  move/le_n_S/SSR_leq: H2 ; by case: ssrnat.leq.
Qed.

Section Iter_nat.

Context {T : Type}.

Context (op : T -> T -> T).
Context (x0 : T).
Context (neutral_l : forall x, op x0 x = x).
Context (neutral_r : forall x, op x x0 = x).
Context (assoc : forall x y z, op x (op y z) = op (op x y) z).

Definition iter_nat (a : nat -> T) n m :=
  iter op x0 (iota n (S m - n)) a.

Lemma iter_nat_ext_loc (a b : nat -> T) (n m : nat) :
  (forall k, (n <= k <= m)%nat -> a k = b k) ->
  iter_nat a n m = iter_nat b n m.
Proof.
  intros Heq.
  apply iter_ext.
  intros k Hk.
  apply Heq.
  by apply In_iota.
Qed.

Lemma iter_nat_point a n :
  iter_nat a n n = a n.
Proof.
  unfold iter_nat.
  rewrite -minus_Sn_m // minus_diag /=.
  by apply neutral_r.
Qed.

Lemma iter_nat_Chasles a n m k :
  (n <= S m)%nat -> (m <= k)%nat ->
  iter_nat a n k = op (iter_nat a n m) (iter_nat a (S m) k).
Proof.
  intros Hnm Hmk.
  rewrite -iter_cat //.
  pattern (S m) at 2 ;
  replace (S m) with (ssrnat.addn n (S m - n)).
  rewrite -(iota_add n (S m - n)).
  apply (f_equal (fun k => iter _ _ (iota n k) _)).
  change ssrnat.addn with Peano.plus.
  omega.
  change ssrnat.addn with Peano.plus.
  omega.
Qed.

Lemma iter_nat_S a n m :
  iter_nat (fun n => a (S n)) n m = iter_nat a (S n) (S m).
Proof.
  rewrite /iter_nat iter_comp.
  apply (f_equal (fun l => iter _ _ l _)).
  rewrite MyNat.sub_succ.
  elim: (S m - n)%nat {1 3}(n) => {n m} [ | n IH] m //=.
  by rewrite IH.
Qed.

End Iter_nat.
