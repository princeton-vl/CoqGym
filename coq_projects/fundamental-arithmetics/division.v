(* Copyright (C) 2005-2008 Sebastien Briais *)
(* http://lamp.epfl.ch/~sbriais/ *)

(* This library is free software; you can redistribute it and/or modify *)
(* it under the terms of the GNU Lesser General Public License as *)
(* published by the Free Software Foundation; either version 2.1 of the *)
(* License, or (at your option) any later version. *)

(* This library is distributed in the hope that it will be useful, but *)
(* WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA *)
(* 02110-1301 USA *)

Require Import missing.
Require Import Wf_nat.

(** b | a if there is q such that a = b * q*)
Definition divides (a b:nat) := exists q:nat,a = (b*q).

(** 1 divides every natural number *)
Lemma one_min_div : forall (n:nat),(divides n 1).
  intros.
  red.
  exists n.
  auto with arith.
Qed.

(** 0 is divides by every natural number *)
Lemma zero_max_div : forall (n:nat),(divides O n).
  intros.
  red.
  exists O.
  auto with arith.
Qed.

(** the relation of divisibility is reflexive *)
Lemma divides_refl : forall (a:nat),(divides a a).
  intros.
  red.
  exists 1.
  auto with arith.
Qed.

(** the relation of divisibility is transitive *)
Lemma divides_trans : forall (a b c:nat),(divides a b)->(divides b c)->(divides a c).
  unfold divides.
  intros.
  elim H;intro q;intro.
  elim H0;intro q';intro.
  rewrite H2 in H1.
  exists (q' * q).
  rewrite H1.
  auto with arith.
Qed.

(** the relation of divisibility is antisymmetric *)
Lemma divides_antisym : forall (a b:nat),(divides a b)->(divides b a)->a=b.
  unfold divides.
  intros.
  elim H;intro q;intro.
  elim H0;intro q';intro.
  rewrite H2 in H1.
  assert ((a = 0) \/ (q' * q)=1).
  apply mult_lemma4.
  replace (a*(q'*q)) with (a*q'*q);try (auto with arith).
  case H3;intro.
  rewrite H4 in H2;simpl in H2;rewrite H2;trivial.
  elim (mult_lemma5 q' q H4);intros.
  rewrite H5 in H2;rewrite mult_comm in H2;simpl in H2;rewrite plus_comm in H2;simpl in H2;symmetry;trivial.
Qed.

(** corollary: forall a<>1, not(a | 1) *)
Lemma non_div_1 : forall (a:nat),(a<>1)->~(divides 1 a).
  intros.
  red.
  intro.
  apply H.
  apply divides_antisym;trivial.
  apply one_min_div.
Qed.

(** if d | a and d | b then d | (a+b) *)
Lemma divides_plus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (plus a b) d).
  unfold divides.
  intros.
  elim H;intro q;intro.
  elim H0;intro q';intro.
  exists (q+q').
  rewrite H1;rewrite H2.
  ring.
Qed.

(** if d | a then d | a*b *)
Lemma divides_mult : forall (d a b:nat),(divides a d)->(divides (a*b) d).
  unfold divides.
  intros.
  elim H;intro q;intro.
  exists (b * q).
  rewrite H0.
  ring.
Qed.

(** if d | a and d | b then d | (b-a) *)
Lemma divides_minus : forall (d a b:nat),(divides a d)->(divides b d)->(divides (b-a) d).
  unfold divides.
  intros.
  elim H;intro q;intro.
  elim H0;intro q';intro.
  rewrite H1;rewrite H2.
  exists (q'-q).
  rewrite (mult_comm d q');rewrite (mult_comm d q);rewrite (mult_comm d (q'-q));auto with arith.
Qed.

(** here we show that if b | a then it is possible to compute q such that a = b*q *)
Lemma quo_dec : forall (a b:nat),(divides a b)->{q:nat | a=b*q}.
  intros.
  apply (lt_wf_rec a (fun x:nat => (divides x b)->{q:nat | x = b*q}));trivial.
  intro.
  case n;intros.
  exists 0;auto with arith.
  elim (H0 ((S n0)-b)).
  intro q;intro.
  exists (S q).
  replace (S n0) with (b+(S n0-b)).
  rewrite p;rewrite plus_comm;auto with arith.
  symmetry.
  apply le_plus_minus.
  elim H1;intros.
  rewrite H2.
  replace (b <= b*x) with (1*b <= b*x);rewrite (mult_comm b x).
  apply mult_le_compat_r.
  destruct x;[rewrite mult_comm in H2;discriminate | auto with arith].
  simpl;auto with arith.
  destruct b.
  elim H1;simpl;intros;discriminate.
  omega.
  apply (divides_minus b b (S n0));[apply divides_refl | trivial].
Qed.

(** we can now define the quotient of a by b in case of b | a *)
Definition quo (a b:nat) (H:(divides a b)) := let (q,_):=(quo_dec a b H) in q.

(** the quotient is the quotient! *)
Lemma quo_is_quo : forall (a b:nat)(H:divides a b),a=(mult b (quo a b H)).
  intros.
  unfold quo.
  generalize (quo_dec a b H);intro;elim s;trivial.
Qed.

(** if b | a then (n*a/b) = n*(a/b) *) 
Lemma quo_mult : forall (a b:nat)(H:divides a b),forall (n:nat),(b<>O)->(quo (a*n) b (divides_mult b a n H))=n*(quo a b H).
  intros.
  generalize (quo_is_quo (a*n) b (divides_mult b a n H));intro.
  generalize (quo_is_quo a b H);intro.
  replace (a*n = b * quo (a * n) b (divides_mult b a n H)) with (b*(quo a b H)*n = b * quo (a * n) b (divides_mult b a n H)) in H1.
  symmetry;rewrite mult_comm.
  apply mult_lemma6 with b;trivial.
  rewrite mult_assoc;trivial.
  rewrite <- H2;trivial.
Qed.

