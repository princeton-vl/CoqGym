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
Require Import division.

Unset Standard Proposition Elimination Names.

(** definition of square *)
Definition square (x:nat) := x*x.

(** (x*y)^2 = x^2*y^2 *)
Lemma square_mult_lemma : forall (a b:nat),(square (a*b))=((square a)*(square b)).
  unfold square.
  intros.
  ring.
Qed.

(** we now generalize the theorem to the nth-root *)
Fixpoint power (x n:nat) {struct n} : nat :=
  match n with
    O => 1
    | (S n) => (x*(power x n))
  end.

Lemma power_mult_lemma1 : forall (n x y:nat),(power (x*y) n)=(power x n)*(power y n).
  induction n;simpl;trivial.
  intros;rewrite (IHn x y);ring.
Qed.

Lemma power_plus_lemma1 : forall (n m x:nat),(power x (n+m))=(power x n)*(power x m).
  induction n;simpl;intros.
  auto with arith.
  rewrite IHn;ring.
Qed.

Lemma power_divides_lemma1 : forall (n x:nat),(0<n)->(divides (power x n) x).
  induction n;simpl;intros.
  inversion H.
  exists (power x n);trivial.
Qed.

Lemma power_power_lemma1 : forall (n m x:nat),(power (power x n) m)=(power x (n*m)).
  induction n;simpl;intros.
  induction m;simpl;auto with arith.
  rewrite IHm;ring.
  rewrite power_mult_lemma1;rewrite IHn;rewrite <- power_plus_lemma1;trivial.
Qed.

Lemma power_zero : forall (n x:nat),(power x n)=O->x=O.
  induction n;simpl;intros.
  discriminate.
  case (mult_lemma2 x (power x n) H);auto.
Qed.

(** if 1<p and 0<m then p^m>1 *)
Lemma power_lt : forall (p m:nat),(1<p)->(0<m)->1<(power p m).
  induction m;simpl;try omega;intros.
  destruct m;simpl;try omega.
  simpl in IHm.
  assert (1 < p*(power p m)).
  apply IHm;auto with arith.
  rewrite mult_comm.
  apply lt_trans with (1*p);try omega.
  apply mult_lt_compat_r;try omega.
Qed.

(** 1^n = 1 *)
Lemma power_one : forall (n:nat),(power 1 n)=1.
  induction n;simpl;trivial.
  rewrite IHn;ring.
Qed.

(** if x>1 and x^m | x^n then m<=n *)
Lemma power_divides_power : forall (x n m:nat),(x>1)->(divides (power x n) (power x m))->(m<=n).
  intros.
  case (le_lt_dec m n);trivial.
  intro.
  generalize (le_plus_minus n m);intro.
  rewrite H1 in H0;try omega.
  elim H0;intro q;rewrite power_plus_lemma1;intro.
  assert (1=(power x (m-n))*q).
  apply mult_lemma6 with (power x n).
  intro;generalize (power_zero n x H3);omega.
  rewrite mult_assoc;rewrite <- H2;ring.
  symmetry in H3;elim (mult_lemma5 (power x (m-n)) q H3);intros.
  case (eq_nat_dec (m-n) 0);intro;try omega.
  assert (x=1);try omega.
  apply divides_antisym;[apply one_min_div | rewrite <- H4;apply power_divides_lemma1;omega].
Qed.

