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

Require Export Arith.
Require Export ArithRing.
Require Export Omega.

Unset Standard Proposition Elimination Names.

(** We first begin with some lemmas that relates *)
(** +, * and - that are not in the standard library *)
Lemma mult_lemma1 : forall (n m:nat),(n <> O)->(m <> 0)->(n <= n*m).
  intros.
  rewrite mult_comm.
  induction m;simpl;auto with arith.
  elim H0;trivial.
Qed.

Lemma mult_lemma2 : forall (n m:nat),(n*m = O)->(n=O)\/(m=O).
  intros.
  induction n.
  tauto.
  simpl in H.
  right.
  assert (m <= O);try omega.
  rewrite <- H.
  auto with arith.
Qed.

Lemma mult_lemma3 : forall (n m:nat),(n <> O)->(m > 1)->(n < n*m).
  intros.
  rewrite mult_comm.
  induction m.
  inversion H0.
  simpl.
  assert (O < m*n);try omega.
  inversion H0;try omega.
  assert (1 <= n);try omega.
  assert (m > 1);try omega.
  generalize (IHm H4);omega.
Qed.

Lemma mult_lemma4 : forall (n m:nat),n=n*m -> n=O \/ m=1.
  intros n m.
  case n.
  left;trivial.
  intros.
  right.
  destruct m.
  rewrite mult_comm in H.
  discriminate.
  destruct m;trivial.
  assert ((S n0)<(S n0)*(S (S m))).
  apply mult_lemma3;intros;auto with arith.
  rewrite <- H in H0.
  elim (lt_irrefl (S n0) H0).
Qed.

Lemma mult_lemma5 : forall (n m:nat),((n * m) =1)->(n=1)/\(m=1).
  induction n;simpl;intros;try discriminate.
  induction m.
  rewrite mult_comm in H.
  simpl in H;discriminate.
  assert ((S n)<=((S n)*(S m))).
  apply mult_lemma1;discriminate.
  assert (((S n)*(S m))=((S m)+n*(S m))).
  reflexivity.
  rewrite H1 in H0.
  rewrite H in H0.
  assert ((S n)=1).
  omega.
  split;trivial.
  inversion H2.
  rewrite H4 in H.
  simpl in H.
  omega.
Qed.

Lemma plus_minus_lemma1 : forall (y x:nat),(x+y-y=x).
  induction y;intros;rewrite plus_comm;simpl.
  auto with arith.
  rewrite plus_comm.
  apply IHy.
Qed.

Lemma mult_minus_lemma1 : forall (a n:nat),a*n-n = (a-1)*n.
  intros.
  induction a.
  simpl.
  trivial.
  replace (S a*n) with (n+a*n);try (auto with arith).
  rewrite plus_comm.
  rewrite plus_minus_lemma1.
  simpl.
  rewrite <- minus_n_O;trivial.
Qed.

Lemma mult_lemma6 : forall (a b n:nat),(n <> O)->(n*a=n*b)->(a=b).
  induction a.
  intros;rewrite <- mult_n_O in H0; generalize (mult_lemma2 n b); intros Hl2; elim Hl2; intros; (auto || elim H ; auto).
  intros b n H.
  rewrite mult_comm;simpl;rewrite mult_comm;intro.
  assert (n*a = n*b-n).
  apply plus_minus;auto.
  assert (a*n=(b-1)*n).
  rewrite <- mult_minus_lemma1;rewrite mult_comm;rewrite (mult_comm b n);trivial.
  assert (a=(b-1)).
  apply (IHa (b-1) n);trivial.
  rewrite mult_comm;rewrite (mult_comm n (b-1));trivial.
  destruct b;simpl in H3.
  rewrite H3 in H0;rewrite (mult_comm n 0) in H0;rewrite plus_comm in H0;simpl in H0;elim H;trivial.
  rewrite <- minus_n_O in H3;auto.
Qed.

Lemma mult_lemma7 : forall (x y z t:nat),x*y*(z*t)=z*(x*y*t).
  intros.
  ring.
Qed.

Lemma minus_lemma1 : forall (a b:nat),(S a-S b)<S a.
  intros.
  omega.
Qed.

Lemma minus_lemma2 : forall (n m:nat),(n<=m)->(n-m=O).
  intros.
  omega.
Qed.

Lemma mult_minus_lemma2 : forall (x y z:nat),(x*(y-z))=(x*y-x*z).
  intros.
  case (le_lt_dec y z);intro.
  rewrite (minus_lemma2 y z l);rewrite mult_comm;simpl;rewrite minus_lemma2;trivial;auto with arith.
  assert (y=z+(y-z)).
  rewrite <- (le_plus_minus z y);try (auto with arith).
  replace (x*y) with (x*(z+(y-z))).
  rewrite mult_plus_distr_l;rewrite minus_plus;trivial.
  rewrite <- H;trivial.
Qed.

Lemma plus_minus_lemma2 : forall (x y z:nat),(y<=x)->(x-y+z)=(x+z-y).
  intros.
  rewrite (le_plus_minus y x);try (auto with arith).
  rewrite minus_plus;rewrite <- plus_assoc;rewrite minus_plus;trivial.
Qed.

Lemma minus_minus_lemma1 : forall (x y z:nat),(z<=y)->(x-(y-z))=(x+z-y).
  intros.
  rewrite (le_plus_minus z y);trivial.
  rewrite minus_plus;rewrite plus_comm;rewrite <- minus_plus_simpl_l_reverse;trivial.
Qed.

Lemma minus_minus_lemma2 : forall (x y z:nat),(x-y-z)=(x-(y+z)).
  induction x;simpl;trivial.
  intros.
  case y;simpl;trivial.
Qed.

Lemma minus_lt_lemma1 : forall (b a:nat),(a<b)->(0<b-a).
  intros.
  omega.
Qed.
