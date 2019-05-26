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

(** First, we show the following theorem: *)
(** if p is a prime number and gcd(p,k)=1 then sqrt(p*k) is not rational *)

(** Then, we strengthen the result to the n-th root of p^r*k *)
(** where 0 < r < n obtaining the theorem: *)
(**  if p is a prime number, gcd(p,k)=1 and 0 < r < n then the n-th root of p^r*k is not rational *)

Require Import missing.
Require Import division.
Require Import gcd.
Require Import primes.
Require Import power.

Unset Standard Proposition Elimination Names.

(** now, we show the result claimed in the header *)
Lemma sqrt_prime_irrat_aux : forall (p k a b:nat),(is_prime p)->(rel_prime p k)->(rel_prime a b)->(p*k*(square b) <> (square a)).
  intros.
  intro.
  assert (divides a p).
  apply prime_square;trivial.
  exists (k*(square b)).
  rewrite <- H2;ring.
  elim H3;intro n_a;intro.
  rewrite H4 in H2;rewrite square_mult_lemma in H2;unfold square in H2.
  assert (k*(b*b)=p*(n_a*n_a)).
  apply mult_lemma6 with p.
  intro H5;rewrite H5 in H;apply not_prime_zero;trivial.
  rewrite mult_assoc;rewrite H2;ring.
  assert (divides b p).
  apply prime_square;trivial;unfold square.
  apply gauss with k.
  apply rel_prime_sym;trivial.
  exists (n_a*n_a);trivial.
  assert (p=1).
  unfold rel_prime in H1.
  elim H1;intros.
  apply divides_antisym;try (apply one_min_div).
  apply H8;red;tauto.
  elim H;tauto.
Qed.

(** Theorem: if p is prime, p and k are relatively prime, then sqrt(p*k) is not rationnal *)
Theorem sqrt_prime_irrat : forall (p k a b:nat),(is_prime p)->(rel_prime p k)->(b<>O)->(p*k*(square b) <> (square a)).
  intros.
  generalize (gcd_is_gcd a b);intro.
  generalize (quo_is_quo a (gcd a b) (gcd_div_l (gcd a b) a b H2));intro.
  generalize (quo_is_quo b (gcd a b) (gcd_div_r (gcd a b) a b H2));intro.
  intro.
  rewrite H3 in H5.
  replace (square b) with (square (gcd a b * quo b (gcd a b) (gcd_div_r (gcd a b) a b H2))) in H5;auto.
  rewrite square_mult_lemma in H5;rewrite square_mult_lemma in H5.
  assert (p*k*(square (quo b (gcd a b) (gcd_div_r (gcd a b) a b H2)))=(square (quo a (gcd a b) (gcd_div_l (gcd a b) a b H2)))).
  apply mult_lemma6 with (square (gcd a b)).
  unfold square.
  generalize (gcd_non_zero (gcd a b) a b H1 H2);intro.
  intro;apply H6.
  case (mult_lemma2 (gcd a b) (gcd a b) H7);trivial.
  rewrite <- H5;ring.
  apply (sqrt_prime_irrat_aux p k (quo a (gcd a b) (gcd_div_l (gcd a b) a b H2)) (quo b (gcd a b) (gcd_div_r (gcd a b) a b H2)));auto.
  apply gcd_rel_prime;apply (gcd_non_zero (gcd a b) a b);trivial.
Qed.

(** if p is prime then sqrt(p) is not rationnal *)
Fact sqrt_prime : forall (p:nat),(is_prime p)->forall (a b:nat),(b<>O)->(p*(square b)<>(square a)).
  intros.
  replace p with (p*1);try (auto with arith).
  apply sqrt_prime_irrat;trivial;apply rel_prime_1.
Qed.

(** We now deduce from this theorem that sqrt(2) is not rationnal *)
(** here is it! *)
Fact sqrt_2_irrat : forall (p q:nat),(q<>O)->(2*(square q)<>(square p)).
  intros.
  apply sqrt_prime;trivial.
  apply is_prime_2.
Qed.

(** generalisation *)
Lemma nth_root_irrat_aux : forall (p k a b n r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(rel_prime a b)->((power p r)*k*(power b n) <> (power a n)).
  intros.
  intro.
  assert (divides a p).
  apply prime_power with n;trivial.
  generalize (power_divides_lemma1 r p H1);intro.
  elim H5;intro q;intros.
  rewrite H6 in H4.
  rewrite <- H4;exists (q*k*(power b n));ring.
  assert (divides b p).
  elim H5;intro q;intros.
  rewrite H6 in H4.
  rewrite power_mult_lemma1 in H4.
  assert ((power p n)=(power p (r+(n-r)))).
  rewrite <- le_plus_minus;try (auto with arith).
  rewrite H7 in H4;rewrite power_plus_lemma1 in H4.
  assert ((power p r)<>O).
  intro.
  apply not_prime_zero.
  assert (p=O).
  apply power_zero with r;trivial.
  rewrite H9 in H;trivial.
  rewrite <- mult_assoc in H4;rewrite <- mult_assoc in H4;generalize (mult_lemma6 (k*(power b n)) ((power p (n-r))*(power q n)) (power p r) H8 H4);intro.
  assert (divides (power p (n-r)) p).
  apply power_divides_lemma1;apply minus_lt_lemma1;trivial.
  apply prime_power with n;trivial.
  apply gauss with k;try (apply rel_prime_sym;trivial).
  rewrite H9;apply divides_mult;trivial.
  elim H3;intros.
  elim H;intros.
  apply H9;apply divides_antisym;try (apply one_min_div).
  apply H8;red;tauto.
Qed.

(** generalization of the theorem: if p is a prime number, 0 < r < n and gcd(p,k)=1 then the n-th root of p^r*k is not rationnal! *)
Theorem nth_root_irrat : forall (p k a b n r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(b<>0)->((power p r)*k*(power b n) <> (power a n)).
  intros.
  intro.
  generalize (gcd_is_gcd a b);intro.
  generalize (quo_is_quo a (gcd a b) (gcd_div_l (gcd a b) a b H5));intro.
  generalize (quo_is_quo b (gcd a b) (gcd_div_r (gcd a b) a b H5));intro.
  assert ((power a n)=(power (gcd a b * quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n));try (rewrite <- H6;trivial).
  assert ((power b n)=(power (gcd a b * quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n));try (rewrite <- H7;trivial).
  rewrite power_mult_lemma1 in H8;rewrite H8 in H4.
  rewrite power_mult_lemma1 in H9;rewrite H9 in H4.
  rewrite mult_lemma7 in H4.
  assert ((power (gcd a b) n)<>O).
  intro.
  generalize (power_zero n (gcd a b) H10);intro.
  apply (gcd_non_zero (gcd a b) a b);trivial.
  generalize (mult_lemma6 (power p r * k * power (quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n) (power (quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n) (power (gcd a b) n) H10 H4).
  fold ((power p r * k * power (quo b (gcd a b) (gcd_div_r (gcd a b) a b H5)) n)<>(power (quo a (gcd a b) (gcd_div_l (gcd a b) a b H5)) n)).
  apply nth_root_irrat_aux;trivial.
  apply gcd_rel_prime;apply (gcd_non_zero (gcd a b) a b);trivial.
Qed.

(** Generalization of the previous theorem *)
Theorem nth_root_irrational : forall (p k a b n q r:nat),(is_prime p)->(rel_prime p k)->(0<r)->(r<n)->(b<>0)->((power p (q*n+r))*k*(power b n) <> (power a n)).
  intros.
  intro.
  rewrite power_plus_lemma1 in H4.
  assert (divides a (power p q)).
  apply prime_power_qn with n;try (auto with arith);try omega.
  exists ((power p r)*k*(power b n)).
  rewrite <- H4;ring.
  assert (0<n);try omega.
  elim H5;intro a';intro.
  rewrite H7 in H4.
  rewrite power_mult_lemma1 in H4;rewrite power_power_lemma1 in H4.
  assert ((power p (q*n))<>0).
  intro;apply not_prime_zero;generalize (power_zero (q*n) p H8);intro;rewrite H9 in H;trivial.
  rewrite <- (mult_assoc (power p (q*n))) in H4;rewrite <- (mult_assoc (power p (q*n))) in H4.
  generalize (mult_lemma6 (power p r*k*power b n) (power a' n) (power p (q*n)) H8 H4).
  fold (power p r * k * power b n <> power a' n).
  apply nth_root_irrat;trivial.
Qed.

(** let x and n be two numbers such that n > 0, then either the n-th root of x is a natural number of it is not rationnal *)
Theorem nth_root : forall (x n:nat),(n>0)->{y:nat | x=(power y n)}+{forall (a b:nat),(b<>0)->x*(power b n)<>(power a n)}.
  intros.
  case (is_power_m_dec x n H);intro;try tauto.
  elim s;intro p;intro.
  elim p0;intro q;intro.
  elim p1;intro r;intro.
  elim p2;intro k;intro.
  right;intros.
  assert (x=(power p (q*n+r))*k);try tauto.
  rewrite H1;apply nth_root_irrational;tauto.
Qed.
