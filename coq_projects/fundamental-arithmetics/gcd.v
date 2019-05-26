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
Require Import euclide.
Require Import power.
Require Import Wf_nat.

Unset Standard Proposition Elimination Names.

(** d is a common divisor of a and b if d | a and d | b *)
Definition is_cd (d a b : nat) := (divides a d)/\(divides b d).

(** d is a greatest common divisor of a and b if it is a maximal common divisor *)
Definition is_gcd (d a b:nat) := (is_cd d a b)/\(forall (d':nat),(is_cd d' a b)->(divides d d')).

(** there is at most one gcd of a and b *)
Theorem gcd_unique : forall (d d' a b:nat),(is_gcd d a b)->(is_gcd d' a b)->d=d'.
  unfold is_gcd.
  intros.
  elim H;elim H0;intros.
  apply divides_antisym;auto.
Qed.

(** gcd(a,b) = gcd(b,a) *)
Lemma gcd_sym : forall (d a b:nat),(is_gcd d a b)->(is_gcd d b a).
  unfold is_gcd.
  intros.
  elim H;intros.
  split.
  red;red in H0;tauto.
  intros.
  apply H1.
  red;red in H2;tauto.
Qed.

(** gcd(0,a)=a *)
Lemma gcd_zero : forall (a:nat),(is_gcd a O a).
  unfold is_gcd.
  intro.
  split.
  red;split;[apply zero_max_div | apply divides_refl].
  unfold is_cd;tauto.
Qed.

(** gcd(1,a)=1 *)
Lemma gcd_one : forall (a:nat),(is_gcd 1 1 a).
  unfold is_gcd.
  intros.
  split.
  red;split;[apply divides_refl | apply one_min_div].
  unfold is_cd;tauto.
Qed.

(** if a <= b then gcd(a,b)=gcd(a,b-a) *)
Lemma gcd_minus : forall (d a b:nat),(a <= b)->((is_gcd d a b)<->(is_gcd d a (b-a))).
  intros.
  unfold is_gcd.
  split;intro.
  elim H0;intros.
  split.
  red in H1;red.
  elim H1;intros.
  split;try tauto.
  apply divides_minus;trivial.
  unfold is_cd;intros.
  apply H2;red;elim H3;intros.
  split;[tauto | rewrite (le_plus_minus a b H);apply divides_plus;trivial].
  elim H0;unfold is_cd;intros.
  split.
  split;[tauto | elim H1;intros;rewrite (le_plus_minus a b H);apply divides_plus;trivial].
  intros.
  elim H3;intros;apply H2.
  split;try (apply divides_minus);trivial.
Qed.

(** gcd(a,a) = a *)
Lemma gcd_refl : forall (a:nat),(is_gcd a a a).
  unfold is_gcd.
  intros.
  unfold is_cd.
  split;try tauto.
  split;apply divides_refl.
Qed.

(** two trivial lemmas: gcd(a,b) | a *)
Lemma gcd_div_l : forall (d a b:nat),(is_gcd d a b)->(divides a d).
  unfold is_gcd;unfold is_cd;intros;tauto.
Qed.

(** gcd(a,b) | b *)
Lemma gcd_div_r : forall (d a b:nat),(is_gcd d a b)->(divides b d).
  unfold is_gcd;unfold is_cd;intros;tauto.
Qed.

(** we now show that gcd(a,b) exists for all a and b (we even have an algorithm) *)
Definition f (x:nat*nat) := (fst x)+(snd x).

Definition R (x y:nat*nat) := (f x)<(f y).

Lemma Rwf : well_founded R.
  unfold R.
  apply (well_founded_ltof (nat*nat) f).
Qed.

(** proof of existence of gcd(a,b): it relies on the relation gcd(a,b)=gcd(a,b-a) if a<=b *)
Lemma gcd_exists_prod : forall (x:nat*nat),{d:nat | (is_gcd d (fst x) (snd x))}.
  apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => {d:nat | (is_gcd d (fst x) (snd x))})).
  unfold ltof.
  unfold f.
  intros.
  case (lt_eq_lt_dec (fst x) (snd x));intro.
  case s;intro.
  destruct (fst x).
  exists (snd x);apply gcd_zero.
  elim (H (S n,snd x-S n)).
  simpl;intro d;intro.
  exists d.
  elim (gcd_minus d (S n) (snd x));try (auto with arith).
  simpl.
  omega.
  rewrite e;exists (snd x);apply gcd_refl.
  destruct (snd x).
  exists (fst x);apply gcd_sym;apply gcd_zero.
  elim (H (S n,fst x-S n)).
  simpl;intro d;intro.
  exists d.
  apply gcd_sym.
  elim (gcd_minus d (S n) (fst x));try (auto with arith).
  simpl.
  omega.
Qed.

(** here we are: the gcd exists *)
Theorem gcd_exists : forall (a b:nat),{d:nat | (is_gcd d a b)}.
  intros.
  elim (gcd_exists_prod (a,b)).
  simpl;intro d;intro;exists d;trivial.
Qed.

(** take the first projection of the proof *)
Definition gcd (a b:nat) := let (d,_):=(gcd_exists a b) in d.

(** the gcd is the gcd! *)
Lemma gcd_is_gcd : forall (a b:nat),(is_gcd (gcd a b) a b).
  intros.
  unfold gcd.
  generalize (gcd_exists a b).
  intro;elim s;intro d;trivial.
Qed.

(** a and b are relatively prime if gcd(a,b)=1 *)
Definition rel_prime (a b:nat) := (is_gcd 1 a b). 

(** if a and b are relatively prime then so are b and a *)
Lemma rel_prime_sym : forall (a b:nat),(rel_prime a b)->(rel_prime b a).
  unfold rel_prime.
  intros;apply gcd_sym;trivial.
Qed.

(** for all a, a and 1 are relatively prime *)
Lemma rel_prime_1 : forall (a:nat),(rel_prime a 1).
  unfold rel_prime.
  intros;apply gcd_sym;apply gcd_one.
Qed.

(** we have that a/gcd(a,b) and b/gcd(a,b) are relatively prime *)
Lemma gcd_rel_prime : forall (d a b:nat)(H:(is_gcd d a b)),(d <> O)->(rel_prime (quo a d (gcd_div_l d a b H)) (quo b d (gcd_div_r d a b H))).
  unfold rel_prime.
  intros.
  generalize (quo_is_quo a d (gcd_div_l d a b H));intro.
  generalize (quo_is_quo b d (gcd_div_r d a b H));intro.
  unfold is_gcd;split;unfold is_cd.
  split;apply one_min_div.
  intros.
  elim H3;intros.
  elim H4;intro q;intro.
  elim H5;intro q';intro.
  rewrite H6 in H1.
  rewrite H7 in H2.
  assert (divides d (d*d')).
  red in H;elim H;intros.
  apply H9;red;split;[exists q;rewrite H1;ring | exists q';rewrite H2;ring].
  elim H8;intros.
  exists x.
  apply mult_lemma6 with d;trivial.
  rewrite mult_assoc;rewrite <- H9;auto with arith.
Qed.

(** if q<>0 then gcd(p,q)<>0 *)
Lemma gcd_non_zero : forall (d p q:nat),(q<>O)->(is_gcd d p q)->(d<>O).
  unfold is_gcd.
  intros.
  elim H0;intros.
  intro.
  elim H1;intros.
  elim H5;intros.
  rewrite H3 in H6;simpl in H6;auto.
Qed.

(** we now exhibit an algorithm that computes Bezout coefficient: for all a b, there is u and v such that a*u-b*v = gcd(a,b) or b*v-a*u = gcd(a,b) *)
(** the 4 lemmae gives the idea of the algorithm *)
Lemma bezout_aux1 : forall (x y u v:nat),(x<=y)->(is_gcd (u*x-v*(y-x)) x (y-x))->(is_gcd ((u+v)*x-v*y) x y).
  intros.
  elim (gcd_minus ((u+v)*x-v*y) x y H);intros.
  apply H2.
  rewrite mult_plus_distr_r;rewrite <- minus_minus_lemma1;try (auto with arith);rewrite <- mult_minus_lemma2;trivial.
Qed.

Lemma bezout_aux2 : forall (x y u v:nat),(x<=y)->(is_gcd (v*(y-x)-u*x) x (y-x))->(is_gcd (v*y-(u+v)*x) x y).
  intros.
  elim (gcd_minus (v*y-(u+v)*x) x y H);intros.
  apply H2.
  rewrite mult_plus_distr_r;rewrite plus_comm;rewrite <- minus_minus_lemma2;rewrite <- mult_minus_lemma2;trivial.
Qed.

(** Bezout coefficient *)
Lemma bezout_exists_prod : forall (x:nat*nat),{y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))}.
  apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => ({y:nat*nat | (is_gcd ((fst y)*(fst x)-(snd y)*(snd x)) (fst x) (snd x))}+{y:nat*nat | (is_gcd ((snd y)*(snd x)-(fst y)*(fst x)) (fst x) (snd x))})%type)).
  unfold ltof.
  unfold f.
  intros.
  case (lt_eq_lt_dec (fst x) (snd x));intro.
  case s;intro.
  destruct (fst x).
  right;exists (0,1);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_zero.
  elim (H (S n,snd x-S n));try (intro;simpl).
  elim a;intro y;intro.
  left;exists ((fst y)+(snd y),(snd y)).
  simpl;apply bezout_aux1;try (auto with arith).
  elim b;intro y;intro.
  right;exists ((fst y)+(snd y),(snd y)).
  simpl;apply bezout_aux2;try (auto with arith).
  simpl;omega.
  rewrite e;left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_refl.
  destruct (snd x).
  left;exists (1,0);simpl;rewrite <- minus_n_O;rewrite plus_comm;simpl;apply gcd_sym;apply gcd_zero.
  elim (H (S n,fst x-S n));try (intro;simpl).
  elim a;intro y;intro.
  right;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
  simpl;apply bezout_aux1;try (auto with arith).
  elim b;intro y;intro.
  left;exists ((snd y),(fst y)+(snd y));apply gcd_sym.
  simpl;apply bezout_aux2;try (auto with arith).
  simpl;omega.
Qed.

(** Bezout' theorem *)
Theorem bezout_exists : forall (a b:nat),{u:nat & {v:nat | (is_gcd (a*u-b*v) a b)}}+{u:nat & {v:nat | (is_gcd (b*v-a*u) a b)}}.
  intros.
  elim (bezout_exists_prod (a,b));intro.
  elim a0;destruct x;simpl;intros.
  left;exists n;exists n0;rewrite mult_comm;rewrite (mult_comm b);trivial.
  elim b0;destruct x;simpl;intros.
  right;exists n;exists n0;rewrite mult_comm;rewrite (mult_comm a);trivial.
Qed.

(** Bezout' theorem reformulated *)
Theorem bezout : forall (d a b:nat),(is_gcd d a b)->exists u:nat,exists v:nat,d=a*u-b*v \/ d=b*v-a*u.
  intros.
  elim (bezout_exists a b);intro.
  elim a0;intro u;intro;elim p;intro v;intro;exists u;exists v;left;apply (gcd_unique d (a*u-b*v) a b);trivial.
  elim b0;intro u;intro;elim p;intro v;intro;exists u;exists v;right;apply (gcd_unique d (b*v-a*u) a b);trivial.
Qed.

(** Bezout' theorem and relatively prime numbers *)
Theorem bezout_rel_prime : forall (a b:nat),(rel_prime a b)<->(exists u:nat, exists v:nat, 1=a*u-b*v \/ 1 = b*v-a*u).
  intros.
  unfold rel_prime.
  split;intro.
  apply bezout;trivial.
  elim H;intro u;intro H0.
  elim H0;intro v;intro.
  unfold is_gcd;unfold is_cd.
  split.
  split;apply one_min_div.
  intros.
  elim H2;intros.
  elim H3;intro q;intro.
  elim H4;intro q';intro.
  rewrite H5 in H1;rewrite H6 in H1.
  case H1;intro.
  exists (q*u-q'*v);rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
  exists (q'*v-q*u);rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
Qed.

(** gcd(n*a,n*b) = n*gcd(a,b) *)
Lemma gcd_mult : forall (d a b:nat),(is_gcd d a b)->(forall (n:nat),(is_gcd (n*d) (n*a) (n*b))).
  unfold is_gcd;unfold is_cd.
  intros.
  elim H;intros.
  elim H0;intros.
  split.
  elim H2;intro q;intro.
  elim H3;intro q';intro.
  rewrite H4;rewrite mult_assoc.
  rewrite H5;rewrite mult_assoc.
  split;[exists q;trivial | exists q';trivial].
  intros.
  elim H4;intros.
  elim (bezout d a b);try (unfold is_gcd;unfold is_cd;trivial).
  intro u;intro.
  elim H7;intro v;intro.
  elim H5;intro q;intro.
  elim H6;intro q';intro.
  case H8;intro;[exists (q*u-q'*v) | exists (q'*v-q*u)];rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;rewrite <- H9;rewrite <- H10;rewrite H11;rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;trivial.
Qed.

(** Gauss' theorem (use Bezout) *)
Theorem gauss : forall (d a b:nat),(rel_prime a d)->(divides (a*b) d)->(divides b d).
  unfold rel_prime.
  intros.
  elim (bezout 1 a d H);intro u;intro.
  elim H1;intro v;intro.
  elim H0;intro q;intro.
  case H2;intro;[exists (q*u-b*v) | exists (b*v-q*u)];rewrite mult_minus_lemma2;rewrite mult_assoc;rewrite mult_assoc;rewrite <- H3;rewrite (mult_comm a b);rewrite (mult_comm d b);rewrite <- mult_assoc;rewrite <- mult_assoc;rewrite <- mult_minus_lemma2;rewrite <- H4;auto with arith.
Qed.

(** we show that if b<>0, then gcd(a,b)=gcd(b,a mod b) *)
Lemma gcd_euclide : forall (d a b:nat)(H:(b<>0)),(is_gcd d a b)<->(is_gcd d b (remainder_euclide a b H)).
  intros.
  generalize (quo_rem_euclide a b H);intro.
  red;split;intro.
  rewrite H0 in H1.
  elim H1;intros.
  unfold is_gcd;unfold is_cd.
  elim H2;intros.
  split.
  split;try tauto.
  elim H4;intro q;intro.
  elim H5;intro q';intro.
  replace (b*(quotient_euclide a b H)) with (d*q'*(quotient_euclide a b H)) in H6.
  assert ((remainder_euclide a b H)=(d*q-d*q'*(quotient_euclide a b H))).
  rewrite <- H6;rewrite minus_plus;trivial.
  rewrite <- mult_assoc in H8;rewrite <- mult_minus_lemma2 in H8.
  exists (q-q'*(quotient_euclide a b H));trivial.
  rewrite <- H7;trivial.
  intros.
  elim H6;intros.
  apply H3.
  unfold is_cd;split;try tauto.
  elim H7;intro q;intro.
  elim H8;intro q';intro.
  rewrite H10.
  replace (b*(quotient_euclide a b H)) with (d'*q*(quotient_euclide a b H)).
  rewrite <- mult_assoc;rewrite <- mult_plus_distr_l.
  exists (q*(quotient_euclide a b H)+q');trivial.
  rewrite <- H9;trivial.
  unfold is_gcd;unfold is_cd.
  unfold is_gcd in H1;unfold is_cd in H1.
  elim H1;intros.
  elim H2;intros.
  rewrite H0.
  split.
  split;try tauto.
  elim H4;intro q;intro.
  elim H5;intro q';intro.
  rewrite H7.
  replace (b*(quotient_euclide a b H)) with (d*q*(quotient_euclide a b H)).
  rewrite <- mult_assoc;rewrite <- mult_plus_distr_l.
  exists (q*(quotient_euclide a b H)+q');trivial.
  rewrite <- H6;trivial.
  intros.
  apply H3.
  split;try tauto.
  elim H6;intros.
  elim H7;intro q;intro.
  elim H8;intro q';intro.
  assert ((remainder_euclide a b H)=b*(quotient_euclide a b H)+(remainder_euclide a b H)-b*(quotient_euclide a b H)).
  rewrite minus_plus;trivial.
  rewrite H9 in H11.
  exists (q-q'*(quotient_euclide a b H)).
  rewrite mult_minus_lemma2;rewrite mult_assoc.
  rewrite <- H10;trivial.
Qed.

(** we give a "more efficient" algorithm to compute gcd(a,b) *)
Lemma gcd_exists_prod_bis : forall (x:nat*nat),{d:nat | (is_gcd d (fst x) (snd x))}.
  apply (induction_ltof2 (nat*nat) f (fun x:nat*nat => {d:nat | (is_gcd d (fst x) (snd x))})).
  unfold ltof;unfold f;intros.
  case (lt_eq_lt_dec (fst x) (snd x));intro.
  case s;intro.
  case (eq_nat_dec (fst x) 0);intro.
  rewrite e;exists (snd x);apply gcd_zero.
  elim (H ((fst x),(remainder_euclide (snd x) (fst x) n)));simpl.
  intro d;intro.
  exists d.
  apply gcd_sym.
  elim (gcd_euclide d (snd x) (fst x) n);auto.
  generalize (rem_euclide (snd x) (fst x) n);try omega.
  rewrite e;exists (snd x);apply gcd_refl.
  case (eq_nat_dec (snd x) 0);intro.
  rewrite e;exists (fst x);apply gcd_sym;apply gcd_zero.
  elim (H ((snd x),(remainder_euclide (fst x) (snd x) n)));simpl.
  intro d;intro.
  exists d.
  elim (gcd_euclide d (fst x) (snd x) n);auto.
  generalize (rem_euclide (fst x) (snd x) n);try omega.
Qed.

(** efficient algorithm to compute gcd(a,b) *)
Theorem gcd_exists_bis : forall (a b:nat),{d:nat | (is_gcd d a b)}.
  intros.
  elim (gcd_exists_prod_bis (a,b));intro d;simpl;intros.
  exists d;trivial.
Qed.

(** it is decidable to say if a and b are relatively prime *)
Lemma rel_prime_dec : forall (a b:nat),{rel_prime a b}+{~(rel_prime a b)}.
  intros.
  unfold rel_prime.
  generalize (gcd_is_gcd a b);intro.
  case (eq_nat_dec (gcd a b) 1);intro.
  left;rewrite e in H;trivial.
  right;intro;apply n;apply (gcd_unique (gcd a b) 1 a b);trivial.
Qed.

(** if gcd(a,b)=1 and gcd(a,c)=1 then gcd(a,b*c)=1 *)
Lemma rel_prime_mult : forall (a b c:nat),(rel_prime a b)->(rel_prime a c)->(rel_prime a (b*c)).
  intros.
  split.
  split;try (apply one_min_div).
  intros.
  elim H1;intros.
  case (rel_prime_dec b d');intro.
  assert (divides c d').
  apply gauss with b;trivial.
  elim H0;intros.
  apply H6;unfold is_cd;tauto.
  generalize (gcd_is_gcd b d');intro.
  assert ((gcd b d')<>1).
  intro;apply n.
  unfold rel_prime;rewrite <- H5;trivial.
  generalize (gcd_div_l (gcd b d') b d' H4);intro.
  generalize (gcd_div_r (gcd b d') b d' H4);intro.
  assert (divides a (gcd b d')).
  apply divides_trans with d';[apply H2 | apply H7].
  elim H5.
  apply divides_antisym.
  apply one_min_div.
  elim H;intros;apply H10;unfold is_cd;tauto.
Qed.

(** if gcd(a,b*c)=1 then gcd(a,b)=1 and gcd(a,c)=1 *)
Lemma mult_rel_prime : forall (a b c:nat),(rel_prime a (b*c))->((rel_prime a b)/\(rel_prime a c)).
  intros.
  split;split;[split | intros | split | intros];try (apply one_min_div);elim H0;intros;elim H;intros;apply H4;split;trivial;elim H2;intro q;intro;rewrite H5;[exists (q*c) | exists (q*b)];ring.
Qed.

(** if gcd(a,d)=1 then gcd(a,d^n)=1 *)
Lemma rel_prime_power : forall (d a n:nat),(rel_prime a d)->(rel_prime a (power d n)).
  induction n;simpl;intros.
  unfold rel_prime;apply gcd_sym;apply gcd_one.
  generalize (IHn H);intro.
  apply rel_prime_mult;trivial.
Qed.

(** if n>0 and gcd(a,d^n)=1 then gcd(a,d)=1 *)
Lemma power_rel_prime : forall (d a n:nat),(n>0)->(rel_prime a (power d n))->(rel_prime a d).
  destruct n;simpl;intros.
  inversion H.
  elim (mult_rel_prime a d (power d n));auto.
Qed.

(** if n>0 and m>0 then gcd(a^n,b^m)=1 iff gcd(a,b)=1 *)
Lemma power_power_rel_prime : forall (a n b m:nat),(n>0)->(m>0)->((rel_prime (power a n) (power b m))<->(rel_prime a b)).
  split;intro.
  apply power_rel_prime with m;trivial;apply rel_prime_sym;apply power_rel_prime with n;trivial;apply rel_prime_sym;trivial.
  apply rel_prime_power;apply rel_prime_sym;apply rel_prime_power;apply rel_prime_sym;trivial.
Qed.

