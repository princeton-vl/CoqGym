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
Require Import Wf_nat.

Unset Standard Proposition Elimination Names.

(** lemmae about divisibility *)
Lemma divides_le : forall (a b:nat),(a<>O)->(divides a b)->(b<=a).
  intros.
  elim H0;intro q;intro.
  replace b with (b*1);try ring.
  rewrite H1.
  apply mult_le_compat;try omega.
  destruct q;omega.
Qed.

(** Euclide theorem (existence) *)
Theorem euclide : forall (a b:nat),(b<>O)->{q:nat & { r:nat | (a=b*q+r) /\ (r < b)}}.
  intros.
  apply (lt_wf_rec a (fun a:nat =>{q : nat &  {r : nat | a = b * q + r /\ r < b}})).
  intros.
  case (le_lt_dec b n);intro.
  elim (H0 (n-b)).
  intro q;intro.
  elim p;intro r;intro.
  exists (q+1);exists r.
  split;try tauto.
  rewrite (le_plus_minus b n);trivial.
  elim p0;intros.
  rewrite H1;ring.
  omega.
  exists 0;exists n.
  split;try tauto.
  ring.
Qed.

Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.

Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

(** a div b where b<>0 *)
Lemma quo_rem_euclide : forall (a b:nat)(H:(b<>O)),a=b*(quotient_euclide a b H)+(remainder_euclide a b H).
  unfold quotient_euclide;unfold remainder_euclide;intros.
  generalize (euclide a b H);intros.
  elim s;intro q;intro.
  elim p;intro r;intro.
  tauto.
Qed.

(** a mod b where b<>0 *)
Lemma rem_euclide : forall (a b:nat)(H:(b<>O)),(remainder_euclide a b H)<b.
  unfold remainder_euclide;intros.
  generalize (euclide a b H);intros.
  elim s;intro q;intro.
  elim p;intro r;intro.
  tauto.
Qed.

(** Euclide division is unique *)
Lemma euclide_unique : forall (a b q r q' r':nat),(b<>O)->a=b*q+r->a=b*q'+r'->r<b->r'<b->(q=q')/\(r=r').
  intros.
  rewrite H1 in H0.
  case (lt_eq_lt_dec q q');intro.
  case s;intro.
  rewrite (le_plus_minus q q') in H0;try (auto with arith).
  rewrite mult_plus_distr_l in H0.
  assert (b*(q'-q)+r' = r).
  apply plus_reg_l with (b*q).
  rewrite plus_assoc;trivial.
  assert (0<(q'-q));try omega.
  assert (b<=b*(q'-q));try omega.
  case (mult_O_le b (q'-q));intro;try omega.
  rewrite mult_comm;trivial.
  split;try tauto.
  rewrite <- e in H0.
  symmetry;apply plus_reg_l with (b*q);trivial.
  rewrite (le_plus_minus q' q) in H0;try (auto with arith).
  rewrite mult_plus_distr_l in H0.
  assert (r'=(b*(q-q')+r)).
  apply plus_reg_l with (b*q').
  rewrite plus_assoc;trivial.
  assert (0<(q-q'));try omega.
  assert (b<=b*(q-q'));try omega.
  case (mult_O_le b (q-q'));intro;try omega.
  rewrite mult_comm;trivial.
Qed.

(** if b<>0, then b | a iff a mod b = 0 *) 
Lemma divides_euclide : forall (a b:nat)(H:(b<>O)),((divides a b)<->((remainder_euclide a b H)=O)).
  intros.
  red.
  split;intro.
  generalize (quo_rem_euclide a b H);intro.
  generalize (rem_euclide a b H);intro.
  elim H0;intro q;intro.
  assert (a=b*q+0).
  rewrite plus_comm;simpl;trivial.
  assert (0<b);try omega.
  generalize (euclide_unique a b (quotient_euclide a b H) (remainder_euclide a b H) q 0 H H1 H4 H2 H5).
  intros;tauto.
  generalize (quo_rem_euclide a b H).
  rewrite H0;rewrite plus_comm;simpl.
  intro;exists (quotient_euclide a b H);trivial.
Qed.

(** divisibility is decidable *)
Lemma divides_dec : forall (a b:nat),{divides a b}+{~(divides a b)}.
  intros.
  case (eq_nat_dec b 0).
  case (eq_nat_dec a 0);intros.
  rewrite e;left;apply zero_max_div.
  right;rewrite e;intro.
  elim H;intro q;intro.
  simpl in H0;apply n;trivial.
  intro.
  case (eq_nat_dec (remainder_euclide a b n) 0);[left | right];intros;elim (divides_euclide a b n);auto.
Qed.

(** if a property about integer is decidable then it is decidable if there is an integer less than n that satisfies this property *)
Lemma dec_impl_lt_dec : forall (P:nat->Prop),(forall (n:nat),{(P n)}+{~(P n)})->(forall (m:nat),{n:nat | (n<m)/\(P(n))}+{(forall (n:nat),(n<m)->~(P n))}).
  intros.
  induction m.
  right;intros;inversion H0.
  case (H m);intro.
  left;exists m;split;try (auto with arith).
  case IHm;intro.
  elim s;intro n0;intro.
  left;exists n0;split;[omega | tauto].
  right;intros.
  inversion H0;trivial.
  apply n0;omega.
Qed.

(** forall n, either forall p, p<>1 /\ p<>n -> not(p | n) or there is p such that p<>1 and p<>n and p | n *) 
Lemma divides_nat : forall (n:nat),{p:nat | (p<>1)/\(p<>n)/\(divides n p)}+{forall (p:nat),(p<>1)->(p<>n)->~(divides n p)}.
  intros.
  case (dec_impl_lt_dec (fun p => (p<>1)/\(divides n p))) with n;intros.
  case (divides_dec n n0);intro.
  case (eq_nat_dec n0 1);intros.
  right;intro;tauto.
  left;tauto.
  right;tauto.
  elim s;intros.
  left;exists x.
  split;try tauto.
  split;try tauto.
  omega.
  case (eq_nat_dec n 0);intro.
  rewrite e;left;exists 2.
  split;try (intro;discriminate).
  split;try (intro;discriminate).
  apply zero_max_div.
  right;intros.
  case (lt_eq_lt_dec p n);intro.
  case s;intro;[red in n0;intro;apply n0 with p;tauto | auto].
  intro;generalize (divides_le n p n1 H1);omega.
Qed.
