(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



Require Import ZArith.
Require Import ZArithRing.

Require Import divide.
Require Import gcd.

(** Relative primality *)

Definition rel_prime (a b : Z) : Prop := gcd a b 1.


(** Bezout's theorem: [a] and [b] are relatively prime if and
    only if there exist [u] and [v] such that [ua+vb = 1]. *)

Lemma rel_prime_bezout : forall a b : Z, rel_prime a b -> Bezout a b 1.
Proof.
intros a b; exact (gcd_bezout a b 1).
Qed.

Lemma bezout_rel_prime : forall a b : Z, Bezout a b 1 -> rel_prime a b.
Proof.
simple induction 1; constructor; auto.
intros. rewrite <- H0; auto.
Qed.


(** Gauss's theorem: if [a] divides [bc] and if [a] and [b] are
    relatively prime, then [a] divides [c]. *)

Theorem Gauss : forall a b c : Z, (a | b * c)%Z -> rel_prime a b -> (a | c)%Z.
Proof.
intros. elim (rel_prime_bezout a b H0); intros.
replace c with (c * 1)%Z; [ idtac | ring ].
rewrite <- H1.
replace (c * (u * a + v * b))%Z with (c * u * a + v * (b * c))%Z;
 [ eauto | ring ].
Qed.


(** If [a] is relatively prime to [b] and [c], then it is to [bc] *)

Lemma rel_prime_mult :
 forall a b c : Z, rel_prime a b -> rel_prime a c -> rel_prime a (b * c).
Proof.
intros a b c Hb Hc.
elim (rel_prime_bezout a b Hb); intros.
elim (rel_prime_bezout a c Hc); intros.
apply bezout_rel_prime.
apply
 Bezout_intro
  with (u := (u * u0 * a + v0 * c * u + u0 * v * b)%Z) (v := (v * v0)%Z).
rewrite <- H.
replace (u * a + v * b)%Z with ((u * a + v * b) * 1)%Z; [ idtac | ring ].
rewrite <- H0.
ring.
Qed.


(** Primality *)

Inductive prime (p : Z) : Prop :=
    prime_intro :
      (1 < p)%Z -> (forall n : Z, (1 <= n < p)%Z -> rel_prime n p) -> prime p.


(** The sole divisors of a prime number [p] are [-1], [1], 
    [p] and [-p]. *)

Lemma prime_divisors :
 forall p : Z,
 prime p ->
 forall a : Z, (a | p)%Z -> a = (-1)%Z \/ a = 1%Z \/ a = p \/ a = (- p)%Z.
Proof.
simple induction 1; intros.
assert
 (a = (- p)%Z \/
  (- p < a < -1)%Z \/
  a = (-1)%Z \/ a = 0%Z \/ a = 1%Z \/ (1 < a < p)%Z \/ a = p).
assert (Zabs a <= Zabs p)%Z. apply divide_bounds; [ assumption | omega ].
generalize H3. 
pattern (Zabs a) in |- *; apply Zabs_ind; pattern (Zabs p) in |- *;
 apply Zabs_ind; intros; omega.
intuition.
(* -p < a < -1 *)
absurd (rel_prime (- a) p); intuition.
inversion H3.
assert (- a | - a)%Z; auto.
assert (- a | p)%Z; auto.
generalize (H8 (- a)%Z H9 H10); intuition.
generalize (divide_1 (- a) H11); intuition.
(* a = 0 *)
inversion H2. subst a; omega.
(* 1 < a < p *)
absurd (rel_prime a p); intuition.
inversion H3.
assert (a | a)%Z; auto.
assert (a | p)%Z; auto.
generalize (H8 a H9 H10); intuition.
generalize (divide_1 a H11); intuition.
Qed.


(** A prime number is relatively prime with any number it does not divide *)

Lemma prime_rel_prime :
 forall p : Z, prime p -> forall a : Z, ~ (p | a)%Z -> rel_prime p a.
Proof.
simple induction 1; intros.
constructor; intuition.
elim (prime_divisors p H x H3); intuition; subst; auto.
absurd (p | a)%Z; auto.
absurd (p | a)%Z; intuition.
Qed.

Hint Resolve prime_rel_prime.


(** [divide] is decidable *)

Axiom divide_dec : forall a b : Z, {(a | b)%Z} + {~ (a | b)%Z}.

(*
Lemma divide_dec : (a,b:Z) { `a|b` } + { ~ `a|b` }.
Proof.
Intros a b; Case (Z_eq_dec b `0`); Intro.
Left; Subst; Auto.
Case (Z_eq_dec a `0`); Intro.
Right; Red; Intro; Subst.
Inversion H; Omega.
Case (Z_le_gt_dec a `0`); Intro.
Assert `-a > 0`; Try Omega.
Generalize (Z_div_mod_eq b `-a` H); Intro.
Case (Z_eq_dec (Zmod b `-a`) `0`); Intro.
Left.
Apply divide_intro with `-(b/(-a))`.
Rewrite e in H0; Clear e.
Pattern 1 b; Rewrite H0; Ring.
Right; Red; Intro.
Inversion H1.
LetTac q0 := `b / (-a)`; LetTac r := `b % (-a)`.
Generalize (Z_mod_lt b `-a` H).
*)

(** If a prime [p] divides [ab] then it divides either [a] or [b] *)

Lemma prime_mult :
 forall p : Z,
 prime p -> forall a b : Z, (p | a * b)%Z -> (p | a)%Z \/ (p | b)%Z.
Proof.
simple induction 1; intros.
case (divide_dec p a); intuition.
right; apply Gauss with a; auto.
Qed.
















