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
Require Import Zdiv.
Require Import Omega.

Require Import divide.

(** * Greatest common divisor (gcd). *)
   
(** There is no unicity of the gcd; hence we define the
    predicate [gcd a b d] expressing that [d] is a gcd of 
    [a] and [b]. (We show later that the [gcd] is actually
    unique if we discard its sign.) *)

Inductive gcd (a b d : Z) : Prop :=
    gcd_intro :
      (d | a)%Z ->
      (d | b)%Z ->
      (forall x : Z, (x | a)%Z -> (x | b)%Z -> (x | d)%Z) -> gcd a b d.

(** Trivial properties of [gcd] *)

Lemma gcd_sym : forall a b d : Z, gcd a b d -> gcd b a d.
Proof.
simple induction 1; constructor; intuition.
Qed.

Lemma gcd_0 : forall a : Z, gcd a 0 a.
Proof.
constructor; auto.
Qed.

Lemma gcd_minus : forall a b d : Z, gcd a (- b) d -> gcd b a d.
Proof.
simple induction 1; constructor; intuition.
Qed.

Lemma gcd_opp : forall a b d : Z, gcd a b d -> gcd b a (- d).
Proof.
simple induction 1; constructor; intuition.
Qed.

Hint Resolve gcd_sym gcd_0 gcd_minus gcd_opp.

(** * Extended Euclid algorithm. *)

(** Euclid's algorithm to compute the [gcd] mainly relies on
    the following property. *)

Lemma gcd_for_euclid : forall a b d q : Z, gcd b (a - q * b) d -> gcd a b d.
Proof.
simple induction 1; constructor; intuition.
replace a with (a - q * b + q * b)%Z. auto. ring.
Qed.

(** We implement the extended version of Euclid's algorithm,
    i.e. the one computing Bezout's coefficients as it computes
    the [gcd]. We follow the algorithm given in Knuth's
    "Art of Computer Programming", vol 2, page 325. *)

Section extended_euclid_algorithm.

Variable a b : Z.

(** The specification of Euclid's algorithm is the existence of
    [u], [v] and [d] such that [ua+vb=d] and [(gcd a b d)]. *)

Inductive Euclid : Set :=
    Euclid_intro :
      forall u v d : Z, (u * a + v * b)%Z = d -> gcd a b d -> Euclid.

(** The recursive part of Euclid's algorithm uses well-founded
    recursion of non-negative integers. It maintains 6 integers
    [u1,u2,u3,v1,v2,v3] such that the following invariant holds:
    [u1*a+u2*b=u3] and [v1*a+v2*b=v3] and [gcd(u2,v3)=gcd(a,b)]. 
    *)

Lemma euclid_rec :
 forall v3 : Z,
 (0 <= v3)%Z ->
 forall u1 u2 u3 v1 v2 : Z,
 (u1 * a + u2 * b)%Z = u3 ->
 (v1 * a + v2 * b)%Z = v3 ->
 (forall d : Z, gcd u3 v3 d -> gcd a b d) -> Euclid.
Proof.
intros v3 Hv3; generalize Hv3; pattern v3 in |- *.
apply Z_lt_rec.
clear v3 Hv3; intros.
elim (Z_zerop x); intro.
apply Euclid_intro with (u := u1) (v := u2) (d := u3).
assumption.
apply H2.
rewrite a0; auto.
set (q := (u3 / x)%Z) in *.
assert (Hq : (0 <= u3 - q * x < x)%Z).
replace (u3 - q * x)%Z with (u3 mod x)%Z.
apply Z_mod_lt; omega.
assert (xpos : (x > 0)%Z). omega.
generalize (Z_div_mod_eq u3 x xpos). 
unfold q in |- *. 
intro eq; pattern u3 at 2 in |- *; rewrite eq; ring.
apply
 (H (u3 - q * x)%Z Hq (proj1 Hq) v1 v2 x (u1 - q * v1)%Z (u2 - q * v2)%Z).
tauto.
replace ((u1 - q * v1) * a + (u2 - q * v2) * b)%Z with
 (u1 * a + u2 * b - q * (v1 * a + v2 * b))%Z.
rewrite H0; rewrite H1; trivial.
ring.
intros; apply H2.
apply gcd_for_euclid with q; assumption.
assumption.
Qed.

(** We get Euclid's algorithm by applying [euclid_rec] on
    [1,0,a,0,1,b] when [b>=0] and [1,0,a,0,-1,-b] when [b<0]. *)

Lemma euclid : Euclid.
Proof.
case (Z_le_gt_dec 0 b); intro.
intros;
 apply
  euclid_rec
   with (u1 := 1%Z) (u2 := 0%Z) (u3 := a) (v1 := 0%Z) (v2 := 1%Z) (v3 := b);
 auto; ring.
intros;
 apply
  euclid_rec
   with
     (u1 := 1%Z)
     (u2 := 0%Z)
     (u3 := a)
     (v1 := 0%Z)
     (v2 := (-1)%Z)
     (v3 := (- b)%Z); auto; try ring.
omega.
Qed.

End extended_euclid_algorithm.

Theorem gcd_uniqueness_apart_sign :
 forall a b d d' : Z, gcd a b d -> gcd a b d' -> d = d' \/ d = (- d')%Z.
Proof.
simple induction 1.
intros H1 H2 H3; simple induction 1; intros.
generalize (H3 d' H4 H5); intro Hd'd.
generalize (H6 d H1 H2); intro Hdd'.
exact (divide_antisym d d' Hdd' Hd'd).
Qed.

(** * Bezout's coefficients *)

Inductive Bezout (a b d : Z) : Prop :=
    Bezout_intro : forall u v : Z, (u * a + v * b)%Z = d -> Bezout a b d.

(** Existence of Bezout's coefficients for the [gcd] of [a] and [b] *)

Lemma gcd_bezout : forall a b d : Z, gcd a b d -> Bezout a b d.
Proof.
intros a b d Hgcd.
elim (euclid a b); intros.
generalize (gcd_uniqueness_apart_sign a b d d0 Hgcd g).
intro H; elim H; clear H; intros.
apply Bezout_intro with u v.
rewrite H; assumption.
apply Bezout_intro with (- u)%Z (- v)%Z.
rewrite H; rewrite <- e; ring.
Qed.

(** gcd of [ca] and [cb] is [c gcd(a,b)]. *)

Lemma gcd_mult : forall a b c d : Z, gcd a b d -> gcd (c * a) (c * b) (c * d).
Proof.
simple induction 1; constructor; intuition.
elim (gcd_bezout a b d H); intros.
elim H3; intros.
elim H4; intros.
apply divide_intro with (u * q + v * q0)%Z.
rewrite <- H5.
replace (c * (u * a + v * b))%Z with (u * (c * a) + v * (c * b))%Z.
rewrite H6; rewrite H7; ring.
ring.
Qed.
