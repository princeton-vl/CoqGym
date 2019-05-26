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
Require Import Zcomplements.

Unset Standard Proposition Elimination Names.

(** Divisibility *)

Inductive divide (a b : Z) : Prop :=
    divide_intro : forall q : Z, b = (q * a)%Z -> divide a b.

Notation "( x | y )" := (divide x y) (at level 0) : Z_scope.

Local Open Scope Z_scope.


(** Results *)

Lemma divide_refl : forall a : Z, (a | a).
Proof.
intros; apply divide_intro with 1; ring.
Qed.

Lemma one_divide : forall a : Z, (1 | a).
Proof.
intros; apply divide_intro with a; ring.
Qed.

Lemma divide_0 : forall a : Z, (a | 0).
Proof.
intros; apply divide_intro with 0; ring.
Qed.

Hint Resolve divide_refl one_divide divide_0.

Lemma divide_mult_left : forall a b c : Z, (a | b) -> (c * a | c * b).
Proof.
simple induction 1; intros; apply divide_intro with q.
rewrite H0; ring.
Qed.

Lemma divide_mult_right : forall a b c : Z, (a | b) -> (a * c | b * c).
Proof.
intros a b c; rewrite (Zmult_comm a c); rewrite (Zmult_comm b c).
apply divide_mult_left; trivial.
Qed.

Hint Resolve divide_mult_left divide_mult_right.

Lemma divide_plus : forall a b c : Z, (a | b) -> (a | c) -> (a | b + c).
Proof.
simple induction 1; intros q Hq; simple induction 1; intros q' Hq'.
apply divide_intro with (q + q').
rewrite Hq; rewrite Hq'; ring.
Qed.

Lemma divide_opp : forall a b : Z, (a | b) -> (a | - b).
Proof.
simple induction 1; intros; apply divide_intro with (- q).
rewrite H0; ring.
Qed.

Lemma divide_opp_rev : forall a b : Z, (a | - b) -> (a | b).
Proof.
intros; replace b with (- - b). apply divide_opp; trivial. ring.
Qed.

Lemma divide_opp_left : forall a b : Z, (a | b) -> (- a | b).
Proof.
simple induction 1; intros; apply divide_intro with (- q).
rewrite H0; ring.
Qed.

Lemma divide_opp_left_rev : forall a b : Z, (- a | b) -> (a | b).
Proof.
intros; replace a with (- - a). apply divide_opp_left; trivial. ring.
Qed.

Lemma divide_minus : forall a b c : Z, (a | b) -> (a | c) -> (a | b - c).
Proof.
simple induction 1; intros q Hq; simple induction 1; intros q' Hq'.
apply divide_intro with (q - q').
rewrite Hq; rewrite Hq'; ring.
Qed.

Lemma divide_left : forall a b c : Z, (a | b) -> (a | b * c).
Proof.
simple induction 1; intros q Hq; apply divide_intro with (q * c).
rewrite Hq; ring.
Qed.

Lemma divide_right : forall a b c : Z, (a | c) -> (a | b * c).
Proof.
simple induction 1; intros q Hq; apply divide_intro with (q * b).
rewrite Hq; ring.
Qed.

Lemma divide_a_ab : forall a b : Z, (a | a * b).
Proof.
intros; apply divide_intro with b; ring.
Qed.

Lemma divide_a_ba : forall a b : Z, (a | b * a).
Proof.
intros; apply divide_intro with b; ring.
Qed.

Hint Resolve divide_plus divide_opp divide_opp_rev divide_opp_left
  divide_opp_left_rev divide_minus divide_left divide_right divide_a_ab
  divide_a_ba.


(** Trivial lemmas to do case analysis over [x:Z]. *)

Lemma z_case_0_1 :
 forall x : Z, x <= -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x >= 2.
Proof. intro; omega. Qed.

Lemma z_case_0 : forall x : Z, x <= -1 \/ x = 0 \/ x >= 1.
Proof. intro; omega. Qed.


(** Only [1] and [-1] divide [1]. *)

Lemma divide_1 : forall x : Z, (x | 1) -> x = 1 \/ x = -1.
Proof.
simple induction 1; intros.
elim (z_case_0_1 x); intuition; elim (z_case_0 q); intuition.
assert (q * x >= 1 * 2). 
replace (q * x) with (- q * - x); try ring.
apply Zmult_ge_compat; omega.
omega.
rewrite H3 in H0; omega.
assert (- (q * x) >= 1 * 2). 
replace (- (q * x)) with (q * - x); try ring.
apply Zmult_ge_compat; omega.
omega.
rewrite H1 in H0; omega.
rewrite H1 in H0; omega.
rewrite H1 in H0; omega.
assert (- (q * x) >= 1 * 2). 
replace (- (q * x)) with (- q * x); try ring.
apply Zmult_ge_compat; omega.
omega.
rewrite H3 in H0; omega.
assert (q * x >= 1 * 2). 
apply Zmult_ge_compat; omega.
omega.
Qed.


(** If [a] divides [b] and [b] divides [a] 
    then [a] is [b] or [-b]. *)

Lemma divide_antisym : forall a b : Z, (a | b) -> (b | a) -> a = b \/ a = - b.
Proof.
simple induction 1; intros.
inversion H1.
rewrite H0 in H2; clear H H1.
case (Z_zerop a); intro.
left; rewrite H0; rewrite e; ring.
assert (Hqq0 : q0 * q = 1).
apply Zmult_reg_l with a.
assumption.
ring_simplify.
pattern a at 2 in |- *; rewrite H2; ring.
assert (q | 1).
rewrite <- Hqq0; auto.
elim (divide_1 q H); intros.
rewrite H1 in H0; left; omega.
rewrite H1 in H0; right; omega.
Qed.


(** If [a] divides [b] and [b<>0] then [|a| <= |b|]. *)

Lemma Zabs_ind :
 forall (P : Z -> Prop) (x : Z),
 (x >= 0 -> P x) -> (x <= 0 -> P (- x)) -> P (Zabs x).
Proof.
intros; elim (Z_lt_ge_dec x 0); intro. 
rewrite Zabs_non_eq. apply H0; omega. omega.
rewrite Zabs_eq. apply H; assumption. omega.
Qed.

Lemma divide_bounds : forall a b : Z, (a | b) -> b <> 0 -> Zabs a <= Zabs b.
Proof.
simple induction 1; intros.
pattern (Zabs a) in |- *; apply Zabs_ind; pattern (Zabs b) in |- *;
 apply Zabs_ind; intros.
(* a >= 0, b >= 0 *)
elim (z_case_0 q); intro.
assert (- b >= 1 * 0).
replace (- b) with (- q * a).
apply Zmult_ge_compat; omega.
rewrite H0; ring. omega.
elim H4; intro; clear H4. 
rewrite H5 in H0; omega.
apply Zge_le.
replace a with (1 * a).
rewrite H0.
apply Zmult_ge_compat; omega.
ring.
(* a >= 0, b <= 0 *)
elim (z_case_0 q); intro.
apply Zge_le.
replace a with (1 * a).
rewrite H0.
replace (- (q * a)) with (- q * a).
apply Zmult_ge_compat; omega.
ring. ring.
elim H4; intro; clear H4. 
rewrite H5 in H0; omega.
assert (b >= 1 * 0).
rewrite H0.
apply Zmult_ge_compat; omega.
omega.
(* a <= 0, b >= 0 *)
elim (z_case_0 q); intro.
apply Zge_le.
replace (- a) with (1 * - a).
rewrite H0.
replace (q * a) with (- q * - a).
apply Zmult_ge_compat; omega.
ring. ring.
elim H4; intro; clear H4. 
rewrite H5 in H0; omega.
assert (- b >= 1 * 0).
rewrite H0.
replace (- (q * a)) with (q * - a).
apply Zmult_ge_compat; omega.
ring. omega.
(* a <= 0, b <= 0 *)
elim (z_case_0 q); intro.
assert (b >= 1 * 0).
rewrite H0.
replace (q * a) with (- q * - a).
apply Zmult_ge_compat; omega.
ring. omega.
elim H4; intro; clear H4. 
rewrite H5 in H0; omega.
apply Zge_le.
replace (- a) with (1 * - a).
rewrite H0.
replace (- (q * a)) with (q * - a).
apply Zmult_ge_compat; omega.
ring. ring.
Qed.
