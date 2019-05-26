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


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************)
(*           The Calculus of Inductive Constructions            *)
(*                       COQ v5.10                              *)
(*                                                              *)
(* Laurent Arditi.  Laboratoire I3S. CNRS ura 1376.             *)
(* Universite de Nice - Sophia Antipolis                        *)
(* arditi@unice.fr, http://wwwi3s.unice.fr/~arditi/lolo.html    *)
(*                                                              *)
(* date: may 1995                                               *)
(* file: Arith_compl.v                                          *)
(* contents: additionnal lemmas on plus,mult,minus,le...        *)
(* definitions of 2^ and factorial, lemmas about them           *)
(****************************************************************)


Require Export Plus.
Require Export Mult.
Require Import Minus.
Require Export Lt.
Require Export Le.
Require Export Gt.

(****************************************************************)
(* Complements sur plus et mult *)

Lemma plus_n_SO : forall x : nat, x + 1 = S x.
intros; rewrite plus_comm; auto with arith.
Qed. Hint Resolve plus_n_SO.

Lemma plus_permute2 : forall x y z : nat, x + y + z = x + z + y.
intros.
rewrite (plus_comm x y).
rewrite (plus_comm x z).
rewrite plus_comm.
symmetry  in |- *.
rewrite plus_comm.
rewrite plus_permute.
auto with arith.
Qed. Hint Resolve plus_permute2.

Lemma mult_sym : forall a b : nat, a * b = b * a.
intros a b; elim a; simpl in |- *; auto with arith.
intros y H.
replace (y * b) with (b * y).
elim (mult_n_Sm b y).
apply plus_comm.
Qed. Hint Resolve mult_sym.

Lemma mult_permute : forall a b c : nat, a * b * c = a * c * b.
intros.
rewrite mult_assoc_reverse.
rewrite mult_assoc_reverse.
replace (c * b) with (b * c); auto with arith.
Qed. Hint Resolve mult_permute.

(*
Lemma plus_n_n : (n:nat)((plus n n)=(mult n (S (S O)))).
Intro.
Rewrite -> mult_sym.
Simpl.
Replace (plus n O) with (plus O n);Auto with arith.
Qed. Hints Resolve plus_n_n.
*)

Lemma plus_O_O : forall n m : nat, n + m = 0 -> n = 0.
simple induction n. intros. trivial with arith.
intros. inversion H0.
Qed.

Lemma mult_plus_distr2 : forall n m p : nat, n * (m + p) = n * m + n * p.
intros. rewrite mult_sym. rewrite mult_plus_distr_r. rewrite mult_sym.
replace (p * n) with (n * p). trivial with arith. apply mult_sym.
Qed.

(****************************************************************)
(* La fonction puissance de 2 *)

Fixpoint power2 (n : nat) : nat :=
  match n with
  | O => 1
  | S x => power2 x + power2 x
  end.

Lemma power2_eq2 : forall x : nat, power2 (S x) = power2 x + power2 x.
Proof. 
 auto with arith.
Qed.


(*
Lemma power2_SO : ((S (S O))=(power2 (S O))).
Auto with arith. Qed. Hints Resolve power2_SO.

Lemma mult_power2 : (x,y:nat)
		((mult (power2 x) (power2 y))=(power2 (plus x y))).
*)
Lemma power2_plus : forall x y : nat, power2 (x + y) = power2 x * power2 y.
simple induction x. intros. simpl in |- *. elim plus_n_O; auto with arith.
intros. simpl in |- *. rewrite H. rewrite mult_plus_distr_r. trivial with arith.
Qed.

(****************************************************************)
(* Complements sur Lt Le Gt... *)

Theorem le_plus_n_m : forall n m : nat, n <= m -> n + n <= m + m.
simple induction n. auto with arith.
intros. inversion H0. auto with arith.
simpl in |- *. elim plus_n_Sm. elim plus_n_Sm.
apply le_n_S. apply le_n_S. apply H. apply le_Sn_le. exact H1.
Qed. Hint Resolve le_plus_n_m.

Theorem lt_plus_n_m : forall n m : nat, n < m -> S (n + n) < m + m.
simple induction n.
simpl in |- *. simple induction m. simpl in |- *. intros. absurd (0 < 0). apply le_not_lt. auto with arith.
exact H.
intros. simpl in |- *. elim plus_n_Sm. apply lt_n_S. auto with arith.
intros. inversion H0. simpl in |- *. repeat elim plus_n_Sm. auto with arith.
simpl in |- *.
repeat elim plus_n_Sm. apply lt_n_S. apply lt_n_S. apply H. inversion H1. auto with arith.
apply le_lt_n_Sm. apply le_Sn_le. apply le_Sn_le. exact H3.
Qed.

Lemma le_plus_lem1 : forall a b c : nat, a <= b -> c + a <= c + b.
intros. inversion H. auto with arith.
elim plus_n_Sm. apply le_S. auto with arith.
Qed. Hint Resolve le_plus_lem1.

Lemma le_plus_lem2 : forall a b c : nat, c + a <= c + b -> a <= b.
simple induction c. auto with arith.
simpl in |- *. intros. apply H. apply le_S_n. exact H0.
Qed.

Lemma gt_double : forall a b : nat, a + a > b + b -> a > b. 
simple induction a. simpl in |- *. intros. absurd (0 > b + b). auto with arith.
auto with arith. simple induction b. simpl in |- *. auto with arith.
intros. apply gt_n_S.
apply H. generalize H1. simpl in |- *. elim plus_n_Sm. elim plus_n_Sm. intro.
cut (S (n + n) > S (n0 + n0)). intro. apply gt_S_n. exact H3.
apply gt_S_n. exact H2.
Qed.

Lemma gt_double_inv : forall a b : nat, a > b -> a + a > b + b.
simple induction a. intros. absurd (0 > b). auto with arith. exact H.
simple induction b. intros. simpl in |- *. auto with arith.
intros. simpl in |- *. elim plus_n_Sm.
elim plus_n_Sm. apply gt_n_S. apply gt_n_S. apply H. apply gt_S_n. exact H1.
Qed.

Lemma gt_double_n_S : forall a b : nat, a > b -> a + a > S (b + b).
simple induction a. intros. absurd (0 > b). auto with arith.
exact H.
simple induction b. simpl in |- *. intro.
apply gt_n_S. unfold gt in |- *. unfold lt in |- *. elim plus_n_Sm. auto with arith.
intros. simpl in |- *. apply gt_n_S.
elim plus_n_Sm. apply gt_n_S. elim plus_n_Sm. apply H. apply gt_S_n. exact H1.
Qed.

Lemma gt_double_S_n : forall a b : nat, a > b -> S (a + a) > b + b.
intros. apply gt_trans with (a + a). auto with arith. apply gt_double_inv. exact H.
Qed.

(****************************************************************)
(* Complements sur minus *)

Lemma minus_le_O : forall a b : nat, a <= b -> a - b = 0.
intros. pattern a, b in |- *. apply le_elim_rel. auto with arith.
intros. simpl in |- *. exact H1.
exact H.
Qed.

Lemma minus_n_SO : forall n : nat, n - 1 = pred n.
simple induction n. auto with arith. intros. simpl in |- *. auto with arith.
Qed.

Lemma minus_le_lem2c : forall a b : nat, a - S b <= a - b.
intros. pattern a, b in |- *. apply nat_double_ind. auto with arith.
intro. elim minus_n_O. rewrite minus_n_SO. simpl in |- *. auto with arith.
intros. simpl in |- *. exact H.
Qed.

Lemma minus_le_lem2 : forall a b : nat, a - b <= a.
simple induction b. elim minus_n_O. auto with arith.
intros. apply le_trans with (a - n). apply minus_le_lem2c.
exact H.
Qed. Hint Resolve minus_le_lem2.

Lemma minus_minus_lem1 : forall a b : nat, a - b - a = 0.
intros. apply minus_le_O. apply minus_le_lem2.
Qed. Hint Resolve minus_minus_lem1.

Lemma minus_minus_lem2 : forall a b : nat, b <= a -> a - (a - b) = b.
simple induction b. intros. elim minus_n_O. elim minus_n_n. trivial with arith. intros.
replace (a - (a - S n)) with (S a - S (a - S n)).
rewrite <- (minus_Sn_m a (S (a - S n))). rewrite (minus_Sn_m a (S n)).
simpl in |- *. rewrite <- H. rewrite H. rewrite H. trivial with arith.
apply le_Sn_le. exact H0.
apply le_Sn_le. exact H0. apply le_Sn_le. exact H0. exact H0.
rewrite minus_Sn_m. simpl in |- *. apply minus_le_lem2. exact H0. simpl in |- *. trivial with arith.
Qed.

Lemma le_minus_minus : forall a b c : nat, c <= b -> a - b <= a - c.
simple induction a. simpl in |- *. auto with arith.
intros. generalize H0. elim c. elim minus_n_O. intro. apply minus_le_lem2.
elim b. intros. absurd (S n0 <= 0). auto with arith.
exact H2.
intros. simpl in |- *. apply H. apply le_S_n. exact H3.
Qed.
