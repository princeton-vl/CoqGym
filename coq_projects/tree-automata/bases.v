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


Require Import Bool.
Require Import Arith.
Require Import ZArith.
Require Import NArith.
Require Import Ndec.
From IntMap Require Import Allmaps.
Require Import EqNat.
Require Export Max.

Lemma nat_sum : forall n : nat, n = 0 \/ (exists m : nat, n = S m).
Proof.
	simple induction n. left. reflexivity. intros. right.
	split with n0. reflexivity.
Qed.

Lemma le_n_n : forall n : nat, n <= n.
Proof.
        simple induction n. trivial.
        intros. exact (le_n_S n0 n0 H).
Qed.

Lemma le_l_or_r : forall n m : nat, n <= m \/ m <= n.
Proof.
        intros. cut (n <= m \/ m < n). intros. elim H.
        intros. left. assumption.
        intros. right. exact (lt_le_weak m n H0).
        exact (le_or_lt n m).
Qed.

Lemma plus_n_O : forall n : nat, n + 0 = n.
 Proof.
       simple induction n. trivial.
       intros. simpl in |- *. rewrite H. trivial.
 Qed.
 
 Lemma S_plus_l : forall n m : nat, S (n + m) = S n + m.
 Proof.
       simpl in |- *. trivial.
 Qed.
 
 Lemma S_plus_r : forall n m : nat, S (n + m) = n + S m.
 Proof.
       intros. rewrite (plus_comm n (S m)). rewrite (plus_comm n m).
       simpl in |- *. trivial.
 Qed.


(* lemmes concernant max *)

Lemma max_le_Sr_0 :
 forall n m : nat, max n m <= max n (S m) /\ max (S n) m <= max (S n) (S m).
Proof.
	simple induction n; simple induction m. simpl in |- *. split. exact (le_n_Sn 0).
	exact (le_n_n 1).
	intros. split. elim H. intros. intros. simpl in |- *. exact (le_n_Sn (S n0)).
	elim H. intros. simpl in |- *. exact (le_n_Sn (S n0)).
	split. simpl in |- *. cut (max n0 0 = n0). intros. rewrite H0. trivial.
	rewrite max_l; auto with arith.
 	simpl in |- *. exact (le_n_n (S (S n0))).
	intros. elim H0. intros. split. simpl in |- *. elim (H n1). intros.
	exact (le_n_S (max n0 n1) (max n0 (S n1)) H3).
	cut (max (S (S n0)) (S n1) = S (max (S n0) n1)).
	cut (max (S (S n0)) (S (S n1)) = S (max (S n0) (S n1))).
	intros. rewrite H3. rewrite H4. elim (H (S n1)).
	intros. elim (H n1). intros.
	exact (le_n_S (max (S n0) n1) (max (S n0) (S n1)) H8).
	simpl in |- *. trivial.
	simpl in |- *. trivial.
Qed.

Lemma max_le_Sr : forall n m : nat, max n m <= max n (S m).
Proof.
	intros. elim (max_le_Sr_0 n m). intros. exact H.
Qed.

(* lemmes arithmétiques *)

Lemma plus_O_r : forall n : nat, n + 0 = n.
Proof.
	simple induction n. simpl in |- *. trivial.
	intros. simpl in |- *. rewrite H. trivial.
Qed.

Lemma plus_O_l : forall n : nat, n + 0 = n.
Proof.
	simple induction n. simpl in |- *; trivial.
	intros; simpl in |- *. rewrite H. trivial.
Qed.

Lemma le_mult_lS : forall n m : nat, n * m <= S n * m.
Proof.
	simple induction n. simpl in |- *. intro. cut (m + 0 = m). intros.
	rewrite H. exact (le_O_n m).
	exact (plus_O_r m).
	simpl in |- *. intros. exact (le_plus_r m (m + n0 * m)).
Qed.

Lemma le_mult_rS : forall n m : nat, n * m <= n * S m.
Proof.
	intros. cut (n * m = m * n). cut (n * S m = S m * n).
	intros. rewrite H. rewrite H0. exact (le_mult_lS m n).
	exact (mult_comm n (S m)).
	exact (mult_comm n m).
Qed.

Lemma le_disj : forall n m : nat, n <= m -> n = m \/ S n <= m.
Proof.
	intros. cut (m <= n \/ n < m). intro. elim H0; intros.
	left. exact (le_antisym n m H H1).
	right. exact (lt_le_S n m H1).
	exact (le_or_lt m n).
Qed.

Lemma le_mult_l : forall n m p : nat, n <= m -> n * p <= m * p.
Proof.
	intro. simple induction m. intros. cut (n = 0). intro. rewrite H0; trivial.
	symmetry  in |- *. exact (le_n_O_eq n H).
	induction  n as [| n Hrecn]. intros. simpl in |- *. exact (le_O_n (p + n * p)).
	intros. simpl in |- *. cut (n = n0 \/ S n <= n0). intro. cut (n * p <= n0 * p).
	intro. elim H1; intros. cut (p <= p). intros.
	exact (plus_le_compat p p (n * p) (n0 * p) H4 H2).
	exact (le_n_n p).
	cut (n * p <= S n * p). cut (S n * p <= n0 * p).
	intros. apply (le_trans (p + n * p) (p + S n * p) (p + n0 * p)).
	exact (plus_le_compat p p (n * p) (S n * p) (le_n_n p) H5).
	exact (plus_le_compat p p (S n * p) (n0 * p) (le_n_n p) H4).
	exact (H p H3).
	exact (le_mult_lS n p).
	elim H1; intros. rewrite H2. exact (le_n_n (n0 * p)).
	cut (n * p <= S n * p). intro.
	cut (S n * p <= n0 * p). intro.
	exact (le_trans (n * p) (S n * p) (n0 * p) H3 H4).
	exact (H p H2). exact (le_mult_lS n p).
	cut (n <= n0). intro. exact (le_disj n n0 H1).
	exact (le_S_n n n0 H0).
Qed.

Lemma le_mult_r : forall n m p : nat, n <= m -> p * n <= p * m.
Proof.
	intros. cut (p * n = n * p). intros. cut (p * m = m * p).
	intros. rewrite H0. rewrite H1. exact (le_mult_l n m p H).
	exact (mult_comm p m).
	exact (mult_comm p n).
Qed.

Lemma le_mult_mult : forall n m p q : nat, n <= m -> p <= q -> n * p <= m * q.
Proof.
	intros. cut (n * p <= n * q). intro.
	cut (n * q <= m * q). intro.
	exact (le_trans (n * p) (n * q) (m * q) H1 H2).
	exact (le_mult_l n m q H).
	exact (le_mult_r p q n H0).
Qed.

Lemma Sn_eq_Sm_n_eq_m : forall n m : nat, S n = S m -> n = m.
Proof.
	simple induction n. simple induction m. intros. reflexivity. intros.
	inversion H0. simple induction m. intros. inversion H0. intros.
	inversion H1. reflexivity.
Qed.

(* lemmes sur les booléens *)

Lemma bool_dec_eq : forall a b : bool, {a = b} + {a <> b}.
Proof.
	intros. case a. case b. left. trivial.
	right. exact diff_true_false.
	case b. right. exact diff_false_true.
	left. trivial.
Qed.

Lemma bool_is_false_or_true : forall a : bool, a = false \/ a = true.
Proof.
	simple induction a. right. trivial.
	left. trivial.
Qed.

Lemma bool_is_true_or_false : forall a : bool, a = true \/ a = false.
Proof.
	simple induction a. left. trivial.
	right. trivial.
Qed.

Lemma in_M0_false :
 forall (A : Set) (a : A), ~ (exists e : ad, MapGet A (M0 A) e = Some a).
Proof.
	intros. intro. elim H. intros. inversion H0.
Qed.

Lemma in_M1_id :
 forall (A : Set) (a : A) (x : ad) (e : A),
 (exists c : ad, MapGet A (M1 A x e) c = Some a) -> a = e.
Proof.
	intros. elim H. intros. cut (x = x0). intro. rewrite H1 in H0.
	cut (MapGet A (M1 A x0 e) x0 = Some e). intros. 
	cut (Some e = Some a). intro. inversion H3. trivial.
	transitivity (MapGet A (M1 A x0 e) x0).
	symmetry  in |- *. assumption.
	assumption.
	exact (M1_semantics_1 A x0 e).
	cut (Neqb x x0 = false \/ Neqb x x0 = true). intro. elim H1; intros.
	cut (MapGet A (M1 A x e) x0 = None). intro. cut (Some a = None).
	intro. inversion H4. transitivity (MapGet A (M1 A x e) x0). symmetry  in |- *.
	assumption.
	assumption.
	exact (M1_semantics_2 A x x0 e H2).
	exact (Neqb_complete x x0 H2).
	elim (bool_dec_eq (Neqb x x0) true). intros. right. assumption.
	intro y. left. exact (not_true_is_false (Neqb x x0) y).
Qed.

Lemma in_M2_disj :
 forall (A : Set) (a : A) (m0 m1 : Map A),
 (exists c : ad, MapGet A (M2 A m0 m1) c = Some a) ->
 (exists c : ad, MapGet A m0 c = Some a) \/
 (exists c : ad, MapGet A m1 c = Some a).
Proof.
	intros. elim H. simple induction x. simpl in |- *. intro. left. split with N0.
	assumption.
	simple induction p. intros. right. simpl in H1. split with (Npos p0).
	assumption.
	intros. left. simpl in H1. split with (Npos p0). assumption.
	intros. right. simpl in H0. split with N0. assumption.
Qed.

(* équations auxilliaires sur Neqb_1 *)

Lemma aux_Neqb_1_0 : forall p : positive, Peqb p p = true.
Proof.
	simple induction p. simpl in |- *. intros. trivial. simpl in |- *. intros.
	trivial. trivial.
Qed.

Lemma aux_Neqb_1_1 : forall p p0 : positive, Peqb p p0 = true -> p = p0.
Proof.
	simple induction p. intro. intro. simple induction p1. intros. simpl in H1.
	cut (p0 = p2). intro. rewrite H2. trivial. exact (H p2 H1).
	intros. simpl in H1. inversion H1. intros. inversion H0.
	intro. intro. simple induction p1. intros. inversion H1.
	intros. cut (p0 = p2). intros. rewrite H2. trivial.
	simpl in H1. exact (H p2 H1). intros. inversion H0.
	simple induction p0. intros. inversion H0. intros. inversion H0.
	intros. trivial.
Qed.

(* lemmes auxilliaires sur Neqb *)

Lemma aux_Neqb_trans :
 forall a b c : ad, Neqb a b = true -> Neqb b c = true -> Neqb a c = true.
Proof.
	intros. rewrite <- (Neqb_complete b c H0). trivial.
Qed.

(* récurrence bien fondée sur nat *)

Lemma indprinciple_nat_gen :
 forall P : nat -> Prop,
 (forall n : nat, (forall m : nat, m < n -> P m) -> P n) ->
 forall n m : nat, m <= n -> P m.
Proof.
	intro. intro. simple induction n. intros. apply (H m). intros. elim (lt_n_O m0 (lt_le_trans m0 m 0 H1 H0)). intros. elim (le_lt_or_eq m (S n0) H1). intros.
	exact (H0 m (lt_n_Sm_le m n0 H2)). intro. rewrite H2. apply (H (S n0)). intros.
	exact (H0 m0 (lt_n_Sm_le m0 n0 H3)).
Qed.

(* quelques lemmes arithmétiques *)

Lemma beq_nat_complete : forall n m : nat, beq_nat n m = true -> n = m.
Proof.
	simple induction n. simple induction m. intros. reflexivity. intros.
	inversion H0. simple induction m. intros. inversion H0. intros.
	simpl in H1. rewrite (H _ H1). reflexivity.
Qed.

Lemma beq_nat_correct : forall n : nat, beq_nat n n = true.
Proof.
	simple induction n. reflexivity. intros. simpl in |- *. exact H.
Qed.
