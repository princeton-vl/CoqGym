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
(* file: Lists_field.v                                          *)
(* contents: trunc, strip, sublist and elemlist for polymorphic *)
(* lists.                                                       *)
(****************************************************************)

Require Import Arith_compl.
Require Export Minus.
Require Export Lists_compl.


Section Lists_field.
Variable A : Set.

Fixpoint trunc (v : list A) : nat -> list A :=
  fun n : nat =>
  match v return (list A) with
  | nil => nil
  | b :: w =>
      match n return (list A) with
      | O => nil
      | S p => b :: trunc w p
      end
  end.

Definition strip (v : list A) (n : nat) :=
  rev A (trunc (rev A v) (length v - n)).

(* Selection d'une sous liste commencant a la position start, de
   longueur lengt *)
Definition sublist (v : list A) (start lengt : nat) :=
  trunc (strip v start) lengt.

(* Selection de la liste contenant le i-eme element d'une liste *)
Definition elemlist (v : list A) (i : nat) := trunc (strip v i) 1.

(****************************************************************)
(* lemmes sur trunc *)

Lemma length_trunc :
 forall (v : list A) (i : nat),
 (*****************)
 i <= length v -> length (trunc v i) = i.
simple induction v. simpl in |- *. auto with arith.
intros b b0 H. simple induction i. simpl in |- *. trivial with arith.
simpl in |- *. intros. apply eq_S. apply H. apply le_S_n. exact H1.
Qed.

Lemma trunc_inv :
 forall (v : list A) (i : nat) (b : A),
 (**************)
 b :: trunc v i = trunc (b :: v) (S i).
simpl in |- *. trivial with arith.
Qed.

Lemma trunc_all : forall v : list A, trunc v (length v) = v.
(**************)
simple induction v. simpl in |- *. trivial with arith.
intros. rewrite length_eq2. simpl in |- *. rewrite H. trivial with arith.
Qed. Hint Resolve trunc_all.

Lemma trunc_max :
 forall (v : list A) (i : nat),
 (**************)
 length v <= i -> trunc v i = v.
simple induction v. simpl in |- *. trivial with arith.
intros. inversion H0. rewrite trunc_all. trivial with arith.
simpl in |- *. rewrite H. trivial with arith.
apply le_Sn_le. generalize H1. simpl in |- *. trivial with arith.
Qed.

Lemma trunc_O : forall v : list A, trunc v 0 = nil.
(************)
simple induction v; auto with arith.
Qed. Hint Resolve trunc_O.

Lemma le_length_trunc :
 forall (v : list A) (i : nat), length (trunc v i) <= i.
(********************)
simple induction v. simpl in |- *. auto with arith.
intros. case i. rewrite trunc_O. auto with arith.
intro. simpl in |- *. apply le_n_S. apply H.
Qed. Hint Resolve le_length_trunc.

Lemma trunc_app :
 forall (v1 v2 : list A) (i : nat),
 (**************)
 trunc (v1 ++ v2) i = trunc v1 i ++ trunc v2 (i - length v1).
simple induction v1. simpl in |- *. auto with arith.
intros. rewrite app_eq2.
rewrite length_eq2. elim i. simpl in |- *. rewrite trunc_O. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed. Hint Resolve trunc_app.

Lemma app_v_trunc :
 forall (v1 v2 : list A) (i : nat),
 (****************)
 v1 ++ trunc v2 i = trunc (v1 ++ v2) (length v1 + i).
intros. rewrite trunc_app. rewrite (trunc_max v1 (length v1 + i)).
replace (length v1 + i - length v1) with i. trivial with arith. auto with arith.
auto with arith.
Qed.

Lemma trunc_eq :
 forall (v1 v2 : list A) (i : nat), v1 = v2 -> trunc v1 i = trunc v2 i.
(*************)
intros. rewrite H. trivial with arith.
Qed. Hint Resolve trunc_eq.

Lemma trunc_sym :
 forall (v : list A) (i j : nat), 
 (**************)
 trunc (trunc v i) j = trunc (trunc v j) i.
simple induction v. simpl in |- *. trivial with arith.
simple induction i; simple induction j. trivial with arith.
repeat rewrite trunc_O. simpl in |- *. trivial with arith.
repeat rewrite trunc_O. simpl in |- *. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed.

Lemma trunc_trunc1 :
 forall (v : list A) (i : nat),
 (*****************)
 trunc (trunc v i) i = trunc v i.
simple induction v. simpl in |- *. trivial with arith.
simple induction i. repeat rewrite trunc_O. trivial with arith.
intros. simpl in |- *. rewrite H. trivial with arith.
Qed. Hint Resolve trunc_trunc1.

Lemma trunc_trunc2 :
 forall (v : list A) (i j : nat),
 (*****************)
 i <= j -> trunc (trunc v i) j = trunc v i.
intros. rewrite (trunc_max (trunc v i) j). trivial with arith.
apply le_trans with i. apply le_length_trunc. exact H.
Qed.

Lemma trunc_trunc3 :
 forall (v : list A) (i j : nat),
 (*****************)
 j <= i -> trunc (trunc v i) j = trunc v j.
intros. rewrite <- (trunc_max (trunc v j) i). rewrite trunc_sym. trivial with arith.
apply le_trans with j. apply le_length_trunc.
exact H.
Qed.

Lemma trunc_plus_petit :
 forall (v1 v2 : list A) (i j : nat),
 (*********************)
 j <= i -> trunc v1 i = v2 -> trunc v1 j = trunc v2 j.
intros. rewrite <- H0. rewrite trunc_trunc3. trivial with arith. exact H.
Qed.

(****************************************************************)
(* lemmes sur strip *)

Lemma strip_nil : forall i : nat, strip nil i = nil.
(**************)
intro. auto with arith.
Qed. Hint Resolve strip_nil.

Lemma strip_cons_S :
 forall (v : list A) (i : nat) (b : A),
 (*****************)
 strip (b :: v) (S i) = strip v i.
unfold strip in |- *. simple induction i. simpl in |- *.
elim minus_n_O. intro. replace (length v) with (length (rev A v)).
rewrite trunc_all. rewrite trunc_app. rewrite trunc_all.
elim minus_n_n. rewrite trunc_O. rewrite app_v_nil. trivial with arith.
apply length_rev.
intros. apply rev_eq. simpl in |- *.
rewrite trunc_app. rewrite length_rev. rewrite minus_minus_lem1.
rewrite trunc_O. rewrite app_v_nil. trivial with arith.
Qed. Hint Resolve strip_cons_S.

Lemma length_strip :
 forall (v : list A) (i : nat),
 (*****************)
 i <= length v -> length (strip v i) = length v - i.
unfold strip in |- *. intros. rewrite length_rev. rewrite length_trunc. trivial with arith.
rewrite length_rev. apply minus_le_lem2.
Qed.

Lemma le_length_strip :
 forall (v : list A) (i : nat),
 (********************)
 length (strip v i) <= length v - i.
unfold strip in |- *. intros. rewrite length_rev. apply le_length_trunc.
Qed.

Lemma strip_inv :
 forall (v : list A) (i : nat),
 (***************)
 rev A (trunc (rev A v) (length v - i)) = strip v i.
unfold strip in |- *. trivial with arith.
Qed.

Lemma strip_all : forall v : list A, strip v (length v) = nil.
(**************)
unfold strip in |- *. intro. rewrite <- minus_n_n. rewrite trunc_O. auto with arith.
Qed. Hint Resolve strip_all.

Lemma strip_max :
 forall (v : list A) (i : nat),
 (**************)
 length v <= i -> strip v i = nil.
unfold strip in |- *. intros. rewrite <- rev_eq1.
apply rev_eq. rewrite <- length_rev. rewrite minus_le_O. auto with arith.
rewrite length_rev. exact H.
Qed.

Lemma strip_O : forall v : list A, strip v 0 = v.
(************)
intro. unfold strip in |- *. rewrite <- minus_n_O. rewrite <- length_rev.
rewrite trunc_all. rewrite rev_rev. trivial with arith.
Qed. Hint Resolve strip_O.

Lemma strip_app :
 forall (v1 v2 : list A) (i : nat),
 (**************)
 strip (v1 ++ v2) i = strip v1 i ++ strip v2 (i - length v1).
simple induction v1. simpl in |- *. intros. elim minus_n_O. trivial with arith.
simple induction v2. intro. simpl in |- *.
rewrite strip_nil. rewrite app_v_nil. rewrite app_v_nil. trivial with arith.
simple induction i.
rewrite strip_O. simpl in |- *. rewrite strip_O. rewrite strip_O. auto with arith.
intros. rewrite app_eq2. rewrite strip_cons_S.
rewrite strip_cons_S. rewrite length_eq2. simpl in |- *. apply H.
Qed.

Lemma strip_strip_S :
 forall (v : list A) (i j : nat),
 (******************)
 strip (strip v (S i)) j = strip (strip v i) (S j).
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intros. rewrite strip_O.
do 2 rewrite strip_cons_S. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O.
repeat rewrite strip_cons_S. elim n. rewrite strip_O. trivial with arith.
intros. rewrite <- H. rewrite strip_O. trivial with arith.
intros. do 2 rewrite strip_cons_S. apply H.
Qed.

Lemma strip_sym :
 forall (v : list A) (i j : nat),
 (**************)
 strip (strip v i) j = strip (strip v j) i.
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intro. rewrite strip_O. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O. rewrite strip_O. try trivial with arith.
intros. rewrite strip_cons_S. rewrite strip_cons_S.
replace (strip (strip l n) (S n0)) with (strip (strip l (S n)) n0).
apply H. apply strip_strip_S.
Qed.

Lemma strip_eq :
 forall (v1 v2 : list A) (i : nat), v1 = v2 -> strip v1 i = strip v2 i.
(*************)
intros. rewrite H. trivial with arith.
Qed. Hint Resolve strip_eq.

Lemma strip_strip :
 forall (v : list A) (i j : nat),
 (****************)
 strip (strip v i) j = strip v (i + j).
simple induction v. intros. rewrite strip_nil. rewrite strip_nil. trivial with arith.
simple induction i. intro. simpl in |- *. rewrite strip_O. trivial with arith.
simple induction j. rewrite strip_O. elim plus_n_O. trivial with arith.
intros. rewrite strip_cons_S. simpl in |- *. rewrite strip_cons_S. apply H.
Qed. Hint Resolve strip_strip.

(****************************************************************)
(* lemmes sur trunc et strip ensembles *)

Lemma app_trunc_strip :
 forall (v : list A) (i : nat),
 (********************)
 trunc v i ++ strip v i = v.
simple induction v. unfold strip in |- *. simpl in |- *. trivial with arith.
intros. elim i. rewrite trunc_O. rewrite strip_O. simpl in |- *. trivial with arith.
intros. unfold strip in |- *. simpl in |- *.
rewrite trunc_app. rewrite rev_app. rewrite length_rev.
case n. rewrite <- minus_n_O.
rewrite <- minus_n_n. rewrite trunc_O. rewrite trunc_O. simpl in |- *.
rewrite <- length_rev. rewrite trunc_all. rewrite rev_rev. trivial with arith.
intro. replace (length l - S n0 - length l) with 0.
rewrite trunc_O. simpl in |- *.
replace (rev A (trunc (rev A l) (length l - S n0))) with (strip l (S n0)).
rewrite H. trivial with arith.
unfold strip in |- *. trivial with arith.
rewrite minus_minus_lem1. trivial with arith.
Qed.

Lemma strip_trunc_i :
 forall (v : list A) (i : nat), strip (trunc v i) i = nil.
(******************)
simple induction v. auto with arith.
simple induction i. auto with arith.
intros. simpl in |- *. rewrite strip_cons_S. apply H.
Qed. Hint Resolve strip_trunc_i.

Lemma strip_trunc :
 forall (v : list A) (i j : nat),
 (****************)
 strip (trunc v i) j = trunc (strip v j) (i - j).
simple induction v. simpl in |- *. unfold strip in |- *. simpl in |- *. trivial with arith.
simple induction i; simple induction j.
simpl in |- *. rewrite strip_O. rewrite trunc_O. trivial with arith.
rewrite trunc_O.
simpl in |- *. intros. unfold strip in |- *. simpl in |- *. rewrite trunc_O. trivial with arith.
rewrite strip_O. rewrite strip_O. elim minus_n_O. trivial with arith.
intros. rewrite strip_cons_S. simpl in |- *. rewrite strip_cons_S. apply H.
Qed.

Lemma trunc_strip :
 forall (v : list A) (i j : nat),
 (****************)
 trunc (strip v i) j = strip (trunc v (i + j)) i.
simple induction v. unfold strip in |- *. simpl in |- *. trivial with arith.
simple induction i; simple induction j. rewrite trunc_O. rewrite strip_O. auto with arith.
intros. rewrite strip_O. rewrite strip_O. auto with arith.
rewrite trunc_O. elim plus_n_O. rewrite strip_trunc_i. trivial with arith.
intros.
rewrite strip_cons_S. replace (S n + S n0) with (S (n + S n0)).
simpl in |- *. rewrite strip_cons_S. apply H.
auto with arith.
Qed.

(****************************************************************)
(* lemmes sur elemlist et sublist *)

Lemma elemlist_is_sublist :
 forall (v : list A) (i : nat),
 (************************)
 elemlist v i = sublist v i 1.
unfold elemlist, sublist in |- *. trivial with arith.
Qed.

Lemma elemlist_cons_S :
 forall (v : list A) (i : nat) (b : A),
 (********************)
 elemlist (b :: v) (S i) = elemlist v i.
unfold elemlist in |- *. intros. rewrite strip_cons_S. trivial with arith.
Qed.

Lemma elemlist_cons_O :
 forall (v : list A) (b : A),
 (********************)
 elemlist (b :: v) 0 = b :: nil.
intros.
unfold elemlist in |- *. rewrite strip_O. simpl in |- *. rewrite trunc_O. trivial with arith.
Qed.

Lemma elemlist_inv :
 forall (l : list A) (i : nat),
 (*****************)
 trunc (strip l i) 1 = elemlist l i.
unfold elemlist in |- *. trivial with arith.
Qed.

Lemma app_trunc_elemlist :
 forall (v : list A) (i : nat),
 (***********************)
 S i <= length v -> trunc v i ++ elemlist v i = trunc v (S i).
simple induction v. unfold elemlist in |- *. simpl in |- *. trivial with arith.
simple induction i. simpl in |- *. unfold elemlist in |- *. rewrite trunc_O.
rewrite strip_O. simpl in |- *. rewrite trunc_O. trivial with arith.
intros. simpl in |- *. unfold elemlist in |- *.
rewrite strip_cons_S. unfold elemlist in H. rewrite H. trivial with arith.
generalize H1. simpl in |- *. auto with arith.
Qed.


Lemma length_elemlist :
 forall (l : list A) (i : nat),
 (********************)
 i < length l -> length (elemlist l i) = 1.
intros. unfold elemlist in |- *. rewrite length_trunc. trivial with arith.
rewrite length_strip. inversion H. rewrite <- minus_Sn_m. auto with arith. auto with arith.
rewrite <- minus_Sn_m. auto with arith. apply le_Sn_le. exact H1. apply lt_le_weak. exact H.
Qed.


End Lists_field.