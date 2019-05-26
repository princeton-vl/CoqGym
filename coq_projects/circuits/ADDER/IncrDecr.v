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
(* date: october 1995                                           *)
(* file: IncrDecr.v                                             *)
(* contents: definnition of an incrementer and a decrementer    *)
(* on BVs     **** TO BE COMPLETED ****                         *)
(****************************************************************)

Require Export AdderProof.



Fixpoint BV_increment (l : list bool) : BV :=
  match l with
  | nil => nilbv
  | false :: v => true :: v
  | true :: v => false :: BV_increment v
  end.


Fixpoint BV_increment_carry (l : list bool) : bool :=
  match l with
  | nil => true
  | false :: v => false
  | true :: v => BV_increment_carry v
  end.



Fixpoint BV_decrement (l : list bool) : BV :=
  match l with
  | nil => nilbv
  | false :: v => true :: BV_decrement v
  | true :: v => false :: v
  end.

Fixpoint BV_decrement_carry (l : list bool) : bool :=
  match l with
  | nil => true
  | false :: v => BV_decrement_carry v
  | true :: v => false
  end.



Lemma length_BV_increment :
 forall v : BV, lengthbv (BV_increment v) = lengthbv v.
simple induction v. auto.
simple induction a.
simpl in |- *. intros. rewrite H; trivial.
simpl in |- *. intros. trivial.
Qed.

Lemma length_BV_decrement :
 forall v : BV, lengthbv (BV_decrement v) = lengthbv v.
simple induction v. auto.
simple induction a.
simpl in |- *. intros. trivial.

simpl in |- *. intros. rewrite H; trivial.
Qed.

Lemma BV_increment_limit :
 forall n : nat,
 BV_increment (list_const bool n true) = list_const bool n false.
simple induction n. simpl in |- *. auto. intros. simpl in |- *. rewrite H; trivial.
Qed.

Lemma BV_decrement_limit :
 forall n : nat,
 BV_decrement (list_const bool n false) = list_const bool n true.
simple induction n. simpl in |- *. auto. intros. simpl in |- *. rewrite H; trivial.
Qed.


Lemma BV_increment_limit_carry :
 forall n : nat, BV_increment_carry (list_const bool n true) = true.
simple induction n. auto. intros. simpl in |- *. exact H.
Qed.

Lemma BV_decrement_limit_carry :
 forall n : nat, BV_decrement_carry (list_const bool n false) = true.
simple induction n. auto. intros. simpl in |- *. exact H.
Qed.


Lemma BV_increment_adder :
 forall v : BV,
 appbv (BV_increment v) (consbv (BV_increment_carry v) nilbv) =
 BV_full_adder v nilbv true.
simple induction v.
simpl in |- *. unfold BV_full_adder in |- *. unfold nilbv, consbv, appbv in |- *. simpl in |- *. trivial.
(* Induction a. Unfold consbv nilbv appbv . Simpl. Intros. Rewrite -> H.*)
simple induction a. intros. unfold consbv, nilbv, appbv in |- *. simpl in |- *.
unfold consbv, nilbv, appbv in H. rewrite H.
(* *)
unfold BV_full_adder in |- *. simpl in |- *. replace (half_adder_sum true true) with false.
trivial.
auto.
unfold BV_full_adder in |- *. unfold consbv, nilbv, appbv in |- *. intros. simpl in |- *.
replace (half_adder_sum false true) with true.
replace (BV_full_adder_sum l nil false) with l.
replace (BV_full_adder_carry l nil false) with false.
trivial.
auto. auto. auto.
Qed.

Lemma BV_increment_ok :
 forall v : BV,
 BV_to_nat (appbv (BV_increment v) (consbv (BV_increment_carry v) nilbv)) =
 S (BV_to_nat v).
intro. rewrite BV_increment_adder. rewrite BV_full_adder_ok.
simpl in |- *. elim plus_n_O. elim plus_n_Sm. auto.
Qed.

Lemma BV_decr_incr : forall v : BV, BV_decrement (BV_increment v) = v.
simple induction v. simpl in |- *. trivial.
simple induction a. intros. simpl in |- *. rewrite H; trivial.
intros. simpl in |- *. trivial.
Qed.

Lemma BV_incr_decr : forall v : BV, BV_increment (BV_decrement v) = v.
simple induction v.
auto. simple induction a; intros; simpl in |- *. trivial. rewrite H; trivial.
Qed.
