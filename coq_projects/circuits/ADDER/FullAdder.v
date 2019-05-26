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
(* file: FullAdder.v                                            *)
(* contents: definition and verification of a full adder        *)
(*                                                              *)
(****************************************************************)

(* Full adder sur les bits (bool) : rend la somme ou le carry *)
(* Verification: Theorem full_adder_ok *)

Require Export HalfAdder.

(****************************************************************)

Definition full_adder_sum (a b c : bool) :=
  half_adder_sum (half_adder_sum a b) c.

Definition full_adder_carry (a b c : bool) :=
  half_adder_carry a b || half_adder_carry (half_adder_sum a b) c.

(****************************************************************)

Lemma full_adder_sum_sym1 :
 forall a b c : bool, full_adder_sum a b c = full_adder_sum b a c.
simple induction a; simple induction b; auto.
Qed. Hint Resolve full_adder_sum_sym1.

Lemma full_adder_sum_sym2 :
 forall a b c : bool, full_adder_sum a b c = full_adder_sum a c b.
simple induction b.
simple induction c.
auto.
unfold full_adder_sum in |- *.
rewrite half_adder_sum_false.
rewrite half_adder_sum_false.
auto.
unfold full_adder_sum in |- *.
rewrite half_adder_sum_false.
intro.
auto.
Qed. Hint Resolve full_adder_sum_sym2.

Lemma full_adder_sum_false :
 forall a : bool, full_adder_sum a false false = a.
simple induction a; auto.
Qed. Hint Resolve full_adder_sum_false.

Lemma full_adder_sum_true : forall a : bool, full_adder_sum a true true = a.
simple induction a; auto.
Qed. Hint Resolve full_adder_sum_true.

Lemma full_adder_carry_sym1 :
 forall a b c : bool, full_adder_carry a b c = full_adder_carry b a c.
simple induction a; simple induction b; auto.
Qed. Hint Resolve full_adder_carry_sym1.

Lemma full_adder_carry_sym2 :
 forall a b c : bool, full_adder_carry a b c = full_adder_carry a c b.
simple induction b.
simple induction c.
auto.
unfold full_adder_carry in |- *.
rewrite half_adder_sum_false.
rewrite half_adder_carry_false.
rewrite half_adder_carry_false.
simpl in |- *.
elim (half_adder_carry a true); auto.
intros.
unfold full_adder_carry in |- *.
rewrite half_adder_carry_false.
rewrite half_adder_sum_false.
rewrite half_adder_carry_false.
simpl in |- *.
elim (half_adder_carry a c); auto.
Qed. Hint Resolve full_adder_carry_sym2.

Lemma full_adder_carry_false :
 forall a : bool, full_adder_carry a false false = false.
simple induction a; auto.
Qed. Hint Resolve full_adder_carry_false.

Lemma full_adder_carry_true :
 forall a : bool, full_adder_carry a true true = true.
simple induction a.
unfold full_adder_carry in |- *.
auto.
unfold full_adder_carry in |- *.
auto.
Qed. Hint Resolve full_adder_carry_true.

Lemma full_adder_carry_true_false :
 forall a : bool, full_adder_carry a true false = a.
simple induction a; auto.
Qed. Hint Resolve full_adder_carry_true_false.

Lemma full_adder_carry_neg :
 forall a b : bool, full_adder_carry a (negb a) b = b.
simple induction a; simple induction b; simpl in |- *.
rewrite full_adder_carry_sym1. rewrite full_adder_carry_true. trivial.
rewrite full_adder_carry_false. trivial.
rewrite full_adder_carry_true. trivial.
rewrite full_adder_carry_sym1. rewrite full_adder_carry_false. trivial.
Qed.

(****************************************************************)

Theorem full_adder_ok :
 forall a b c : bool,
 bool_to_nat (full_adder_sum a b c) +
 (bool_to_nat (full_adder_carry a b c) + bool_to_nat (full_adder_carry a b c)) =
 bool_to_nat a + bool_to_nat b + bool_to_nat c.
simple induction a; simple induction b; simple induction c; auto.
Qed.
