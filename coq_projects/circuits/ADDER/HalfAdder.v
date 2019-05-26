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
(* file: HalfAdder.v                                            *)
(* contents: definition and verification of an half-adder       *)
(*                                                              *)
(****************************************************************)

(* Half adder sur les bits (bool) : rend la somme ou le carry *)
(* Verification: Theorem half_adder_ok *)

Require Export Arith_compl.
Require Export Bool_compl.

(****************************************************************)

Definition half_adder_sum (a b : bool) := xorb a b.
Definition half_adder_carry (a b : bool) := a && b.

(****************************************************************)

Lemma half_adder_sum_sym :
 forall a b : bool, half_adder_sum a b = half_adder_sum b a.
simple induction a; simple induction b; auto.
Qed. Hint Resolve half_adder_sum_sym.

Lemma half_adder_carry_sym :
 forall a b : bool, half_adder_carry a b = half_adder_carry b a.
simple induction a; simple induction b; auto.
Qed. Hint Resolve half_adder_carry_sym.

Lemma half_adder_sum_false : forall a : bool, half_adder_sum a false = a.
simple induction a; auto.
Qed. Hint Resolve half_adder_sum_false.

Lemma half_adder_carry_false :
 forall a : bool, half_adder_carry a false = false.
simple induction a; auto.
Qed. Hint Resolve half_adder_carry_false.

Lemma half_adder_sum_true : forall a : bool, half_adder_sum a true = negb a.
auto.
Qed. Hint Resolve half_adder_sum_true.

Lemma half_adder_carry_true : forall a : bool, half_adder_carry a true = a.
simple induction a; auto.
Qed. Hint Resolve half_adder_carry_true.

(****************************************************************)

Theorem half_adder_ok :
 forall a b : bool,
 bool_to_nat (half_adder_sum a b) +
 (bool_to_nat (half_adder_carry a b) + bool_to_nat (half_adder_carry a b)) =
 bool_to_nat a + bool_to_nat b.
simple induction a; simple induction b; auto.
Qed.
