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
(* file: Bool_compl.v                                           *)
(* contents: additional lemmas about bool, definition of xor,   *)
(* bool_to_nat and if_then_else                                 *)
(****************************************************************)

Require Export Bool.

(****************************************************************)
Lemma neg_eq : forall a b : bool, negb a = negb b -> a = b.
simple induction a; simple induction b; auto.
Qed. Hint Resolve neg_eq.

Lemma false_to_true : false = negb true.
auto.
Qed.

Lemma true_to_false : true = negb false.
auto.
Qed.

Definition xorb (b1 b2 : bool) : bool := b1 && negb b2 || negb b1 && b2.

Lemma xorb_b_b : forall b : bool, xorb b b = false.
simple induction b; auto.
Qed. Hint Resolve xorb_b_b.

Lemma xorb_b_false : forall b : bool, xorb b false = b.
simple induction b; auto.
Qed. Hint Resolve xorb_b_false.

Lemma xorb_b_true : forall b : bool, xorb b true = negb b.
simple induction b; auto.
Qed. Hint Resolve xorb_b_true.

(****************************************************************)
Definition bool_to_nat (b : bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Lemma bool_to_nat_all :
 forall b : bool, bool_to_nat b = 0 \/ bool_to_nat b = 1.
simple induction b; auto.
Qed. Hint Resolve bool_to_nat_all.

(*
Lemma bool_to_nat_negb : (b:bool)
	(bool_to_nat (negb b))=(minus (S O) (bool_to_nat b)).
Induction b;Auto.
Qed. Hints Resolve bool_to_nat_negb.
*)


(****************************************************************)
(* Conditionnelle polymorphique: le test est un booleen,        *)
(* les clauses d'un type quelconque (le meme pour les 2 clauses *)

Definition If (T : Set) (b : bool) (x y : T) :=
  match b with
  | true => x
  | false => y
  end.

Lemma If_neg :
 forall (T : Set) (b : bool) (x y : T), If T (negb b) x y = If T b y x.
simple induction b; simpl in |- *; trivial.
Qed. Hint Resolve If_neg.

Lemma If_eq : forall (T : Set) (b : bool) (x : T), If T b x x = x.
simple induction b; simpl in |- *; trivial.
Qed. Hint Resolve If_eq.

Lemma IfIf :
 forall (T : Set) (b1 b2 : bool) (x x' y y' : T),
 If T b1 (If T b2 x y) (If T b2 x' y') =
 If T b2 (If T b1 x x') (If T b1 y y').
simple induction b2; auto.
Qed.

Lemma If_cond_true :
 forall (T : Set) (a : bool) (x y : T), x <> y -> If T a x y = x -> a = true.
unfold not in |- *. simple induction a; auto. 
Qed.

Lemma If_cond_false :
 forall (T : Set) (a : bool) (x y : T), x <> y -> If T a x y = y -> a = false.
unfold not in |- *. simple induction a. simpl in |- *. intros. absurd (x = y). auto.
exact H0. auto.
Qed.

Lemma F_If :
 forall (T T' : Set) (a : bool) (x y : T) (F : T -> T'),
 F (If T a x y) = If T' a (F x) (F y).
simple induction a; auto.
Qed. Hint Resolve F_If.





