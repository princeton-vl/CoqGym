(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU Lesser General Public License for more details.                *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

(***********************************************************************)
(*    Proof of Huffman algorithm: ISort.v                              *)
(*                                                                     *)
(*    Definition of sorting by insertion and its proof of correctness  *)
(*                                                                     *)
(*    Definitions: isort, insert                                       *)
(*                                                                     *)
(*                                    Laurent.Thery@inria.fr (2003)    *)
(***********************************************************************)

Require Import List.
From Huffman Require Import Permutation.
From Huffman Require Import Ordered.
From Huffman Require Import sTactic.
 
Section ISortExample.
Variable A : Type.
Variable order : A -> A -> Prop.
Variable order_fun : A -> A -> bool.
Hypothesis order_fun_true : forall a b : A, order_fun a b = true -> order a b.
Hypothesis order_fun_false : forall a b : A, order_fun a b = false -> order b a.

(* Insert an element *) 
Fixpoint insert (a : A) (l : list A) {struct l} : list A :=
  match l with
  | nil => a :: nil
  | b :: l1 =>
      match order_fun a b with
      | true => a :: l
      | false => b :: insert a l1
      end
  end.

(* Inserting preserves ordering *)
Theorem insert_ordered :
 forall l : list A,
 ordered order l -> forall a : A, ordered order (insert a l).
Proof using order_fun_false order_fun_true.
intros l H'; elim H'; clear H' l; auto.
simpl in |- *; auto.
intros a b; simpl in |- *.
generalize (refl_equal (order_fun b a));
 pattern (order_fun b a) at -1 in |- *; case (order_fun b a); 
 intros Eq0; auto.
intros a b l H'0 H'1 H'2 a0.
simpl in |- *.
generalize (refl_equal (order_fun a0 a));
 pattern (order_fun a0 a) at -1 in |- *; case (order_fun a0 a); 
 intros Eq0; auto.
generalize (H'2 a0); simpl in |- *.
generalize (refl_equal (order_fun a0 b));
 pattern (order_fun a0 b) at -1 in |- *; case (order_fun a0 b); 
 intros Eq1; auto.
Qed.

(* Inserting returns a permutation *)
Theorem insert_permutation :
 forall (L : list A) (a : A), permutation (a :: L) (insert a L).
Proof using.
intros L; elim L; simpl in |- *; auto.
intros b l H' a.
CaseEq (order_fun a b); intros H1; auto.
apply permutation_trans with (l2 := b :: a :: l); auto.
Qed.
Hint Resolve insert_ordered insert_permutation : core.

(* Sorting by insertion *)
Fixpoint isort (l : list A) : list A :=
  match l with
  | nil => nil
  | b :: l1 => insert b (isort l1)
  end.

(* Sorting gives an ordered list *)
Theorem isort_ordered : forall l : list A, ordered order (isort l).
Proof using order_fun_false order_fun_true. 
intros l; elim l; simpl in |- *; auto.
Qed.

(* The result is a permutation of the original list *)
Theorem isort_permutation : forall l : list A, permutation l (isort l).
Proof using.
intros l; elim l; clear l; simpl in |- *; auto.
intros a l H'.
apply permutation_trans with (l2 := a :: isort l); auto.
Qed.
Hint Resolve isort_ordered isort_permutation : core.

End ISortExample.
Arguments insert [A].
Arguments isort [A].
