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
(*    Proof of Huffman algorithm: UList.v                              *)
(*                                                                     *)
(*    Definition of list with distinct elements                        *)
(*                                                                     *)
(*    Definition: ulist                                                *)
(*                                                                     *)
(*                                    Laurent.Thery@inria.fr (2003)    *)
(***********************************************************************)

Require Import List.
Require Import Arith.
From Huffman Require Import Permutation.
From Huffman Require Import sTactic.
 
Section UniqueList.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
 
(* A list is unique if there is not twice the same element in the list *)
Inductive ulist : list A -> Prop :=
  | ulist_nil : ulist nil
  | ulist_cons : forall a l, ~ In a l -> ulist l -> ulist (a :: l).
Hint Constructors ulist : core.
 
(* Inversion theorem *)
Theorem ulist_inv : forall a l, ulist (a :: l) -> ulist l.
Proof using.  
intros a l H; inversion H; auto.
Qed.
 
(* The append of two unique list is unique if the list are distinct *)
Theorem ulist_app :
 forall l1 l2,
 ulist l1 ->
 ulist l2 -> (forall a : A, In a l1 -> In a l2 -> False) -> ulist (l1 ++ l2).
Proof using.  
intros L1; elim L1; simpl in |- *; auto.
intros a l H l2 H0 H1 H2; apply ulist_cons; simpl in |- *; auto.
red in |- *; intros H3; case in_app_or with (1 := H3); auto; intros H4.
inversion H0; auto.
apply H2 with a; auto.
apply H; auto.
apply ulist_inv with (1 := H0); auto.
intros a0 H3 H4; apply (H2 a0); auto.
Qed.
 
(* Inversion theorem the appended list *)
Theorem ulist_app_inv :
 forall l1 l2 (a : A), ulist (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 a0 H0 [H1| H1] H2.
inversion H0; auto.
case H5; rewrite H1; auto with datatypes.
apply (H l2 a0); auto.
apply ulist_inv with (1 := H0); auto.
Qed.
 
(* Inversion theorem the appended list *)
Theorem ulist_app_inv_l : forall l1 l2 : list A, ulist (l1 ++ l2) -> ulist l1.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 H0; inversion H0; apply ulist_cons; auto.
Contradict H3; auto with datatypes.
apply H with l2; auto.
Qed.
 
(* Inversion theorem the appended list *)
Theorem ulist_app_inv_r : forall l1 l2 : list A, ulist (l1 ++ l2) -> ulist l2.
Proof using.
intros l1; elim l1; simpl in |- *; auto.
intros a l H l2 H0; inversion H0; auto.
Qed.
 
(* Uniqueness is decidable *)
Definition ulist_dec : forall l, {ulist l} + {~ ulist l}.
intros l; elim l; auto.
intros a l1 [H| H]; auto.
case (In_dec eqA_dec a l1); intros H2; auto.
right; red in |- *; intros H1; inversion H1; auto.
right; Contradict H; apply ulist_inv with (1 := H).
Defined.
 
(* Uniqueness is compatible with permutation *) 
Theorem ulist_perm :
 forall l1 l2 : list A, permutation l1 l2 -> ulist l1 -> ulist l2.
Proof using.
intros l1 l2 H; elim H; clear H l1 l2; simpl in |- *; auto.
intros a l1 l2 H0 H1 H2; apply ulist_cons; auto.
inversion H2; auto.
Contradict H4; apply permutation_in with (1 := permutation_sym _ _ _ H0);
 auto.
inversion H2; auto.
intros a b L H0; apply ulist_cons; auto.
inversion H0; auto.
inversion H3; auto.
simpl in |- *; Contradict H7; case H7; auto.
intros H8; case H2; rewrite H8; simpl in |- *; auto.
apply ulist_cons; auto.
inversion H0; auto.
Contradict H2; simpl in |- *; auto.
inversion H0; auto.
inversion H3; auto.
Qed.
 
End UniqueList.
Arguments ulist [A].
Hint Constructors ulist : core.
