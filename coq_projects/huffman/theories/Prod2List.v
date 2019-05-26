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

(**********************************************************************
    Proof of Huffman algorithm: Prod2List.v                          
                                                                     
    Definition of a product between an integer list and a list of    
    trees and its properties                                         
                                                                     
    Definition: prod2list                                            
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.

Section Prod2List.
Variable A : Type.
Variable f : A -> nat.

(* 
 In the product the sum of the leaves is multiplied by the integer
 and added to the weight of the tree
*)
Definition prod2list l1 l2 :=
  fold_left plus
    (map2 (fun a b => a * sum_leaves f b + weight_tree f b) l1 l2) 0.

(* The product of the appended list is the sum of the product *)
Theorem prod2list_app :
 forall l1 l2 l3 l4,
 length l1 = length l2 ->
 prod2list (l1 ++ l3) (l2 ++ l4) = prod2list l1 l2 + prod2list l3 l4.
Proof using.
intros l1 l2 l3 l4 H; unfold prod2list in |- *.
rewrite map2_app; auto.
rewrite fold_left_app.
rewrite plus_comm.
apply sym_equal.
repeat
 rewrite
  fold_left_eta with (f := plus) (f1 := fun a b : nat => a + (fun x => x) b);
 auto.
apply sym_equal; rewrite <- fold_plus_split with (f := fun x : nat => x);
 auto.
apply plus_comm.
Qed.

(* Permuting two choosen elements lower the product *)
Theorem prod2list_le_l :
 forall a b c d l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 sum_leaves f c <= sum_leaves f d ->
 a <= b ->
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) <=
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6).
Proof using.
intros a b c d l1 l2 l3 l4 l5 l6 H H0 H1 H2 H3;
 change
   (prod2list (l1 ++ (a :: nil) ++ l2 ++ (b :: nil) ++ l3)
      (l4 ++ (d :: nil) ++ l5 ++ (c :: nil) ++ l6) <=
    prod2list (l1 ++ (a :: nil) ++ l2 ++ (b :: nil) ++ l3)
      (l4 ++ (c :: nil) ++ l5 ++ (d :: nil) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto.
apply plus_le_compat; auto with arith.
repeat rewrite plus_assoc; apply plus_le_compat; auto.
repeat rewrite (fun x y z => plus_comm (prod2list (x :: y) z)).
repeat rewrite plus_assoc_reverse; apply plus_le_compat; auto.
unfold prod2list in |- *; simpl in |- *.
rewrite le_plus_minus with (1 := H3); auto.
rewrite le_plus_minus with (1 := H2); auto.
replace
 (a * (sum_leaves f c + (sum_leaves f d - sum_leaves f c)) + weight_tree f d +
  ((a + (b - a)) * sum_leaves f c + weight_tree f c)) with
 (a * sum_leaves f c + weight_tree f c +
  (a * (sum_leaves f d - sum_leaves f c) + (a + (b - a)) * sum_leaves f c +
   weight_tree f d)); [ idtac | ring ].
apply plus_le_compat; auto with arith.
apply plus_le_compat; auto with arith.
repeat rewrite mult_plus_distr_l || rewrite mult_plus_distr_r;
 auto with arith.
replace
 (a * (sum_leaves f d - sum_leaves f c) +
  (a * sum_leaves f c + (b - a) * sum_leaves f c)) with
 (a * sum_leaves f c + (b - a) * sum_leaves f c +
  (a * (sum_leaves f d - sum_leaves f c) + 0)); [ auto with arith | ring ].
Qed.

(* Permuting two choosen elements lower the product *)
Theorem prod2list_le_r :
 forall a b c d l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 sum_leaves f d <= sum_leaves f c ->
 b <= a ->
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ d :: l5 ++ c :: l6) <=
 prod2list (l1 ++ a :: l2 ++ b :: l3) (l4 ++ c :: l5 ++ d :: l6).
Proof using.
intros a b c d l1 l2 l3 l4 l5 l6 H H0 H1 H2 H3;
 change
   (prod2list (l1 ++ (a :: nil) ++ l2 ++ (b :: nil) ++ l3)
      (l4 ++ (d :: nil) ++ l5 ++ (c :: nil) ++ l6) <=
    prod2list (l1 ++ (a :: nil) ++ l2 ++ (b :: nil) ++ l3)
      (l4 ++ (c :: nil) ++ l5 ++ (d :: nil) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto.
apply plus_le_compat; auto with arith.
repeat rewrite plus_assoc; apply plus_le_compat; auto.
repeat rewrite (fun x y z => plus_comm (prod2list (x :: y) z)).
repeat rewrite plus_assoc_reverse; apply plus_le_compat; auto.
unfold prod2list in |- *; simpl in |- *.
rewrite le_plus_minus with (1 := H3); auto.
rewrite le_plus_minus with (1 := H2); auto.
replace
 ((b + (a - b)) * (sum_leaves f d + (sum_leaves f c - sum_leaves f d)) +
  weight_tree f c + (b * sum_leaves f d + weight_tree f d)) with
 ((b + (a - b)) * sum_leaves f d + weight_tree f d +
  ((b + (a - b)) * (sum_leaves f c - sum_leaves f d) + b * sum_leaves f d +
   weight_tree f c)); [ idtac | ring ].
apply plus_le_compat; auto with arith.
apply plus_le_compat; auto with arith.
repeat rewrite mult_plus_distr_l || rewrite mult_plus_distr_r;
 auto with arith.
replace (b * sum_leaves f d + b * (sum_leaves f c - sum_leaves f d)) with
 (b * (sum_leaves f c - sum_leaves f d) + 0 + b * sum_leaves f d);
 [ auto with arith | ring ].
Qed.

(* Permuting two choosen elements with same integer does not change the product *)
Theorem prod2list_eq :
 forall a b c l1 l2 l3 l4 l5 l6,
 length l1 = length l4 ->
 length l2 = length l5 ->
 length l3 = length l6 ->
 prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ b :: l5 ++ c :: l6) =
 prod2list (l1 ++ a :: l2 ++ a :: l3) (l4 ++ c :: l5 ++ b :: l6).
Proof using.
intros a b c l1 l2 l3 l4 l5 l6 H H0 H1;
 change
   (prod2list (l1 ++ (a :: nil) ++ l2 ++ (a :: nil) ++ l3)
      (l4 ++ (b :: nil) ++ l5 ++ (c :: nil) ++ l6) =
    prod2list (l1 ++ (a :: nil) ++ l2 ++ (a :: nil) ++ l3)
      (l4 ++ (c :: nil) ++ l5 ++ (b :: nil) ++ l6)) 
  in |- *.
repeat rewrite prod2list_app; auto with arith.
ring.
Qed.

(* Putting the smallest tree with the smallest integer lower the product *)
Theorem prod2list_reorder :
 forall a b b1 l1 l2 l3 l4 l5,
 length l1 = length l3 ->
 length l2 = length l4 ->
 (forall b, In b l1 -> b <= a) ->
 (forall b, In b l2 -> b <= a) ->
 permutation (l3 ++ b :: l4) (b1 :: l5) ->
 ordered (sum_order f) (b1 :: l5) ->
 exists l6 : _,
   (exists l7 : _,
      length l1 = length l6 /\
      length l2 = length l7 /\
      permutation (b1 :: l5) (l6 ++ b1 :: l7) /\
      prod2list (l1 ++ a :: l2) (l6 ++ b1 :: l7) <=
      prod2list (l1 ++ a :: l2) (l3 ++ b :: l4)).
Proof using.
intros a b b1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
cut (In b (b1 :: l5));
 [ simpl in |- *; intros [HH0| HH0]
 | apply permutation_in with (1 := H3); auto with datatypes ].
exists l3; exists l4; repeat (split; auto).
pattern b1 at 2 in |- *; rewrite HH0; apply permutation_sym; auto.
rewrite HH0; auto.
cut (In b1 (l3 ++ b :: l4));
 [ intros HH1
 | apply permutation_in with (1 := permutation_sym _ _ _ H3);
    auto with datatypes ].
case in_app_or with (1 := HH1); intros HH2.
case in_ex_app with (1 := HH2).
intros l6 (l7, HH3); exists (l6 ++ b :: l7); exists l4; repeat (split; auto).
apply trans_equal with (1 := H).
rewrite HH3; repeat rewrite length_app; simpl in |- *; auto with arith.
apply permutation_sym; apply permutation_trans with (2 := H3); auto.
rewrite HH3.
repeat rewrite app_ass.
simpl in |- *; apply permutation_transposition.
rewrite HH3; auto.
repeat rewrite app_ass.
case (same_length_ex _ _ b1 l6 l7 l1); auto.
rewrite <- HH3; auto.
intros l8 (l9, (b2, (HH4, (HH5, HH6)))).
rewrite HH6.
repeat rewrite app_ass; simpl in |- *.
apply prod2list_le_l; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply le_trans with (1 := H5);
 auto.
apply H1; rewrite HH6; auto with datatypes.
simpl in HH2; case HH2; intros HH3.
exists l3; exists l4; repeat (split; auto); try (rewrite <- HH3; auto; fail).
pattern b1 at 2 in |- *; rewrite <- HH3; apply permutation_sym; auto.
case in_ex_app with (1 := HH3).
intros l6 (l7, HH4); exists l3; exists (l6 ++ b :: l7); repeat (split; auto).
apply trans_equal with (1 := H0).
rewrite HH4; repeat rewrite length_app; simpl in |- *; auto with arith.
apply permutation_sym; apply permutation_trans with (2 := H3); auto.
rewrite HH4.
simpl in |- *; apply permutation_transposition.
rewrite HH4; auto.
case (same_length_ex _ _ b1 l6 l7 l2); auto.
rewrite <- HH4; auto.
intros l8 (l9, (b2, (HH5, (HH6, HH7)))).
rewrite HH7.
apply prod2list_le_r; auto.
change (sum_order f b1 b) in |- *.
apply ordered_trans with (2 := H4); auto.
unfold sum_order in |- *; intros a0 b0 c H5 H6; apply le_trans with (1 := H5);
 auto.
apply H2; rewrite HH7; auto with datatypes.
Qed.

(* Putting the smallest tree with the smallest integer lower the product *) 
Theorem prod2list_reorder2 :
 forall a b c b1 c1 l1 l2 l3 l4 l5,
 length l1 = length l3 ->
 length l2 = length l4 ->
 (forall b, In b l1 -> b <= a) ->
 (forall b, In b l2 -> b <= a) ->
 permutation (l3 ++ b :: c :: l4) (b1 :: c1 :: l5) ->
 ordered (sum_order f) (b1 :: c1 :: l5) ->
 exists l6 : _,
   (exists l7 : _,
      length l1 = length l6 /\
      length l2 = length l7 /\
      permutation (b1 :: c1 :: l5) (l6 ++ b1 :: c1 :: l7) /\
      prod2list (l1 ++ a :: a :: l2) (l6 ++ b1 :: c1 :: l7) <=
      prod2list (l1 ++ a :: a :: l2) (l3 ++ b :: c :: l4)).
Proof using.
intros a b c b1 c1 l1 l2 l3 l4 l5 H H0 H1 H2 H3 H4.
case (prod2list_reorder a b b1 l1 (a :: l2) l3 (c :: l4) (c1 :: l5));
 simpl in |- *; auto.
intros b0 [H5| H5]; auto.
rewrite H5; auto.
intros l6 (l7, (HH1, (HH2, (HH3, HH4)))).
generalize HH2 HH3 HH4; case l7; clear HH2 HH3 HH4 l7.
intros; discriminate.
intros c2 l7 HH2 HH3 HH4.
case (prod2list_reorder a c2 c1 l1 l2 l6 l7 l5); simpl in |- *; auto.
apply permutation_inv with (a := b1); auto.
apply permutation_sym; apply permutation_trans with (1 := HH3).
change
  (permutation (l6 ++ (b1 :: nil) ++ c2 :: l7)
     (((b1 :: nil) ++ l6) ++ c2 :: l7)) in |- *.
repeat rewrite <- app_ass.
apply permutation_app_comp; auto.
apply ordered_inv with (1 := H4); auto.
intros l8 (l9, (HH5, (HH6, (HH7, HH8)))).
exists l8; exists l9; repeat (split; auto).
apply permutation_trans with ((b1 :: c1 :: l9) ++ l8); auto.
simpl in |- *; apply permutation_skip; auto.
apply permutation_trans with (1 := HH7).
apply permutation_trans with ((c1 :: l9) ++ l8); auto.
apply le_trans with (2 := HH4).
change
  (prod2list (l1 ++ (a :: nil) ++ a :: l2) (l8 ++ (b1 :: nil) ++ c1 :: l9) <=
   prod2list (l1 ++ (a :: nil) ++ a :: l2) (l6 ++ (b1 :: nil) ++ c2 :: l7))
 in |- *.
generalize HH8; repeat rewrite prod2list_app; auto with arith.
intros HH9.
repeat rewrite plus_assoc.
repeat rewrite (fun x => plus_comm (prod2list l1 x)).
repeat rewrite plus_assoc_reverse; auto with arith.
Qed.
 
End Prod2List.
Arguments prod2list [A].
