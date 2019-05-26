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
    Proof of Huffman algorithm: SameSumLeaves.v                      
                                                                     
    Definition of the equality of sum leaves                         
                                                                     
    Definition: same_sum_leaves                                      
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export Cover.
From Huffman Require Export WeightTree.
 
Section SameSumLeaves.
Variable A : Type.
Variable f : A -> nat.

(* the sum leaves are the same upto permutation *)
Definition same_sum_leaves (l1 l2 : list (btree A)) : Prop :=
  exists l3 : list (btree A),
    (exists l4 : list (btree A),
       permutation l1 l3 /\
       permutation l2 l4 /\ map (sum_leaves f) l3 = map (sum_leaves f) l4).

(* if the sum leaves are the same, the list are of same length *)
Theorem same_sum_leaves_length :
 forall l1 l2 : list (btree A),
 same_sum_leaves l1 l2 -> length l1 = length l2.
Proof using.
intros l1 l2 (l3, (l4, (H0, (H1, H2)))).
rewrite (permutation_length _ _ _ H0).
rewrite (permutation_length _ _ _ H1).
repeat rewrite <- (length_map _ _ (sum_leaves f)); auto.
apply f_equal with (f := length (A:=nat)); auto.
Qed.
 
End SameSumLeaves.
Arguments same_sum_leaves [A].
