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
    Proof of Huffman algorithm: CoverMin.v                           
                                                                     
    Definition of a minimal tree for a cover                         
                                                                     
    Defintion: cover_min                                             
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export Cover.
From Huffman Require Export WeightTree.
 
Section CoverMin.
Variable A : Type.
Variable f : A -> nat.

(* To be a tree of minimum weight for a cover *)
Definition cover_min (l : list (btree A)) (t1 : btree A) : Prop :=
  cover l t1 /\
  (forall t2 : btree A, cover l t2 -> weight_tree f t1 <= weight_tree f t2).

(* Minimum tree for a singleton cover *)
Theorem cover_min_one : forall t : btree A, cover_min (t :: nil) t.
Proof using.
intros t; split; auto.
intros t2 H; inversion H; auto.
generalize (permutation_length _ _ _ H0); simpl in |- *; intros; discriminate.
Qed.
Hint Resolve cover_min_one : core.

(* Minimum trees are preserved by permutation *)
Theorem cover_min_permutation :
 forall (t : btree A) (l1 l2 : list (btree A)),
 cover_min l1 t -> permutation l1 l2 -> cover_min l2 t.
Proof using.
intros t l1 l2 H H0; split.
apply cover_permutation with (2 := H0); auto.
inversion H; auto.
intros t2 H1.
assert (cover l1 t2).
inversion H; auto.
apply cover_permutation with (2 := permutation_sym _ _ _ H0); auto.
inversion H; auto.
Qed.

(* For all covers, there is a minimum tree *)
Theorem cover_min_ex :
 forall l : list (btree A), l <> nil -> exists t : btree A, cover_min l t.
Proof using.
intros l H;
 generalize (find_min_correct (btree A) (weight_tree f) (all_cover _ l)).
case (find_min (weight_tree f) (all_cover _ l)).
intros p; case p.
intros n b ((H1, H2), H3); exists b; auto.
split; auto.
apply all_cover_cover; auto.
intros t2 H4; apply H3.
apply cover_all_cover; auto.
intros H0.
case (one_cover_ex _ l); auto.
intros x H1; absurd (In x (all_cover A l)).
rewrite H0; simpl in |- *; red in |- *; intros H2; case H2.
apply cover_all_cover; auto.
Qed.
 
End CoverMin.
Hint Resolve cover_min_one : core.
