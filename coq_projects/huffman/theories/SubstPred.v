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
    Proof of Huffman algorithm: SubstPred.v                          
                                                                     
    Definition of the substitution in a tree with respect to a cover 
                                                                     
    Definition: subst_pred                                           
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Import HeightPred.
 
Section SubstPred.
Variable A : Type.

(* Take two covers an substitute the elements of one by the element of the other *)
Inductive subst_pred :
list (btree A) -> list (btree A) -> btree A -> btree A -> Prop :=
  | subst_pred_id :
      forall (t1 t2 : btree A) (l1 l2 : list (btree A)),
      subst_pred (t1 :: nil) (t2 :: nil) t1 t2
  | subst_pred_node :
      forall (t1 t2 t3 t4 : btree A) (l1 l2 l3 l4 l5 l6 : list (btree A)),
      subst_pred l1 l2 t1 t2 ->
      subst_pred l3 l4 t3 t4 ->
      subst_pred (l1 ++ l3) (l2 ++ l4) (node t1 t3) (node t2 t4).
Hint Resolve subst_pred_id subst_pred_node : core.

(* The first cover of the substitution is an ordered cover *)
Theorem subst_pred_ordered_cover_l :
 forall (t1 t2 : btree A) (l1 l2 : list (btree A)),
 subst_pred l1 l2 t1 t2 -> ordered_cover l1 t1.
Proof using.
intros t1 t2 l1 l2 H; elim H; auto.
Qed.

(* The second cover of the substitution is an ordered cover *)
Theorem subst_pred_ordered_cover_r :
 forall (t1 t2 : btree A) (l1 l2 : list (btree A)),
 subst_pred l1 l2 t1 t2 -> ordered_cover l2 t2.
Proof using.
intros t1 t2 l1 l2 H; elim H; auto.
Qed.

(* The two covers have same length *)
Theorem subst_pred_length :
 forall (t1 t2 : btree A) (l1 l2 : list (btree A)),
 subst_pred l1 l2 t1 t2 -> length l1 = length l2.
Proof using.
intros t1 t2 l1 l2 H; elim H; auto.
intros t0 t3 t4 t5 l0 l3 l4 l5 l6 l7 H0 H1 H2 H3; repeat rewrite length_app; auto.
Qed.

(* An ordered cover can  be completed in a substitution *)
Theorem ordered_cover_subst_pred :
 forall (t1 : btree A) (l1 l2 : list (btree A)),
 ordered_cover l1 t1 ->
 length l1 = length l2 -> exists t2 : btree A, subst_pred l1 l2 t1 t2.
Proof using.
intros t1 l1 l2 H; generalize l2; elim H; clear t1 l1 l2 H.
intros t l l2; case l2.
simpl in |- *; intros; discriminate.
intros b l0; case l0; simpl in |- *; auto.
intros H; exists b; auto.
intros; discriminate.
intros t1 t2 l1 l2 l3 H H0 H1 H2 l0 H3.
case (H0 (first_n l0 (length l1))); auto.
rewrite first_n_length; auto;
 (rewrite <- H3; rewrite length_app; auto with arith).
intros t4 HH1.
case (H2 (skip_n l0 (length l1))); auto.
rewrite skip_n_length; auto;
 (rewrite <- H3; rewrite length_app; rewrite minus_plus; auto with arith).
intros t5 HH2.
exists (node t4 t5); auto.
rewrite <- (first_n_skip_n_app _ (length l1) l0); auto.
Qed.

(* A height predicate can be completed in a substitution *) 
Theorem height_pred_subst_pred :
 forall (n : nat) (ln : list nat) (t1 : btree A) (l1 l2 : list (btree A)),
 height_pred n ln l1 t1 ->
 length l1 = length l2 ->
 exists t2 : btree A, height_pred n ln l2 t2 /\ subst_pred l1 l2 t1 t2.
Proof using.
intros n ln t1 l1 l2 H; generalize l2; elim H; clear H n ln t1 l1 l2; auto.
intros n t l2; case l2.
simpl in |- *; intros; discriminate.
intros b l0; case l0; intros; try discriminate; exists b; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 l0 H3.
case (H0 (first_n l0 (length l1))); auto.
rewrite first_n_length; auto;
 (rewrite <- H3; rewrite length_app; auto with arith).
intros t4 (HH1, HH2).
case (H2 (skip_n l0 (length l1))); auto.
rewrite skip_n_length; auto;
 (rewrite <- H3; rewrite length_app; rewrite minus_plus; auto with arith).
intros t5 (HH3, HH4).
exists (node t4 t5); rewrite <- (first_n_skip_n_app _ (length l1) l0); auto.
Qed.
 
End SubstPred.
Arguments subst_pred [A].
Hint Resolve subst_pred_id : core.
