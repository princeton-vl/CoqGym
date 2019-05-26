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
    Proof of Huffman algorithm: Cover.v                              
                                                                     
    Definition of a cover for a tree and some properties             
                                                                     
    Definitions: cover                                               
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export BTree.
From Huffman Require Export Permutation.
Require Import ArithRing.
 
Section Cover.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable empty : A.

(* 
  A list of trees is a cover of a tree if all the trees in the
  list delimit a frontier in the tree
*)
Inductive cover : list (btree A) -> btree A -> Prop :=
  | cover_one : forall t, cover (t :: nil) t
  | cover_node :
      forall l1 l2 t1 t2 t3,
      permutation l1 (t1 :: t2 :: l2) ->
      cover (node t1 t2 :: l2) t3 -> cover l1 t3.
Hint Constructors cover : core.


(* Covers are compatible with permutation *)
Theorem cover_permutation :
 forall t l1 l2, cover l1 t -> permutation l1 l2 -> cover l2 t.
Proof using.
intros t l1 l2 H; generalize l2; elim H; clear H t l1 l2; auto.
intros t l2 H; rewrite (permutation_one_inv _ _ _ H); auto.
intros l1 l2 t1 t2 t3 H H0 H1 l0 H2.
apply cover_node with (2 := H0).
apply permutation_trans with (2 := H).
apply permutation_sym; auto.
Qed.

(* A trivial way to cover a node *)
Theorem cover_cons_l :
 forall t1 t2 l1, cover l1 t1 -> cover (t2 :: l1) (node t2 t1).
intros t1 t2 l1 H; elim H; clear t1 l1 H; simpl in |- *; auto.
intros t; apply cover_node with (l2 := nil (A:=btree A)) (t1 := t2) (t2 := t);
 auto.
intros l1 l2 t1 t0 t3 H H0 H1.
apply cover_node with (l2 := t2 :: l2) (t1 := t1) (t2 := t0); auto.
apply permutation_trans with (t2 :: t1 :: t0 :: l2); auto.
apply permutation_trans with (t1 :: t2 :: t0 :: l2); auto.
apply cover_permutation with (1 := H1); auto.
Qed.

(* A cover cannot be empty *)
Theorem cover_not_nil : forall l t, cover l t -> l <> nil.
Proof using.
intros l t H; case H; simpl in |- *; auto.
intros t0; discriminate.
intros l1 l2 t1 t2 t3 H0 H1; red in |- *; intros H2;
 absurd (length l1 = length (t1 :: t2 :: l2)); auto.
rewrite H2; simpl in |- *; intros; discriminate.
apply permutation_length with (1 := H0); auto.
Qed.

(* A non empty list is a cover of something *) 
Theorem one_cover_ex :
 forall l : list (btree A), l <> nil -> exists t : btree A, cover l t.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros H; case H; auto.
intros a l0; case l0; auto.
intros H H0; exists a; auto.
intros b l1 H H0; case H.
red in |- *; intros; discriminate.
intros x H1; exists (node a x).
apply cover_cons_l; auto.
Qed.

(* Subtrees of the cover are subtrees of the tree *)
Theorem cover_in_inb_inb :
 forall l t1 t2 t3, cover l t1 -> In t2 l -> inb t3 t2 -> inb t3 t1.
Proof using.
intros l t1 t2 t3 H; generalize t2 t3; elim H; clear H l t1 t2 t3;
 auto with datatypes.
simpl in |- *; intros t t2 t3 [H1| H1]; auto.
rewrite H1; auto.
case H1.
intros l1 l2 t1 t2 t3 H H0 H1 t0 t4 H2 H3.
cut (In t0 (t1 :: t2 :: l2)); auto.
simpl in |- *; intros [H4| [H4| H4]]; auto with datatypes.
apply (H1 (node t1 t2)); simpl in |- *; auto.
rewrite H4; auto.
apply (H1 (node t1 t2)); simpl in |- *; auto.
rewrite H4; auto.
apply (H1 t0); simpl in |- *; auto.
apply permutation_in with (1 := H); simpl in |- *; auto.
Qed.

(* Trees of the cover are subtrees of the tree *)
Theorem cover_in_inb : forall l t1 t2, cover l t1 -> In t2 l -> inb t2 t1.
Proof using.
intros l t1 t2 H H0; apply cover_in_inb_inb with (1 := H) (2 := H0); auto.
Qed.
 
Let cover_inv_leaf_aux :
  forall t l, cover l t -> forall a : A, t = leaf a -> l = leaf a :: nil.
Proof using.
intros t l H; elim H; simpl in |- *; auto.
intros t0 a H0; apply f_equal2 with (f := cons (A:=btree A)); auto.
intros.
generalize (H2 a H3); intros; discriminate.
Qed.

(* Covers of a leaf are singleton lists *)
Theorem cover_inv_leaf :
 forall (a : A) l, cover l (leaf a) -> l = leaf a :: nil.
Proof using.
intros a l H; (apply cover_inv_leaf_aux with (t := leaf a); auto).
Qed.

(* Singleton cover are composed of the tree *)
Theorem cover_one_inv : forall t1 t2, cover (t1 :: nil) t2 -> t1 = t2.
Proof using.
intros t1 t2 H; inversion H; auto.
absurd (length (t1 :: nil) = length (t0 :: t3 :: l2)).
simpl in |- *; intros; discriminate.
apply permutation_length with (1 := H0); auto.
Qed.
 
Lemma cover_inv_app_aux :
  forall t t1 t2 l,
  cover l t ->
  t = node t1 t2 ->
  l = node t1 t2 :: nil \/
  (exists l1 : _,
     (exists l2 : _, (cover l1 t1 /\ cover l2 t2) /\ permutation l (l1 ++ l2))).
Proof using.
intros t t1 t2 l H; elim H.
intros t0 Ht0; rewrite Ht0; auto with datatypes.
intros l1 l2 t0 t3 t4 H0 H1 H2 H3; right.
case H2; auto.
intros H4.
exists (t1 :: nil); exists (t2 :: nil); simpl in |- *; repeat (split; auto).
injection H4; intros H5 H6 H7; rewrite <- H5; rewrite <- H6; rewrite <- H7;
 auto.
clear H2 H3; intros (l3, (l4, ((Hl1, Hl2), Hl3))).
case (in_app_or l3 l4 (node t0 t3)).
apply permutation_in with (1 := Hl3); auto with datatypes.
intros H2; case in_ex_app with (1 := H2).
intros l5 (l6, Hl5).
exists (t0 :: t3 :: l5 ++ l6); exists l4; repeat (split; auto).
apply cover_node with (l2 := l5 ++ l6) (t1 := t0) (t2 := t3); auto.
apply cover_permutation with (1 := Hl1).
rewrite Hl5.
apply permutation_trans with (node t0 t3 :: l6 ++ l5); auto.
apply (permutation_app_swap _ l5 (node t0 t3 :: l6)).
apply permutation_trans with (1 := H0).
simpl in |- *; repeat apply permutation_skip.
apply permutation_inv with (a := node t0 t3).
apply permutation_trans with (1 := Hl3).
rewrite Hl5; auto.
change
  (permutation ((l5 ++ node t0 t3 :: l6) ++ l4)
     ((node t0 t3 :: l5 ++ l6) ++ l4)) in |- *.
apply permutation_app_comp; auto.
apply permutation_trans with ((node t0 t3 :: l6) ++ l5); auto.
simpl in |- *; auto.
intros H2; case in_ex_app with (1 := H2).
intros l5 (l6, Hl5).
exists l3; exists (t0 :: t3 :: l5 ++ l6); repeat (split; auto).
apply cover_node with (l2 := l5 ++ l6) (t1 := t0) (t2 := t3); auto.
apply cover_permutation with (1 := Hl2).
rewrite Hl5.
apply permutation_trans with (node t0 t3 :: l6 ++ l5); auto.
apply (permutation_app_swap _ l5 (node t0 t3 :: l6)).
apply permutation_trans with (1 := H0).
apply permutation_trans with ((t0 :: t3 :: l5 ++ l6) ++ l3); auto.
simpl in |- *; repeat apply permutation_skip.
apply permutation_inv with (a := node t0 t3).
apply permutation_trans with (1 := Hl3).
rewrite Hl5.
apply permutation_trans with ((l5 ++ node t0 t3 :: l6) ++ l3); auto.
change
  (permutation ((l5 ++ node t0 t3 :: l6) ++ l3)
     ((node t0 t3 :: l5 ++ l6) ++ l3)) in |- *; auto.
apply permutation_app_comp; auto.
apply permutation_trans with ((node t0 t3 :: l6) ++ l5); auto.
simpl in |- *; auto.
Qed.

(* A cover on a node can be splitted in two *)
Theorem cover_inv_app :
 forall t1 t2 l,
 cover l (node t1 t2) ->
 l = node t1 t2 :: nil \/
 (exists l1 : _,
    (exists l2 : _, (cover l1 t1 /\ cover l2 t2) /\ permutation l (l1 ++ l2))).
Proof using.
intros t1 t2 l H; apply cover_inv_app_aux with (t := node t1 t2); auto.
Qed.

(* Covers of the direct subtrees generate a cover of the whole tree *)
Theorem cover_app :
 forall t1 t2 l1 l2,
 cover l1 t1 -> cover l2 t2 -> cover (l1 ++ l2) (node t1 t2).
Proof using.
intros t1 t2 l1 l2 H1; generalize t2 l2; elim H1; clear t1 t2 l1 l2 H1;
 simpl in |- *; auto.
intros t t2 l2 H; apply cover_cons_l; auto.
intros l1 l2 t1 t2 t3 H H0 H1 t0 l0 H2.
apply cover_node with (l2 := l2 ++ l0) (t1 := t1) (t2 := t2); auto.
apply permutation_trans with ((t1 :: t2 :: l2) ++ l0); auto.
Qed.

(* A cover gives a direct account of the number of the tree *)
Theorem cover_number_of_nodes :
 forall t l,
 cover l t ->
 number_of_nodes t =
 fold_left (fun x y => x + number_of_nodes y) l 0 + pred (length l).
Proof using.
intros t l H; elim H; clear H t l; simpl in |- *; auto.
intros l1 l2 t1 t2 t3 H H0 H1.
apply trans_equal with (1 := H1).
rewrite fold_left_permutation with (2 := H); simpl in |- *; auto.
rewrite permutation_length with (1 := H); simpl in |- *; auto.
rewrite fold_left_init with (h := S); simpl in |- *; auto.
intros a b1 b2; repeat rewrite plus_assoc_reverse.
apply f_equal2 with (f := plus); auto; apply plus_comm.
Qed.

(* A local function to compute all covers of a certain length *)
Fixpoint all_cover_aux (l : list (btree A)) (n : nat) {struct n} : list (btree A) :=
  match n with
  | O => nil
  | S n1 =>
      flat_map
        (fun l1 =>
         match l1 with
         | nil => nil
         | a :: nil => a :: nil
         | a :: b :: l2 => all_cover_aux (node a b :: l2) n1
         end) (all_permutations l)
  end.

(* A function to compute all covers *)
Definition all_cover l := all_cover_aux l (length l).

(* The local function generates covers of a given length *)
Theorem all_cover_aux_cover :
 forall (n : nat) l t, n = length l -> In t (all_cover_aux l n) -> cover l t.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l t H H0; elim H0.
intros n0 H l t H0 H1.
case in_flat_map_ex with (1 := H1); clear H1.
intros x; case x; clear x.
simpl in |- *; intros (H1, H2); case H2.
intros b x; case x; clear x.
simpl in |- *; intros (H1, [H2| H2]).
rewrite <- H2.
rewrite permutation_one_inv with (a := b) (l := l); auto.
apply all_permutations_permutation; auto.
case H2.
intros b1 l1 (H1, H2).
apply cover_node with (l2 := l1) (t1 := b) (t2 := b1); auto.
apply permutation_sym; apply all_permutations_permutation; auto.
apply H; auto.
apply eq_add_S; apply trans_equal with (1 := H0).
apply trans_equal with (length (b :: b1 :: l1)); auto.
apply permutation_length.
apply permutation_sym; apply all_permutations_permutation; auto.
Qed.

(* The list of all covers contain only covers *)
Theorem all_cover_cover : forall l t, In t (all_cover l) -> cover l t.
Proof using.
intros l t H; apply all_cover_aux_cover with (n := length l); auto.
Qed.

(* A cover of a given length is in the local list *)
Theorem cover_all_cover_aux :
 forall (n : nat) l t, n = length l -> cover l t -> In t (all_cover_aux l n).
intros n; elim n; simpl in |- *; auto.
intros l; case l; simpl in |- *; auto.
intros t H H0; inversion H0.
generalize (permutation_nil_inv _ _ (permutation_sym _ _ _ H1)); intros;
 discriminate.
intros; discriminate.
intros n0 H l t H0 H1; inversion H1.
simpl in |- *; auto.
apply in_flat_map with (t1 :: t2 :: l2); auto.
apply H; auto.
apply eq_add_S; apply trans_equal with (1 := H0).
apply trans_equal with (length (t1 :: t2 :: l2)); auto.
apply permutation_length; auto.
apply permutation_all_permutations; auto.
apply permutation_sym; auto.
Qed.

(* A cover is in the list of all covers *)
Theorem cover_all_cover : forall l t, cover l t -> In t (all_cover l).
Proof using.
intros l t H; unfold all_cover in |- *; apply cover_all_cover_aux; auto.
Qed.

(* Covers are decidable *)
Definition cover_dec :
  (forall a b : A, {a = b} + {a <> b}) ->
  forall l t, {cover l t} + {~ cover l t}.
intros H l t; case (In_dec (btree_dec _ H) t (all_cover l)).
intros H1; left; apply all_cover_cover; auto.
intros H1; right; Contradict H1; apply cover_all_cover; auto.
Defined.

(* All the leaves of the tree gives a cover to the tree. *)
Theorem cover_all_leaves :
 forall t : btree A, cover (map (fun x : A => leaf x) (all_leaves t)) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros b H b0 H0; rewrite map_app.
apply cover_app; auto.
Qed.
 
End Cover.
Arguments cover [A].
Hint Constructors cover : core.
