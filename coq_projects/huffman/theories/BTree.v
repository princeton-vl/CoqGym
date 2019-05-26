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
    Proof of Huffman algorithm: BTree.v                              
                                                                     
    Definition and some properties of binary trees                   
                                                                     
    Definitions:                                                     
        btree, inb, all_leaves, distinct_leaves, compute_code,
        number_of_nodes        
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export Code.
From Huffman Require Export ISort.
Require Export Compare_dec.
From Huffman Require Export Weight.
From Huffman Require Export UniqueKey.
Require Import ArithRing.
 
Section Tree.
Variable A : Type.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.
Variable empty : A.

(* Definition of binary trees *)
Inductive btree : Type :=
  | leaf : A -> btree
  | node : btree -> btree -> btree.

(* Predicate that defines belonging *)
Inductive inb : btree -> btree -> Prop :=
  | inleaf : forall t : btree, inb t t
  | innodeL : forall t t1 t2 : btree, inb t t1 -> inb t (node t1 t2)
  | innodeR : forall t t1 t2 : btree, inb t t2 -> inb t (node t1 t2).
Hint Constructors inb : core.

(* inb is transitive *)
Theorem inb_trans : forall t1 t2 t3, inb t1 t2 -> inb t2 t3 -> inb t1 t3.
Proof using.
intros t1 t2 t3 H H1; generalize t1 H; elim H1; clear H H1 t1 t2 t3; auto.
Qed.

(* A tree has at least one leaf  *)
Theorem inb_ex : forall t : btree, exists x : _, inb (leaf x) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a; exists a; auto.
intros b (a, H) b0 H0; exists a; auto.
Qed.

(* Compute the number of nodes of a tree *) 
Fixpoint number_of_nodes (b : btree) : nat :=
  match b with
  | leaf _ => 0
  | node b1 b2 => S (number_of_nodes b1 + number_of_nodes b2)
  end.

(* Belonging gives smaller trees *)
Theorem number_of_nodes_inb_le :
 forall t1 t2, inb t1 t2 -> number_of_nodes t1 <= number_of_nodes t2.
Proof using.
intros t1 t2 H; elim H; clear H t1 t2; simpl in |- *; auto.
intros t t1 t2 H H0; apply le_trans with (1 := H0); auto with arith.
intros t t1 t2 H H0; apply le_trans with (1 := H0); auto with arith.
Qed.

(* Belonging is anisymmetric *)
Theorem inb_antisym : forall t1 t2 : btree, inb t1 t2 -> inb t2 t1 -> t1 = t2.
Proof using.
intros t1 t2 H; elim H; auto.
intros t t0 t3 H0 H1 H2.
absurd (number_of_nodes (node t0 t3) <= number_of_nodes t).
rewrite H1; simpl in |- *; auto with arith.
apply inb_trans with (2 := H2); auto.
apply number_of_nodes_inb_le; auto.
intros t t0 t3 H0 H1 H2.
absurd (number_of_nodes (node t0 t3) <= number_of_nodes t).
rewrite H1; simpl in |- *; auto with arith.
apply inb_trans with (2 := H2); auto.
apply number_of_nodes_inb_le; auto.
Qed.

(* equality on trees is decidable  *)
Definition btree_dec : forall a b : btree, {a = b} + {a <> b}.
intros a; elim a.
intros a1 b; case b.
intros b1; case (eqA_dec a1 b1).
intros e; left; rewrite e; auto.
intros e; right; Contradict e; inversion e; auto.
intros b0 b1; right; red in |- *; intros H; discriminate.
intros b H b0 H0 b1; case b1.
intros a0; right; red in |- *; intros H1; discriminate.
intros b2 b3; case (H b2); intros H1.
case (H0 b3); intros H2.
left; rewrite H1; rewrite H2; auto.
right; rewrite H1; Contradict H2; inversion H2; auto.
right; Contradict H1; inversion H1; auto.
Defined.

(* Belonging is decidable *)
Definition inb_dec : forall a p, {inb a p} + {~ inb a p}.
intros a; elim a; simpl in |- *; auto; clear a.
intros a p; elim p; simpl in |- *; auto; clear p.
intros a1; case (eqA_dec a a1); intros Ha.
left; rewrite Ha; simpl in |- *; auto.
right; red in |- *; Contradict Ha; inversion Ha; auto.
intros b [H| H]; auto.
intros b0 [H1| H1]; auto.
right; red in |- *; intros H2; inversion H2.
case H; auto.
case H1; auto.
intros b H b0 H0 p; elim p; auto.
intros a; right; red in |- *; intros H1; inversion H1.
intros b1 H1 b2 H2.
case H1; intros H3; auto.
case H2; intros H4; auto.
case (btree_dec (node b b0) (node b1 b2)); intros H5.
left; rewrite H5; auto.
right; red in |- *; intros H6; inversion H6; auto.
case H5; rewrite H9; rewrite H10; auto.
Defined.

(* Compute all the leaves of the tree *)
Fixpoint all_leaves (t : btree) : list A :=
  match t with
  | leaf a => a :: nil
  | node t1 t2 => all_leaves t1 ++ all_leaves t2
  end.

(* A leaf is in the list of all leaves *)
Theorem all_leaves_in : forall t a, inb (leaf a) t -> In a (all_leaves t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 H; inversion H; auto.
intros b H b0 H0 a H1; apply in_or_app; inversion H1; auto.
Qed.

(* An element of a list of all leaves is a leaf *)
Theorem all_leaves_inb : forall t a, In a (all_leaves t) -> inb (leaf a) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 [H| H]; [ rewrite H | case H ]; auto.
intros b H b0 H0 a H1; case in_app_or with (1 := H1); auto.
Qed.

(* The property for a tree to have distinct leaves  *)
Definition distinct_leaves (t : btree) : Prop :=
  forall t0 t1 t2 : btree,
  inb (node t1 t2) t -> inb t0 t1 -> inb t0 t2 -> False.

(* A leaf tree has distinct leaves  *)
Theorem distinct_leaves_leaf : forall a : A, distinct_leaves (leaf a).
Proof using.
intros a; red in |- *.
intros a0 t1 t2 H; inversion H.
Qed.
Hint Resolve distinct_leaves_leaf : core.

(* An inversion theorem for node *)
Theorem distinct_leaves_l :
 forall t1 t2 : btree, distinct_leaves (node t1 t2) -> distinct_leaves t1.
Proof using.
intros t1 t2 H; red in |- *.
intros a t0 t3 H0 H1 H2.
apply (H a t0 t3); auto.
Qed.

(* An inversion theorem for node *)
Theorem distinct_leaves_r :
 forall t1 t2 : btree, distinct_leaves (node t1 t2) -> distinct_leaves t2.
Proof using.
intros t1 t2 H; red in |- *.
intros a t0 t3 H0 H1 H2.
apply (H a t0 t3); auto.
Qed.

(* If list of all the leaves of the tree is unique then the tree has distinct leaves *)
Theorem all_leaves_unique :
 forall t, ulist (all_leaves t) -> distinct_leaves t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros b H b0 H0 H1; red in |- *.
intros t0 t1 t2 H2; inversion H2.
intros H4 H7; case (inb_ex t0); intros a HH.
apply ulist_app_inv with (a := a) (1 := H1); auto; apply all_leaves_in;
 apply inb_trans with (1 := HH); auto.
apply H; auto; try apply ulist_app_inv_l with (1 := H1).
apply H0; auto; try apply ulist_app_inv_r with (1 := H1).
Qed.

(* If the tree has distinct leaves then the list of all the leaves of the tree is unique *)
Theorem all_leaves_ulist :
 forall t, distinct_leaves t -> ulist (all_leaves t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros b H b0 H0 H1; apply ulist_app; auto.
apply H; apply distinct_leaves_l with (1 := H1).
apply H0; apply distinct_leaves_r with (1 := H1).
intros a H2 H3; case (H1 (leaf a) b b0); auto.
apply all_leaves_inb with (1 := H2).
apply all_leaves_inb with (1 := H3).
Qed.

(* Uniqueleaf is decidable *)
Definition distinct_leaves_dec :
  forall a, {distinct_leaves a} + {~ distinct_leaves a}.
intros a; case (ulist_dec A eqA_dec (all_leaves a)); intros H.
left; apply all_leaves_unique; auto.
right; Contradict H; apply all_leaves_ulist; auto.
Defined.

(* Compute the code associated with a binary tree *)
Fixpoint compute_code (a : btree) : list (A * list bool) :=
  match a with
  | leaf b => (b, nil) :: nil
  | node l1 l2 =>
      map
        (fun v : A * list bool =>
         match v with
         | (a1, b1) => (a1, false :: b1)
         end) (compute_code l1) ++
      map
        (fun v : A * list bool =>
         match v with
         | (a1, b1) => (a1, true :: b1)
         end) (compute_code l2)
  end.

(* The computed code is never empty *)
Theorem length_compute_lt_O : forall t, 0 < length (compute_code t).
Proof using.
intros t; elim t; simpl in |- *; auto with arith.
intros b H b0 H0; rewrite length_app.
replace 0 with (0 + 0); auto with arith.
apply plus_lt_compat.
generalize H; elim (compute_code b); simpl in |- *; auto with arith.
generalize H0; elim (compute_code b0); simpl in |- *; auto with arith.
Qed.
Hint Resolve length_compute_lt_O : core.

(* If the computed code has a key it was a leaf of the tree *)
Theorem inCompute_inb :
 forall (t : btree) (a : A) (l : list bool),
 In (a, l) (compute_code t) -> inb (leaf a) t.
Proof using.
intros t; elim t; simpl in |- *; auto.
intros a a0 l [H1| H1]; try (case H1; fail).
injection H1; intros H2 H3; rewrite H3; auto.
intros h H h0 H0 a l H1.
case in_app_or with (1 := H1); auto; intros H2.
case in_map_inv with (1 := H2).
intros (a1, l1) (Ha1, Hl1); auto.
apply innodeL; apply (H a l1).
injection Hl1; intros Hl2 Hl3; rewrite Hl3; auto.
case in_map_inv with (1 := H2).
intros (a1, l1) (Ha1, Hl1); auto.
apply innodeR; apply (H0 a l1).
injection Hl1; intros Hl2 Hl3; rewrite Hl3; auto.
Qed.

(* For every leaf in the tree there is an associated key in the code *)
Theorem inb_compute_ex :
 forall a p, inb (leaf a) p -> exists l : _, In (a, l) (compute_code p).
Proof using.
intros a p; elim p; simpl in |- *; auto.
intros a0 H; inversion H.
exists (nil (A:=bool)); auto.
intros p0 H p1 H0 H1; inversion H1.
case H; auto.
intros x Hx; exists (false :: x).
apply in_or_app; left; auto.
change
  (In ((fun v => match v with
                 | (a1, b1) => (a1, false :: b1)
                 end) (a, x))
     (map (fun v => match v with
                    | (a1, b1) => (a1, false :: b1)
                    end) (compute_code p0))) in |- *; 
 apply in_map; auto.
case H0; auto.
intros x Hx; exists (true :: x).
apply in_or_app; right; auto.
change
  (In ((fun v => match v with
                 | (a1, b1) => (a1, true :: b1)
                 end) (a, x))
     (map (fun v => match v with
                    | (a1, b1) => (a1, true :: b1)
                    end) (compute_code p1))) in |- *; 
 apply in_map; auto.
Qed.

(* The computed code is in the alphabet of its leaves *)
Theorem in_alphabet_compute_code :
 forall m t,
 (forall a : A, In a m -> inb (leaf a) t) -> in_alphabet m (compute_code t).
Proof using.
intros m; elim m; simpl in |- *; auto.
intros a l H t H0; cut (inb (leaf a) t); auto; intros H1.
case inb_compute_ex with (1 := H1).
intros l1 Hl1; apply in_alphabet_cons with (ca := l1); auto.
Qed.

(* Two associations in the list with same prefix have same key *)
Theorem btree_unique_prefix1 :
 forall (t : btree) (a1 a2 : A) (lb1 lb2 : list bool),
 In (a1, lb1) (compute_code t) ->
 In (a2, lb2) (compute_code t) -> is_prefix lb1 lb2 -> a1 = a2.
Proof using.
intros t; elim t; simpl in |- *.
intros leaf1 a1 a2 lb1 lb2 H1 H2.
case H1; intros H3; [ injection H3 | case H3 ].
case H2; intros H4; [ injection H4 | case H4 ].
intros H H0 H5 H6 H7; apply trans_equal with (2 := H0); auto.
intros t1 Rec1 t2 Rec2 a1 a2 lb1 lb2 H1 H2.
case (in_app_or _ _ _ H1); case (in_app_or _ _ _ H2); clear H1 H2;
 intros H2 H1 H3.
generalize H1 H2; inversion H3.
intros H4; case in_map_inv with (1 := H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec1 with (lb1 := l1) (lb2 := l2); auto.
case in_map_inv with (1 := H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case in_map_inv with (1 := H6).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
generalize H3.
case in_map_inv with (1 := H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case in_map_inv with (1 := H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H3.
case in_map_inv with (1 := H1).
intros x; case x; intros aa1 ll1 (H4, H5).
case in_map_inv with (1 := H2).
intros x1; case x1; intros aa2 ll2 (H6, H7).
inversion H5; inversion H7; intros tH8; inversion tH8.
generalize H1 H2; inversion H3.
intros H4; case in_map_inv with (1 := H4).
intros x; case x; intros x1 x2 (H5, H6); discriminate.
intros H5 H6; apply Rec2 with (lb1 := l1) (lb2 := l2); auto.
case in_map_inv with (1 := H5).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
case in_map_inv with (1 := H6).
intros x; case x.
intros a l (H7, H8); injection H8.
intros R1 R2 R3; rewrite R1; rewrite R3; auto.
Qed.

(* If a tree has distinc leaves its computed tree has unique keys *)
Theorem btree_unique_prefix2 :
 forall t : btree, distinct_leaves t -> unique_key (compute_code t).
Proof using.
intros t; elim t; simpl in |- *; auto.
intros b H b0 H0 H1.
apply unique_key_app; auto.
apply unique_key_map; auto.
apply H; apply distinct_leaves_l with (1 := H1); auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
apply unique_key_map; auto.
apply H0; apply distinct_leaves_r with (1 := H1); auto.
intros (a1, b1) (a2, b2); simpl in |- *; auto.
intros a b1 c H2 H3.
case in_map_inv with (1 := H2); auto; case in_map_inv with (1 := H3); auto.
intros (a1, l1) (Ha1, Hl1) (a2, l2) (Ha2, Hl2).
apply (H1 (leaf a) b b0); auto.
injection Hl2; intros HH1 HH2; rewrite HH2.
apply inCompute_inb with (1 := Ha2).
injection Hl1; intros HH1 HH2; rewrite HH2.
apply inCompute_inb with (1 := Ha1).
Qed.

(* If a tree has distinct leaves its code is prefix *)
Theorem btree_unique_prefix :
 forall t : btree, distinct_leaves t -> unique_prefix (compute_code t).
Proof using.
intros t H1; split; try exact (btree_unique_prefix1 t);
 apply btree_unique_prefix2; auto.
Qed.
 
End Tree.
Arguments leaf [A].
Arguments node [A].
Arguments inb [A].
Arguments all_leaves [A].
Arguments distinct_leaves [A].
Arguments compute_code [A].
Arguments number_of_nodes [A].
Hint Constructors inb : core.
Hint Resolve distinct_leaves_leaf : core.
Hint Resolve length_compute_lt_O : core.
