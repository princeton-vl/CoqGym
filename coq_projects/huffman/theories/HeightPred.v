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
    Proof of Huffman algorithm: HeightPred.v                         
                                                                     
    Definition of the predicate that associates a height list        
    with a cover                                                     
                                                                     
    Definition: height_pred                                          
                                    Laurent.Thery@inria.fr (2003)    
 **********************************************************************)

From Huffman Require Export OrderedCover.
From Huffman Require Export WeightTree.
Require Import ArithRing.
From Huffman Require Export Ordered.
From Huffman Require Export Prod2List.
 
Section HeightPred.
Variable A : Type.
Variable f : A -> nat.
Variable eqA_dec : forall a b : A, {a = b} + {a <> b}.

(* 
  A predicate that associates an initial height, a list of
  height, a cover and a tree
*)
Inductive height_pred : nat -> list nat -> list (btree A) -> btree A -> Prop :=
  | height_pred_nil :
      forall (n : nat) (t : btree A), height_pred n (n :: nil) (t :: nil) t
  | height_pred_node :
      forall (n : nat) (ln1 ln2 : list nat) (t1 t2 : btree A)
        (l1 l2 : list (btree A)),
      height_pred (S n) ln1 l1 t1 ->
      height_pred (S n) ln2 l2 t2 ->
      height_pred n (ln1 ++ ln2) (l1 ++ l2) (node t1 t2).
Hint Resolve height_pred_nil height_pred_node : core.

(* The cover is an ordered cover *)
Theorem height_pred_ordered_cover :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> ordered_cover l t.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
Qed.

(* The height list is never empty *)
Theorem height_pred_not_nil1 :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> ln <> nil.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros; discriminate.
intros n0 ln1 ln2 t1 t2 l1 l2 H0; case ln1; simpl in |- *; auto.
intros; discriminate.
Qed.

(* The cover list is never empty *) 
Theorem height_pred_not_nil2 :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> l <> nil.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros; discriminate.
intros n0 ln1 ln2 t1 t2 l1 l2 H0; case l1; simpl in |- *; auto.
intros; discriminate.
Qed.

(* The height and cover lists have same length *)
Theorem height_pred_length :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> length ln = length l.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros; repeat rewrite length_app; auto with arith.
Qed.

(* 
  The height and cover list gives a simple relation between
  weight_tree, sum_leaves and the product of the two lists
*)
Theorem height_pred_weight :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t ->
 n * sum_leaves f t + weight_tree f t = prod2list f ln l.
Proof using.
intros n ln t l H; elim H; simpl in |- *; auto.
intros n0 ln1 ln2 t1 t2 l1 l2 H0 H1 H2 H3.
rewrite prod2list_app; auto with arith.
rewrite <- H3; rewrite <- H1; ring.
apply height_pred_length with (1 := H0); auto.
Qed.

(* Ordered covers can be completed with a height list *)
Theorem ordered_cover_height_pred :
 forall (n : nat) (t : btree A) (l : list (btree A)),
 ordered_cover l t -> exists ln : list nat, height_pred n ln l t.
Proof using.
intros n t l H; generalize n; elim H; clear n t l H.
intros t l n; exists (n :: nil); auto.
intros t1 t2 l1 l2 l3 H H0 H1 H2 n.
case (H0 (S n)); intros ln1 HH1.
case (H2 (S n)); intros ln2 HH2.
exists (ln1 ++ ln2); auto.
Qed.

(* Elements in the height list are always larger than the initial height *) 
Theorem height_pred_larger :
 forall (n n1 : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> In n1 ln -> n <= n1.
Proof using.
intros n n1 ln t l H; generalize n1; elim H; clear H n ln t l n1;
 auto with arith.
intros n t n1 [H2| H2]; [ rewrite H2 | case H2 ]; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 n1 H3; apply le_trans with (S n);
 auto with arith.
case in_app_or with (1 := H3); auto.
Qed.

(* 
  In the height list is not a singleton, all its element are
  strictly larger than the initial height
*) 
Theorem height_pred_larger_strict :
 forall (n n1 : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> In n1 ln -> n < n1 \/ ln = n :: nil /\ l = t :: nil.
Proof using.
intros n n1 ln t l H; generalize n1; elim H; clear H n ln t l n1; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 n1 H3; left;
 apply lt_le_trans with (S n); auto.
case in_app_or with (1 := H3).
intros H4; apply height_pred_larger with (1 := H); auto.
intros H4; apply height_pred_larger with (1 := H1); auto.
Qed.

(* There always a larger element that the initial height in the heigh list *)
Theorem height_pred_larger_ex :
 forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
 height_pred n ln l t -> exists n1 : _, In n1 ln /\ n <= n1.
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t; exists n; auto with datatypes.
intros n ln1 ln2 t1 t2 l1 l2 H (n1, (HH1, HH2)) H1 H2.
exists n1; auto with datatypes arith.
Qed.
 
Lemma height_pred_disj_larger_aux :
  forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
  height_pred n ln l t ->
  forall ln1 ln2 a,
  ln = ln1 ++ a :: ln2 ->
  (forall n1 : nat, In n1 ln1 -> n1 < a) ->
  (forall n1 : nat, In n1 ln2 -> n1 <= a) ->
  (exists ln3 : _, ln2 = a :: ln3) \/ ln = n :: nil /\ l = t :: nil.
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t l ln1 ln2 a; case ln1; simpl in |- *; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 ln0 ln3 a H3 H4 H5.
case app_inv_app with (1 := H3).
intros (ln4, H7); auto.
cut (ln3 = ln4 ++ ln2);
 [ intros E1
 | apply app_inv_head with (l1 := ln0 ++ a :: nil); repeat rewrite app_ass;
    simpl in |- *; rewrite <- H3; rewrite H7; rewrite app_ass; 
    auto ].
case H0 with (1 := H7); auto; clear H0 H2.
intros n1 H8; apply H5; rewrite E1; auto with datatypes.
intros (ln5, HH); left; exists (ln5 ++ ln2).
apply trans_equal with (1 := E1); rewrite HH; auto.
intros (HH1, HH2).
cut (ln0 = nil /\ ln4 = nil /\ a = S n);
 [ intros (HH3, (HH4, HH5))
 | generalize HH1; rewrite H7; case ln0; simpl in |- *;
    [ case ln4; try (intros; discriminate); (intros HH6; injection HH6; auto)
    | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
generalize E1 H1; case ln2; simpl in |- *; auto; clear E1 H1.
intros E1 H1; case height_pred_not_nil2 with (1 := H1); auto.
generalize (height_pred_length _ _ _ _ H1); case l2; simpl in |- *; auto;
 intros; discriminate.
intros n0 ln5 E1 H1; case height_pred_larger_strict with (n1 := n0) (1 := H1);
 simpl in |- *; auto with datatypes.
intros HH6; Contradict HH6; apply le_not_lt; rewrite <- HH5; apply H5;
 rewrite E1; auto with datatypes.
intros (H8, H9); left; exists (nil (A:=nat)); injection H8.
intros HH7 HH8; rewrite HH5; rewrite <- HH8; rewrite <- HH7; rewrite E1;
 rewrite HH4; auto.
intros (ln4, H7); auto.
cut (ln0 = ln1 ++ ln4);
 [ intros E1
 | apply app_inv_tail with (l1 := a :: ln3); rewrite <- H3; rewrite H7;
    rewrite app_ass; auto ].
case H2 with (1 := H7); auto.
intros n1 H6; apply H4; rewrite E1; auto with datatypes.
intros (HH1, HH2).
cut (ln3 = nil /\ ln4 = nil /\ a = S n);
 [ intros (HH3, (HH4, HH5))
 | generalize HH1; rewrite H7; case ln4; simpl in |- *;
    [ case ln3; try (intros; discriminate); (intros HH6; injection HH6; auto)
    | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H); auto.
intros n1; rewrite <- HH5; intros (HH6, HH7).
Contradict HH7; apply lt_not_le; apply H4; rewrite E1; auto with datatypes.
Qed.

(* The first maximum height in the list is immediately repeated once *)
Theorem height_pred_disj_larger :
 forall (n a : nat) (ln1 ln2 : list nat) (t : btree A) (l : list (btree A)),
 height_pred n (ln1 ++ a :: ln2) l t ->
 (forall n1 : nat, In n1 ln1 -> n1 < a) ->
 (forall n1 : nat, In n1 ln2 -> n1 <= a) ->
 (exists ln3 : _, ln2 = a :: ln3) \/
 (ln1 = nil /\ a = n /\ ln2 = nil) /\ l = t :: nil.
Proof using.
intros n a ln1 ln2 t l H H0 H1;
 case
  height_pred_disj_larger_aux
   with (a := a) (ln1 := ln1) (ln2 := ln2) (1 := H); 
 auto; case ln1; simpl in |- *;
 [ intros (HH1, HH2); injection HH1; auto
 | intros n0 l1; case l1; simpl in |- *; intuition; try discriminate ].
Qed.
 
Lemma height_pred_disj_larger2_aux :
  forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
  height_pred n ln l t ->
  forall ln1 ln2 a,
  ln = ln1 ++ a :: ln2 ->
  (exists n1 : _, In n1 ln1 /\ a <= n1) \/
  (exists n1 : _, In n1 ln2 /\ a <= n1) \/ ln = n :: nil /\ l = t :: nil.
Proof using.
intros n ln t l H; elim H; clear H n ln t l.
intros n t l ln1 ln2 a; case ln1; simpl in |- *; auto.
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 ln0 ln3 a H3.
case app_inv_app with (1 := H3).
intros (ln4, H4); auto.
cut (ln3 = ln4 ++ ln2);
 [ intros E1
 | apply app_inv_head with (l1 := ln0 ++ a :: nil); repeat rewrite app_ass;
    simpl in |- *; rewrite <- H3; rewrite H4; rewrite app_ass; 
    auto ].
case H0 with (1 := H4); auto; intros [(n1, (HH1, HH2))| (HH1, HH2)]; auto;
 clear H0 H2.
right; left; exists n1; split; auto; rewrite E1; auto with datatypes.
cut (ln0 = nil /\ ln4 = nil /\ a = S n);
 [ intros (HH3, (HH4, HH5))
 | generalize HH1; rewrite H4; case ln0; simpl in |- *;
    [ case ln4; try (intros; discriminate); (intros HH6; injection HH6; auto)
    | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H1); auto.
intros n1; rewrite <- HH5; intros (HM1, HM2).
right; left; exists n1; split; auto; rewrite E1; auto with datatypes.
intros (ln4, H4); auto.
cut (ln0 = ln1 ++ ln4);
 [ intros E1
 | apply app_inv_tail with (l1 := a :: ln3); rewrite <- H3; rewrite H4;
    rewrite app_ass; auto ].
case H2 with (1 := H4); auto; clear H0 H2.
intros (n1, (HH1, HH2)); left; exists n1; split; auto; rewrite E1;
 auto with datatypes.
intros [HH1| (HH1, HH2)]; auto.
cut (ln3 = nil /\ ln4 = nil /\ a = S n);
 [ intros (HH3, (HH4, HH5))
 | generalize HH1; rewrite H4; case ln4; simpl in |- *;
    [ case ln3; try (intros; discriminate); (intros HH6; injection HH6; auto)
    | intros n0 l; case l; simpl in |- *; intros; discriminate ] ].
case height_pred_larger_ex with (1 := H); auto.
intros n1; rewrite <- HH5; intros (HM1, HM2).
left; exists n1; split; auto; rewrite E1; auto with datatypes.
Qed.

(* There is no strict maximum in a list *)
Theorem height_pred_disj_larger2 :
 forall (n a : nat) (ln1 ln2 : list nat) (t : btree A) (l : list (btree A)),
 height_pred n (ln1 ++ a :: ln2) l t ->
 (exists n1 : _, In n1 ln1 /\ a <= n1) \/
 (exists n1 : _, In n1 ln2 /\ a <= n1) \/
 (ln1 = nil /\ a = n /\ ln2 = nil) /\ l = t :: nil.
Proof using.
intros n a ln1 ln2 t l H;
 case
  height_pred_disj_larger2_aux
   with (a := a) (ln1 := ln1) (ln2 := ln2) (1 := H); 
 auto.
intros [H1| (H1, H2)]; auto.
generalize H1 H2; case ln1; simpl in |- *;
 [ intros H3; injection H3; auto with datatypes | idtac ].
intros H0 H4 H5; repeat right; auto.
intros n0 l0; case l0; simpl in |- *; intros; discriminate.
Qed.
 
Let height_pred_shrink_aux :
  forall (n : nat) (ln : list nat) (t : btree A) (l : list (btree A)),
  height_pred n ln l t ->
  forall l1 l2 ln1 ln2 a b t1 t2,
  ln = ln1 ++ a :: b :: ln2 ->
  (forall n1 : nat, In n1 ln1 -> n1 < a) ->
  (forall n1 : nat, In n1 (b :: ln2) -> n1 <= a) ->
  length ln1 = length l1 ->
  l = l1 ++ t1 :: t2 :: l2 ->
  height_pred n (ln1 ++ pred a :: ln2) (l1 ++ node t1 t2 :: l2) t.
Proof using.
intros n ln t l H; elim H; clear n ln t l H; auto.
intros n t l1 l2 ln1 ln2 a b t1 t2; case ln1;
 try (simpl in |- *; intros; discriminate).
intros n0 l0; case l0; try (simpl in |- *; intros; discriminate).
intros n ln1 ln2 t1 t2 l1 l2 H H0 H1 H2 l0 l3 ln0 ln3 a b t0 t3 H3 H4 H5 H6
 H7.
cut (length ln1 = length l1);
 [ intros Eq2 | apply height_pred_length with (1 := H) ].
cut (length ln2 = length l2);
 [ intros Eq3 | apply height_pred_length with (1 := H1) ].
cut (length ln3 = length l3);
 [ intros Eq4
 | apply plus_reg_l with (length (ln0 ++ a :: b :: nil));
    rewrite <- length_app; rewrite app_ass; simpl in |- *; 
    rewrite <- H3; repeat rewrite length_app; simpl in |- *; 
    rewrite Eq2; rewrite Eq3; rewrite <- length_app; 
    rewrite H7; repeat rewrite length_app; simpl in |- *;
    repeat rewrite (fun x y => plus_comm x (S y)); 
    simpl in |- *; rewrite plus_comm; auto ].
case app_inv_app2 with (1 := H3); auto.
intros (ln4, Hp1).
cut (ln3 = ln4 ++ ln2);
 [ intros E1
 | apply app_inv_head with (l1 := ln0 ++ a :: b :: nil);
    repeat rewrite app_ass; simpl in |- *; rewrite <- H3; 
    rewrite Hp1; repeat rewrite app_ass; auto ].
replace (ln0 ++ pred a :: ln3) with ((ln0 ++ pred a :: ln4) ++ ln2);
 [ idtac | rewrite app_ass; rewrite E1; auto ].
cut (l3 = first_n l3 (length ln4) ++ l2).
intros HH;
 replace (l0 ++ node t0 t3 :: l3) with
  ((l0 ++ node t0 t3 :: first_n l3 (length ln4)) ++ l2);
 [ idtac | pattern l3 at 2 in |- *; rewrite HH; rewrite app_ass; auto ].
apply height_pred_node; auto.
apply H0 with (1 := Hp1); auto.
intros n1 HH1; (apply H5; auto).
simpl in HH1; case HH1; intros H9; try rewrite H9; auto with datatypes.
rewrite E1; auto with datatypes.
apply app_inv_tail with (l1 := l2).
repeat rewrite app_ass; apply trans_equal with (1 := H7); auto.
pattern l3 at 1 in |- *; rewrite HH; auto.
apply sym_equal;
 apply trans_equal with (2 := first_n_skip_n_app _ (length ln4) l3).
apply f_equal2 with (f := app (A:=btree A)); auto.
apply trans_equal with (skip_n l2 (length l1 - length l1)).
rewrite <- minus_n_n; simpl in |- *; auto.
rewrite <- skip_n_app1; auto.
rewrite H7.
rewrite <- Eq2; rewrite Hp1.
rewrite skip_n_app1.
rewrite length_app.
rewrite H6; rewrite minus_plus; simpl in |- *; auto.
rewrite <- H6; rewrite length_app; simpl in |- *; auto with arith.
intros [(ln4, HH)| (HH1, HH2)].
cut (ln0 = ln1 ++ ln4);
 [ intros E1
 | apply app_inv_tail with (l1 := a :: b :: ln3); rewrite <- H3; rewrite HH;
    rewrite app_ass; auto ].
cut (l0 = l1 ++ skip_n l0 (length l1)).
intros Eq1; rewrite Eq1; rewrite E1; repeat rewrite app_ass.
apply height_pred_node; auto.
apply H2 with (b := b); auto.
intros n1 H8; apply H4; (rewrite E1; auto with datatypes).
rewrite skip_n_length; rewrite <- Eq2; rewrite <- H6;
 rewrite <- skip_n_length; rewrite E1; rewrite skip_n_app2; 
 auto; rewrite skip_n_id; simpl in |- *; auto.
apply app_inv_head with (l1 := l1).
rewrite <- app_ass; rewrite <- Eq1; auto.
apply sym_equal;
 apply trans_equal with (2 := first_n_skip_n_app _ (length l1) l0).
apply f_equal2 with (f := app (A:=btree A)); auto.
apply trans_equal with (first_n (l1 ++ l2) (length l1)).
rewrite first_n_app1; auto; rewrite <- minus_n_n; simpl in |- *;
 auto with datatypes.
rewrite H7; rewrite first_n_app2; auto.
rewrite <- H6; rewrite <- Eq2; rewrite E1; rewrite length_app;
 auto with arith.
rewrite HH1 in H; case height_pred_disj_larger2 with (1 := H); simpl in |- *;
 auto.
intros (n1, (HH3, HH4)); Contradict HH4; auto with arith.
intros [(n1, (HH3, HH4))| ((HH3, (HH4, HH5)), HH6)]; [ case HH3 | idtac ].
case height_pred_larger_strict with (1 := H1) (n1 := b); auto.
rewrite HH2; auto with datatypes.
rewrite <- HH4; intros HH7; Contradict HH7; apply le_not_lt;
 auto with arith datatypes.
intros (H8, H9); rewrite HH4; rewrite HH3; simpl in |- *.
cut (l0 = nil); [ intros HM1; rewrite HM1 | idtac ].
cut (ln3 = nil); [ intros HM2; rewrite HM2 | idtac ].
replace l3 with (nil (A:=btree A)); simpl in |- *; auto.
rewrite HH6 in H7; rewrite H9 in H7; rewrite HM1 in H7; simpl in H7;
 injection H7.
intros Ht1 Ht2 Ht3; rewrite Ht2; rewrite Ht3; auto.
generalize Eq4; rewrite HM2; case l3; simpl in |- *; auto; intros;
 discriminate.
rewrite HH2 in H8; injection H8; auto.
generalize H6; rewrite HH3; case l0; simpl in |- *; auto; intros;
 discriminate.
Qed.

(* 
  A cover can be shrunk at the first maximum of the height while
  preserving the height list
*) 
Theorem height_pred_shrink :
 forall (n a b : nat) (ln1 ln2 : list nat) (t t1 t2 : btree A)
   (l1 l2 : list (btree A)),
 height_pred n (ln1 ++ a :: b :: ln2) (l1 ++ t1 :: t2 :: l2) t ->
 (forall n1 : nat, In n1 ln1 -> n1 < a) ->
 (forall n1 : nat, In n1 (b :: ln2) -> n1 <= a) ->
 length ln1 = length l1 ->
 height_pred n (ln1 ++ pred a :: ln2) (l1 ++ node t1 t2 :: l2) t.
Proof using.
intros n a b ln1 ln2 t t1 t2 l1 l2 H H0 H1 H2;
 apply height_pred_shrink_aux with (1 := H) (b := b); 
 auto.
Qed.

(*
  Given a tree and its associated code it is possible to build
  a height list (the length of the codes) and a cover (the leaves)
  that are in relation
*)
Theorem height_pred_compute_code :
 forall (n : nat) (t : btree A),
 height_pred n (map (fun x => length (snd x) + n) (compute_code t))
   (map (fun x => leaf (fst x)) (compute_code t)) t.
Proof using.
intros n t; generalize n; elim t; clear t n; simpl in |- *; auto.
intros b H b0 H0 n.
repeat rewrite map_app.
cut
 (forall (b : bool) l,
  map (fun x : A * list bool => length (snd x) + n)
    (map (fun v : A * list bool => let (a1, b1) := v in (a1, b :: b1)) l) =
  map (fun x : A * list bool => length (snd x) + S n) l);
 [ intros E1 | idtac ].
cut
 (forall b l,
  map (fun x : A * list bool => leaf (fst x))
    (map (fun v : A * list bool => let (a1, b1) := v in (a1, b :: b1)) l) =
  map (fun x : A * list bool => leaf (fst x)) l); [ intros E2 | idtac ].
apply height_pred_node; repeat rewrite E1; repeat rewrite E2; auto.
intros b1 l; elim l; simpl in |- *; auto.
intros a; case a; simpl in |- *; auto.
intros a0 l0 l1 H1; apply f_equal2 with (f := cons (A:=btree A)); auto.
intros b1 l; elim l; simpl in |- *; auto.
intros a; case a; simpl in |- *; auto.
intros a0 l0 l1 H1; apply f_equal2 with (f := cons (A:=nat)); auto.
Qed.

(* 
  A consequence of the previous theorem, the weight of the tree
  is exactly the encoding of the message of the corresponding code
*) 
Theorem weight_tree_compute :
 forall (m : list A) t,
 distinct_leaves t ->
 (forall a : A, f a = number_of_occurrences eqA_dec a m) ->
 length (encode eqA_dec (compute_code t) m) = weight_tree f t.
Proof using.
intros m t H0 H.
rewrite frequency_length; auto.
apply trans_equal with (0 * sum_leaves f t + weight_tree f t); auto.
rewrite height_pred_weight with (1 := height_pred_compute_code 0 t).
unfold prod2list in |- *.
rewrite
 fold_left_eta
               with
               (f := 
                 fun (a : nat) (b : A * list bool) =>
                 a + number_of_occurrences eqA_dec (fst b) m * length (snd b))
              (f1 := 
                fun (a : nat) (b : A * list bool) =>
                a + (fun b => f (fst b) * length (snd b)) b); 
 auto.
rewrite <-
 (fold_left_map _ _ (fun a b : nat => a + b) _ 0 (compute_code t)
    (fun b : A * list bool => f (fst b) * length (snd b)))
 .
rewrite fold_left_eta with (f := fun a b : nat => a + b) (f1 := plus); auto.
apply f_equal3 with (f := fold_left (A:=nat) (B:=nat)); auto.
elim (compute_code t); simpl in |- *; auto.
intros a l H1; apply f_equal2 with (f := cons (A:=nat)); auto with arith.
ring.
apply btree_unique_prefix2; auto.
Qed.
 
End HeightPred.
Arguments height_pred [A].
Hint Resolve height_pred_nil height_pred_node : core.
