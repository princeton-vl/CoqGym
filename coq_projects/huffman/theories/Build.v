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
(*    Proof of Huffman algorithm: Build.v                              *)
(*                                                                     *)
(*    Define the build process iteratively  merging the two smaller    *)
(*    trees                                                            *)
(*                                                                     *)
(*    Definition: build build_fun                                      *)
(*                                    Laurent.Thery@inria.fr (2003)    *)
(***********************************************************************)

From Huffman Require Export OneStep.
From Huffman Require Export HeightPred.
From Huffman Require Export CoverMin.
From Huffman Require Export OrderedCover.
From Huffman Require Export SubstPred.
Require Import ArithRing.

Section Build.
Variable A : Type.
Variable f : A -> nat.

(* Iterative the one step predicate *)
Inductive build : list (btree A) -> btree A -> Prop :=
  | build_one : forall t : btree A, build (t :: nil) t
  | build_step :
      forall (t : btree A) (l1 l2 : list (btree A)),
      one_step f l1 l2 -> build l2 t -> build l1 t.
 
(* Building gives a cover *)
Theorem build_cover : forall l t, build l t -> cover l t.
Proof using.
intros l t H; elim H; clear H l t; auto.
intros t l1 l2 (l3, (t1, (t2, (HH, (HH1, HH2))))) H0 H1; try assumption.
apply cover_node with (1 := HH1); auto.
apply cover_permutation with (2 := HH2); auto.
Qed.
 
(* Building is compatible with the weight *)
Theorem build_comp :
 forall (l1 l2 : list (btree A)) (t1 t2 : btree A),
 build l1 t1 ->
 build l2 t2 ->
 weight_tree_list f l1 = weight_tree_list f l2 ->
 same_sum_leaves f l1 l2 -> weight_tree f t1 = weight_tree f t2.
Proof using.
intros l1 l2 t1 t2 H; generalize l2 t2; elim H; clear H l1 t1 l2 t2.
intros t l2 t2 H H0 (l3, (l4, (H1, (H2, H3)))).
generalize H0; inversion H; clear H0.
simpl in |- *; repeat rewrite <- plus_n_O; auto.
case H4.
intros l5 (t3, (t4, (H8, (H9, H10)))).
absurd (length l2 = length (t3 :: t4 :: l5)).
rewrite permutation_length with (1 := H2).
rewrite <- length_map with (f := sum_leaves f) (l := l4).
rewrite <- H3.
rewrite length_map with (f := sum_leaves f).
rewrite permutation_length with (1 := permutation_sym _ _ _ H1).
simpl in |- *; red in |- *; intros; discriminate.
apply permutation_length with (1 := H9).
intros t l1 l2 H H0 H1 l0 t2 H2 H3 H4.
inversion H2.
case H.
intros l5 (t3, (t4, (H8, (H9, H10)))).
case H4.
intros l6 (l7, (H11, (H12, H13))).
absurd (length l1 = length (t3 :: t4 :: l5)).
rewrite permutation_length with (1 := H11).
rewrite <- length_map with (f := sum_leaves f) (l := l6).
rewrite H13.
rewrite length_map with (f := sum_leaves f).
rewrite permutation_length with (1 := permutation_sym _ _ _ H12).
rewrite <- H5; simpl in |- *; red in |- *; intros; discriminate.
apply permutation_length with (1 := H9).
apply H1 with (1 := H6).
case one_step_comp with (3 := H) (4 := H5); auto.
case one_step_comp with (3 := H) (4 := H5); auto.
Qed.
 
(* Two built trees have same weight *)
Theorem build_same_weight_tree :
 forall (l : list (btree A)) (t1 t2 : btree A),
 build l t1 -> build l t2 -> weight_tree f t1 = weight_tree f t2.
Proof using.
intros l t1 t2 H H0; apply build_comp with (l1 := l) (l2 := l); auto.
exists l; exists l; simpl in |- *; auto.
Qed.
 
(* Building is compatible with permutation *)
Theorem build_permutation :
 forall (l1 l2 : list (btree A)) (t : btree A),
 build l1 t -> permutation l1 l2 -> build l2 t.
Proof using.
intros l1 l2 t H; generalize l2; elim H; clear H l1 l2 t; auto.
intros t l2 H; rewrite permutation_one_inv with (1 := H); auto.
apply build_one.
intros t l1 l2 H H0 H1 l0 H2.
apply build_step with (l2 := l2); auto.
case H.
intros l3 (t1, (t2, (HH1, (HH2, HH3)))).
exists l3; exists t1; exists t2; repeat (split; auto).
apply permutation_trans with (2 := HH2); auto.
apply permutation_sym; auto.
Qed.

Definition obuildf :
  forall l : list (btree A),
  l <> nil -> ordered (sum_order f) l -> {t : btree A | build l t}.
intros l; elim l using list_length_induction.
intros l1; case l1; clear l1.
intros H H0; case H0; auto.
intros b l0; case l0.
intros H H0 H1; exists b; auto.
apply build_one.
intros b0 l1 H H0 H1.
case (H (insert (le_sum f) (node b b0) l1)); auto.
rewrite <-
 permutation_length
                    with
                    (1 := insert_permutation _ (le_sum f) l1 (node b b0));
 simpl in |- *; auto.
red in |- *; intros H2;
 absurd
  (length (node b b0 :: l1) = length (insert (le_sum f) (node b b0) l1)).
rewrite H2; simpl in |- *; intros; discriminate.
apply
 permutation_length
  with (1 := insert_permutation _ (le_sum f) l1 (node b b0)); 
 simpl in |- *; auto.
apply insert_ordered; auto.
intros; apply le_sum_correct1; auto.
intros; apply le_sum_correct2; auto.
apply ordered_inv with (a := b0); auto.
apply ordered_inv with (a := b); auto.
intros t Ht; exists t.
apply build_step with (2 := Ht).
red in |- *; auto.
exists l1; exists b; exists b0; (repeat split; auto).
apply permutation_sym; apply insert_permutation.
Defined.

(* a function to buid tree from a cover list merging smaller trees *)
Definition buildf :
  forall l : list (btree A), l <> nil -> {t : btree A | build l t}.
intros l Hl; cut (isort (le_sum f) l <> nil).
intros H1; cut (ordered (sum_order f) (isort (le_sum f) l)).
intros H2; case (obuildf (isort (le_sum f) l) H1 H2).
intros t H3; exists t; auto.
apply build_permutation with (1 := H3); auto.
apply permutation_sym; apply isort_permutation; auto.
apply isort_ordered; auto.
intros; apply le_sum_correct1; auto.
intros; apply le_sum_correct2; auto.
Contradict Hl; apply permutation_nil_inv; auto.
rewrite <- Hl; auto.
apply isort_permutation; auto.
Defined.

(* Merging smaller trees gets the tree of mimimal weight for the given cover *)
Theorem build_correct :
 forall (l : list (btree A)) (t : btree A),
 l <> nil -> build l t -> cover_min _ f l t.
Proof using.
intros l; elim l using list_length_ind.
intros l0 H t H0 H1.
case (cover_min_ex _ f) with (1 := H0); auto.
intros t1 (Ht1, Ht2).
case cover_ordered_cover with (1 := Ht1); auto.
intros l1 (Hl1, Hm1).
case (ordered_cover_height_pred A 0) with (1 := Hm1).
intros ln0 Ht3.
case exist_first_max with ln0.
apply height_pred_not_nil1 with (1 := Ht3); auto.
intros a (ln1, (ln2, (HH1, (HH2, HH3)))).
cut (length ln0 = length l1);
 [ intros IL | apply height_pred_length with (1 := Ht3) ].
rewrite HH1 in Ht3; rewrite HH1 in IL; clear HH1 ln0.
case height_pred_disj_larger with (1 := Ht3); auto.
intros (ln3, HH4); rewrite HH4 in HH3; rewrite HH4 in IL; rewrite HH4 in Ht3;
 clear HH4 ln2; auto.
case same_length_ex with (1 := IL); auto.
intros l2 (l3, (t4, (HM1, (HM2, HM3)))).
generalize HM2 HM3; case l3; try (simpl in |- *; intros; discriminate);
 clear HM2 HM3 l3.
intros t5 l3 HM2 HM3; rewrite HM3 in Ht3; rewrite HM3 in IL;
 rewrite HM3 in Hm1; rewrite HM3 in Hl1; clear HM3 l1.
cut
 (exists b1 : _,
    (exists c1 : _,
       (exists l4 : _,
          permutation (l2 ++ t4 :: t5 :: l3) (b1 :: c1 :: l4) /\
          ordered (sum_order f) (b1 :: c1 :: l4)))).
intros (b1, (c1, (l4, (HC1, HC2)))).
case
 prod2list_reorder2
  with (l1 := ln1) (l2 := ln3) (5 := HC1) (6 := HC2) (a := a);
 auto with datatypes.
intros b H2; apply lt_le_weak; auto with arith.
intros l5 (l6, (HB1, (HB2, (HB3, HB4)))).
case height_pred_subst_pred with (1 := Ht3) (l2 := l5 ++ b1 :: c1 :: l6);
 auto.
rewrite <- IL; repeat rewrite length_app; simpl in |- *; auto.
intros t6 (HD1, HD2).
case (buildf (l5 ++ node b1 c1 :: l6)); auto.
case l5; simpl in |- *; intros; discriminate.
intros t7 HD3.
case H with (3 := HD3); auto with arith.
rewrite permutation_length with (1 := Hl1).
rewrite permutation_length with (1 := HC1).
rewrite permutation_length with (1 := HB3).
repeat rewrite length_app; simpl in |- *; auto with arith.
case l5; simpl in |- *; intros; discriminate.
intros HD4 HD5.
split; auto.
apply build_cover with (1 := H1).
intros t0 H2; apply le_trans with (weight_tree f t1); auto.
rewrite (build_same_weight_tree l0 t t7); auto.
apply le_trans with (weight_tree f t6).
apply HD5; auto.
apply ordered_cover_cover.
apply (height_pred_ordered_cover A 0 (ln1 ++ pred a :: ln3)); auto.
apply height_pred_shrink with (b := a); auto.
replace (weight_tree f t1) with (0 * sum_leaves f t1 + weight_tree f t1);
 [ idtac | simpl in |- *; auto ].
rewrite height_pred_weight with (1 := Ht3).
replace (weight_tree f t6) with (0 * sum_leaves f t6 + weight_tree f t6);
 [ idtac | simpl in |- *; auto ].
rewrite height_pred_weight with (1 := HD1); auto.
apply build_step with (2 := HD3); auto.
exists l4; exists b1; exists c1; repeat (split; auto).
apply permutation_trans with (1 := Hl1).
apply permutation_sym; apply permutation_trans with (1 := HB3).
apply permutation_sym; apply permutation_trans with (1 := HC1); auto.
apply permutation_trans with ((node b1 c1 :: l6) ++ l5); auto.
simpl in |- *; apply permutation_skip.
apply permutation_inv with c1.
apply permutation_inv with b1.
apply permutation_sym; apply permutation_trans with (1 := HB3).
apply (permutation_app_swap _ l5 (b1 :: c1 :: l6)).
generalize (isort_permutation _ (le_sum f) (l2 ++ t4 :: t5 :: l3));
 generalize
  (isort_ordered _ (sum_order f) (le_sum f) (le_sum_correct1 _ f)
     (le_sum_correct2 _ f) (l2 ++ t4 :: t5 :: l3)).
case (isort (le_sum f) (l2 ++ t4 :: t5 :: l3)); auto.
intros H2 H3.
absurd (l2 ++ t4 :: t5 :: l3 = nil); auto.
case l2; simpl in |- *; intros; discriminate.
apply permutation_nil_inv with (1 := H3).
intros b l4; case l4.
intros H2 H3; absurd (l2 ++ t4 :: t5 :: l3 = b :: nil).
case l2; simpl in |- *; try (intros; discriminate).
intros b0 l5; case l5; try (intros; discriminate).
apply permutation_one_inv with (1 := permutation_sym _ _ _ H3).
intros b0 l5 H2 H3; exists b; exists b0; exists l5; auto.
intros ((H2, (H3, H4)), H5); split.
apply build_cover with (1 := H1).
intros t2 H6; rewrite <- cover_one_inv with (t1 := t1) (t2 := t2).
rewrite <- cover_one_inv with (t1 := t1) (t2 := t); auto.
rewrite <- H5; apply cover_permutation with (2 := Hl1); auto.
apply build_cover with (1 := H1).
rewrite <- H5; apply cover_permutation with (2 := Hl1); auto.
Qed.
 
(* Final function that tree of minimal weight for the cover *)
Definition build_fun :
  forall l : list (btree A), l <> nil -> {t : btree A | cover_min _ f l t}.
intros l Hl; case (buildf l Hl).
intros x b; exists x.
apply build_correct; auto.
Defined.
 
End Build.
Arguments build [A].
