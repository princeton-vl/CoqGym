
Require vec.
Require Import monads.
Require qs_definitions.
Require Import util.
Require Import List.
Require Import list_utils.

Section contents.

  Import qs_definitions.nonmonadic.

  Variable X: Set.
  Variable Xle: X -> X -> Prop.
  Variable XleDec: forall x y, { Xle x y } + { Xle y x }.
  Let leb: X -> X -> IdMonad.M bool := fun x y => unsum_bool (XleDec x y).

  Lemma qs_permutes: forall l, Permutation.Permutation l (qs leb l).
  Proof with auto.
    intro. pattern l, (qs leb l).
    apply qs_rect...
    intros.
    simpl.
    apply Permutation.Permutation_cons_app.
    apply Permutation.perm_trans with (filter (leb h) t ++ filter (gt leb h) t).
      apply complementary_filter_perm.
    apply Permutation.perm_trans with (qs leb (filter (leb h) t) ++ qs leb (filter (gt leb h) t)).
      apply Permutation.Permutation_app...
    apply Permutation.Permutation_app_swap.
  Qed.

  Variable PO: Relation_Definitions.preorder X Xle.

  Lemma  qs_correct: forall l, vec.sorted Xle (qs leb l).
  Proof with auto.
    intro.
    pattern l, (qs leb l).
    apply qs_rect.
      apply vec.sorted_nil.
    intros.
    simpl.
    cset (Permutation.Permutation_sym (qs_permutes (filter (leb h) t))).
    cset (Permutation.Permutation_sym (qs_permutes (filter (gt leb h) t))).
    apply vec.sorted_app...
      simpl.
      apply vec.sorted_cons'...
      rewrite vec.list_round_trip.
      intros.
      cset (Permutation.Permutation_in y H1 H3).
      destruct (filter_In (leb h) y t).
      destruct (H5 H4).
      unfold leb in H8.
      destruct (XleDec h y) in H8...
      discriminate.
    intros.
    cset (Permutation.Permutation_in _ H2 H3).
    destruct (filter_In (gt leb h) x t).
    destruct (H6 H5).
    unfold gt, leb in H9.
    destruct (XleDec h x) in H9.
      discriminate.
    destruct H4.
      subst...
    apply (Relation_Definitions.preord_trans _ _ PO x h y)...
    cset (Permutation.Permutation_in _ H1 H4).
    destruct (filter_In (leb h) y t).
    destruct (H11 H10).
    unfold leb in H14. destruct (XleDec h y)...
    discriminate.
  Qed.

End contents.
