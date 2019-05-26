Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
Require Import StructTact.ListUtil.

Set Implicit Arguments.

Section dedup.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Fixpoint dedup (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => let tail := dedup xs in
                 if in_dec A_eq_dec x xs then
                   tail
                 else
                   x :: tail
    end.

  Lemma dedup_eliminates_duplicates : forall a l l',
      dedup (a :: l ++ a :: l') = dedup (l ++ a :: l').
  Proof using.
    intros. simpl in *.
    break_match.
    + auto.
    + exfalso. intuition.
  Qed.

  Lemma dedup_In : forall (x : A) xs,
      In x xs ->
      In x (dedup xs).
  Proof using.
    induction xs; intros; simpl in *.
    - intuition.
    - break_if; intuition; subst; simpl; auto.
  Qed.

  Lemma filter_dedup (pred : A -> bool) :
    forall xs (p : A) ys,
      pred p = false ->
      filter pred (dedup (xs ++ ys)) = filter pred (dedup (xs ++ p :: ys)).
  Proof using.
    intros.
    induction xs; simpl; repeat (break_match; simpl);
      auto using f_equal2; try discriminate.
      + exfalso. apply n. apply in_app_iff. apply in_app_or in i. intuition.
      + exfalso. apply n. apply in_app_or in i. intuition.
        * simpl in *. intuition. congruence.
  Qed.

  Lemma dedup_app : forall (xs ys : list A),
      (forall x y, In x xs -> In y ys -> x <> y) ->
      dedup (xs ++ ys) = dedup xs ++ dedup ys.
  Proof using.
    intros. induction xs; simpl; auto.
    repeat break_match.
    - apply IHxs.
      intros. apply H; intuition.
    - exfalso. specialize (H a a).
      apply H; intuition.
      do_in_app. intuition.
    - exfalso. apply n. intuition.
    - simpl. f_equal.
      apply IHxs.
      intros. apply H; intuition.
  Qed.

  Lemma in_dedup_was_in :
    forall xs (x : A),
      In x (dedup xs) ->
      In x xs.
  Proof using.
    induction xs; intros; simpl in *.
    - intuition.
    - break_if; simpl in *; intuition.
  Qed.

  Lemma NoDup_dedup :
    forall (xs : list A),
      NoDup (dedup xs).
  Proof using.
    induction xs; simpl.
    - constructor.
    - break_if; auto.
      constructor; auto.
      intro.
      apply n.
      eapply in_dedup_was_in; eauto.
  Qed.

  Lemma remove_dedup_comm : forall (x : A) xs,
      remove A_eq_dec x (dedup xs) =
      dedup (remove A_eq_dec x xs).
  Proof using.
    induction xs; intros.
    - auto.
    - simpl. repeat (break_match; simpl); auto using f_equal.
      + exfalso. apply n0. apply remove_preserve; auto.
      + exfalso. apply n. eapply in_remove; eauto.
  Qed.

  Lemma dedup_partition :
    forall xs (p : A) ys xs' ys',
      dedup (xs ++ p :: ys) = xs' ++ p :: ys' ->
      remove A_eq_dec p (dedup (xs ++ ys)) = xs' ++ ys'.
  Proof using.
    intros xs p ys xs' ys' H.
    f_apply H (remove A_eq_dec p).
    rewrite remove_dedup_comm, remove_partition in *.
    find_rewrite.
    rewrite remove_partition.

    apply remove_not_in.
    apply NoDup_remove_2.
    rewrite <- H.
    apply NoDup_dedup.
  Qed.

  Lemma dedup_NoDup_id : forall (xs : list A),
      NoDup xs -> dedup xs = xs.
  Proof using.
    induction xs; intros.
    - auto.
    - simpl. invc_NoDup. concludes.
      break_if; congruence.
  Qed.

  Lemma dedup_not_in_cons :
    forall x xs,
      (~ In x xs) ->
      x :: dedup xs = dedup (x :: xs).
  Proof using.
    induction xs; intros.
    - auto.
    - simpl in *. intuition. repeat break_match; intuition.
  Qed.
End dedup.
