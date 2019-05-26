Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Fixpoint Prefix {A} (l1 : list A) l2 : Prop :=
  match l1, l2 with
    | a :: l1', b :: l2' => a = b /\ Prefix l1' l2'
    | [], _ => True
    | _, _ => False
  end.

Section prefix.
  Variable A : Type.

  Lemma Prefix_refl :
    forall (l : list A),
      Prefix l l.
  Proof using.
    intros. induction l; simpl in *; auto.
  Qed.

  Lemma Prefix_nil :
    forall (l : list A),
      Prefix l [] ->
      l = [].
  Proof using.
    intros. destruct l.
    - reflexivity.
    - contradiction.
  Qed.

  Lemma Prefix_cons :
    forall (l l' : list A) a,
      Prefix l' l ->
      Prefix (a :: l') (a :: l).
  Proof using.
    simpl. intuition.
  Qed.

  Lemma Prefix_in :
    forall (l l' : list A),
      Prefix l' l ->
      forall x, In x l' -> In x l.
  Proof using.
    induction l; intros l' H.
    - find_apply_lem_hyp Prefix_nil. subst. contradiction.
    - destruct l'.
      + contradiction.
      + intros. simpl Prefix in *. break_and. subst. simpl in *. intuition.
        right. eapply IHl; eauto.
  Qed.

  Lemma app_Prefix :
    forall (xs ys zs : list A),
      xs ++ ys = zs ->
      Prefix xs zs.
  Proof using.
    induction xs; intros; simpl in *.
    - auto.
    - break_match.
      + discriminate.
      + subst. find_inversion. eauto.
  Qed.

  Lemma Prefix_In :
    forall (l : list A) l' x,
      Prefix l l' ->
      In x l ->
      In x l'.
  Proof using.
    induction l; intros; simpl in *; intuition;
      subst; break_match; intuition; subst; intuition.
  Qed.

  Lemma Prefix_exists_rest :
    forall (l1 l2 : list A),
      Prefix l1 l2 ->
      exists rest,
        l2 = l1 ++ rest.
  Proof using.
    induction l1; intros; simpl in *; eauto.
    break_match; intuition. subst.
    find_apply_hyp_hyp.
    break_exists_exists. subst. auto.
  Qed.
End prefix.
