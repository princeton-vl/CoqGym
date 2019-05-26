Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Fixpoint before {A: Type} (x : A) y l : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      a = x \/
      (a <> y /\ before x y l')
  end.

Section before.
  Variable A : Type.

  Lemma before_In :
    forall x y l,
      before (A:=A) x y l ->
      In x l.
  Proof using.
    induction l; intros; simpl in *; intuition.
  Qed.

  Lemma before_split :
    forall l (x y : A),
      before x y l ->
      x <> y ->
      In x l ->
      In y l ->
      exists xs ys zs,
        l = xs ++ x :: ys ++ y :: zs.
  Proof using.
    induction l; intros; simpl in *; intuition; subst; try congruence.
    - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
    - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
    - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
    - eapply_prop_hyp In In; eauto. break_exists. subst.
      exists (a :: x0), x1, x2. auto.
  Qed.

  Lemma In_app_before :
    forall xs ys x y,
      In(A:=A) x xs ->
      (~ In y xs) ->
      before x y (xs ++ y :: ys).
  Proof using.
    induction xs; intros; simpl in *; intuition.
  Qed.

  Lemma before_2_3_insert :
    forall xs ys zs x y a b,
      before(A:=A) a b (xs ++ ys ++ zs) ->
      b <> x ->
      b <> y ->
      before a b (xs ++ x :: ys ++ y :: zs).
  Proof using.
    induction xs; intros; simpl in *; intuition.
    induction ys; intros; simpl in *; intuition.
  Qed.

  Lemma before_middle_insert :
    forall xs y zs a b,
      before(A:=A) a b (xs ++ zs) ->
      b <> y ->
      before a b (xs ++ y :: zs).
  Proof using.
    intros.
    induction xs; intros; simpl in *; intuition.
  Qed.

  Lemma before_2_3_reduce :
    forall xs ys zs x y a b,
      before(A:=A) a b (xs ++ x :: ys ++ y :: zs) ->
      a <> x ->
      a <> y ->
      before a b (xs ++ ys ++ zs).
  Proof using.
    induction xs; intros; simpl in *; intuition; try congruence; eauto.
    induction ys; intros; simpl in *; intuition; try congruence.
  Qed.

  Lemma before_middle_reduce :
    forall xs zs a b y,
      before(A:=A) a b (xs ++ y :: zs) ->
      a <> y ->
      before a b (xs ++ zs).
  Proof using.
    induction xs; intros; simpl in *; intuition; try congruence; eauto.
  Qed.

  Lemma before_remove :
    forall x y l y' dec,
      before (A := A) x y (remove dec y' l) ->
      y <> y' ->
      before x y l.
  Proof using.
    induction l; intros; simpl in *; intuition.
    break_if; subst; simpl in *; intuition eauto.
  Qed.

  Lemma before_remove_if :
    forall (x : A) y l x' dec,
      before x y l ->
      x <> x' ->
      before x y (remove dec x' l).
  Proof using.
    induction l; intros; simpl in *; intuition;
      break_if; subst; simpl in *; intuition eauto.
  Qed.

  Lemma before_app :
    forall x y l' l,
      before (A := A) x y (l' ++ l) ->
      ~ In x l' ->
      before (A := A) x y l.
  Proof using.
    induction l'; intros; simpl in *; intuition.
  Qed.

  Lemma before_app_if :
    forall x y l' l,
      before (A := A) x y l ->
      ~ In y l' ->
      before (A := A) x y (l' ++ l).
  Proof using.
    induction l'; intros; simpl in *; intuition.
  Qed.

  Lemma before_antisymmetric :
    forall x y l,
      before (A := A) x y l ->
      before y x l ->
      x = y.
  Proof using.
    intros.
    induction l; simpl in *; intuition; congruence.
  Qed.
End before.
