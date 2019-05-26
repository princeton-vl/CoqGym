Require Import List.
Import ListNotations.

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
    - exists []. simpl.
      apply in_split in H1.
      destruct H1; destruct H1.
      subst. eauto.
    - exists []. simpl.
      apply in_split in H1.
      destruct H1; destruct H1. subst. eauto.      
    - exists []. simpl.
      apply in_split in H1.
      destruct H1; destruct H1. subst. eauto.      
    - match goal with
      | [ H : context [ In ], H' : context [ In ] |- _ ] =>
      eapply H in H'
      end; eauto.
      destruct H1; destruct H1; destruct H1. subst.
      exists (a :: x0), x1, x2. auto.
  Qed.
End before.