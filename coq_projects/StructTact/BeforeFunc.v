Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Before.
Require Import StructTact.Prefix.

Set Implicit Arguments.

Fixpoint before_func {A: Type} (f : A -> bool) (g : A -> bool) (l : list A) : Prop :=
  match l with
  | [] => False
  | a :: l' =>
    f a = true \/
    (g a = false /\ before_func f g l')
  end.

Section before_func.
  Variable A : Type.
  Variables f g : A -> bool.

  Definition before_func_dec : forall l, {before_func f g l} + {~ before_func f g l}.
    intros; induction l; simpl in *.
    - intuition.
    - destruct (f a); destruct (g a); intuition.
  Defined.

  Lemma before_func_app :
    forall l x,
      before_func f g l ->
      before_func f g (l ++ x).
  Proof using.
    intros. induction l; simpl in *; intuition.
  Qed.

  Lemma before_func_antisymmetric :
    forall l, (forall x, f x = true -> g x = true -> False) ->
      before_func f g l ->
      before_func g f l ->
      False.
  Proof using. 
    induction l; simpl; intuition.
    - eauto.
    - congruence.
    - congruence.
  Qed.

  Lemma before_func_prepend :
    forall l l',
      before_func f g l ->
      (forall x, In x l' -> g x = false) ->
      before_func f g (l' ++ l).
  Proof using. 
    induction l'; intros; simpl in *; intuition.
  Qed.

  Lemma before_func_before :
    forall l,
      before_func f g l ->
      forall y,
        g y = true ->
        exists x : A,
          f x = true /\
          before x y l.
  Proof using. 
    induction l; intros; simpl in *; intuition.
    - eauto.
    - find_copy_apply_hyp_hyp. break_exists_exists. intuition.
      right. intuition. congruence.
  Qed.

  Lemma before_func_prefix :
    forall l l',
      Prefix l l' ->
      before_func f g l ->
      before_func f g l'.
  Proof using. 
    intros.
    find_apply_lem_hyp Prefix_exists_rest.
    break_exists; subst.
    eauto using before_func_app.
  Qed.

  Lemma before_func_app_necessary :
    forall l l',
      ~ before_func f g l ->
      before_func f g (l ++ l') ->
      (forall x, In x l -> g x = false) /\
      before_func f g l'.
  Proof using.
    intros. induction l; simpl in *; intuition; subst; auto.
  Qed.
End before_func.
