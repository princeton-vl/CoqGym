Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section list_util.
  Variables A : Type.

  Lemma in_firstn : forall n (x : A) xs,
      In x (firstn n xs) -> In x xs.
  Proof using.
    induction n; simpl; intuition.
    destruct xs;simpl in *; intuition.
  Qed.

  Lemma firstn_NoDup : forall n (xs : list A),
    NoDup xs ->
    NoDup (firstn n xs).
  Proof using.
    induction n; intros; simpl; destruct xs; auto.
    - apply NoDup_nil.
    - inversion H; subst.
      apply NoDup_cons.
      * eauto 6 using in_firstn.
      * apply IHn; auto.        
  Qed.
End list_util.
