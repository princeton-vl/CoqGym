Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section list_util.
  Variables A B : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Lemma In_cons_neq :
    forall a x xs,
      In(A:=A) a (x :: xs) ->
      a <> x ->
      In a xs.
  Proof using.
    simpl.
    intuition congruence.
  Qed.

  Lemma in_fold_left_by_cons_in :
    forall (l : list B) (g : B -> A) x acc,
      In x (fold_left (fun a b => g b :: a) l acc) ->
      In x acc \/ exists y, In y l /\ x = g y.
  Proof using A_eq_dec.
    intros until l.
    induction l.
    - auto.
    - simpl; intros.
      destruct (A_eq_dec x (g a)); subst.
      + right; exists a; tauto.
      + apply IHl in H.
        case H; [left|right].
        * apply In_cons_neq in H0; tauto.
        * destruct H0; destruct H0.
          exists x0; split; auto.
  Qed.
End list_util.
