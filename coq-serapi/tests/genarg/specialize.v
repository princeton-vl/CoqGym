Require Import List.
Import ListNotations.

Set Implicit Arguments.

Ltac break_match :=
  match goal with
    | [ |- context [ match ?X with _ => _ end ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Ltac do_in_app :=
  match goal with
    | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
  end.

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

  Lemma dedup_app : forall (xs ys : list A),
      (forall x y, In x xs -> In y ys -> x <> y) ->
      dedup (xs ++ ys) = dedup xs ++ dedup ys.
  Proof using.
    intros. induction xs; simpl; auto.
    repeat break_match.
    - apply IHxs.
      intros.
      apply H; intuition.
    - exfalso.
      specialize (H a a).
      apply H; intuition.
      do_in_app.
      intuition.
    - exfalso.
      apply n.
      intuition.
    - simpl.
      f_equal.
      apply IHxs.
      intros.
      apply H; intuition.
  Qed.

End dedup.