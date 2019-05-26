Require Import List.
Import ListNotations.
Require Import Sumbool.

Ltac break_and :=
  repeat match goal with
           | [H : _ /\ _ |- _ ] => destruct H
         end.

Ltac break_if :=
  match goal with
    | [ |- context [ if ?X then _ else _ ] ] =>
      match type of X with
        | sumbool _ _ => destruct X
        | _ => destruct X eqn:?
      end
  end.

Definition update2 {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (f : A -> A -> B) (x y : A) (v : B) :=
  fun x' y' => if sumbool_and _ _ _ _ (A_eq_dec x x') (A_eq_dec y y') then v else f x' y'.

Fixpoint collate {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (from : A) (f : A -> A -> list B) (ms : list (A * B)) :=
  match ms with
   | [] => f
   | (to, m) :: ms' => collate A_eq_dec from (update2 A_eq_dec f from to (f from to ++ [m])) ms'
  end.

Section Update2.
  Variables A B : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}. 

  Lemma collate_neq :
    forall h n n' ns (f : A -> A -> list B),
      h <> n ->
      collate A_eq_dec h f ns n n' = f n n'.
  Proof using.
    intros.
    revert f.
    induction ns; intros; auto.
    destruct a.
    simpl in *.
    rewrite IHns.
    unfold update2.
    break_if; auto.
    break_and; subst.
    intuition.
  Qed.
End Update2.