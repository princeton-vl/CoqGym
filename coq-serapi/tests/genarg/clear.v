Require Import List.
Import ListNotations.
Require Import Sumbool.

Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.

Ltac find_injection :=
  match goal with
    | [ H : ?X _ _ = ?X _ _ |- _ ] => injection H; intros; subst
  end.

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

  Lemma collate_f_eq :
    forall (f : A -> A -> list B) g h n n' l,
      f n n' = g n n' ->
      collate A_eq_dec h f l n n' = collate A_eq_dec h g l n n'.
  Proof using.
    intros f g h n n' l.
    generalize f g; clear f g.
    induction l; auto.
    intros.
    simpl in *.
    break_let.
    destruct a.
    find_injection.
    set (f' := update2 _ _ _ _ _).
    set (g' := update2 _ _ _ _ _).
    rewrite (IHl f' g'); auto.
    unfold f', g', update2.
    break_if; auto.
    break_and.
    subst.
    rewrite H.
    trivial.
  Qed.
End Update2.