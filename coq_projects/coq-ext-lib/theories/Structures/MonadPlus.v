Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.

Class MonadPlus (m : Type -> Type) : Type :=
{ mplus : forall {A B:Type}, m A -> m B -> m (A + B)%type }.

Definition mjoin {m : Type -> Type} {M : Monad m} {MP : MonadPlus m} {T} (a b : m T) : m T :=
  bind (mplus a b) (fun x =>
    match x with
      | inl x | inr x => ret x
    end).

Module MonadPlusNotation.
  Notation "x <+> y" := (@mplus _ _ _ _ x y) (at level 49, right associativity) : monad_scope.
End MonadPlusNotation.
