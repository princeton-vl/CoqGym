Require Import ExtLib.Structures.Monad.

Class MonadExc (E : Type) (m : Type -> Type) : Type :=
{ raise : forall {T}, E -> m T
; catch : forall {T}, m T -> (E -> m T) -> m T
}.

Arguments raise {E m mE} {_} _ : rename.
Arguments catch {E m mE} {_} _ _ : rename.