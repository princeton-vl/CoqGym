Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.

Class MonadZero (m : Type -> Type) : Type :=
{ mzero : forall {T}, m T }.

Section ZeroFuncs.
  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.
  Context {Zero_m : MonadZero m}.

  Definition assert (b : bool) : m unit :=
    if b then ret tt else mzero.

End ZeroFuncs.