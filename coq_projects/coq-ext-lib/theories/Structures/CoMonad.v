Set Implicit Arguments.
Set Strict Implicit.

Class CoMonad (m : Type -> Type) : Type :=
{ coret : forall {A}, m A -> A
; cobind : forall {A B}, m A -> (m A -> B) -> m B
}.
