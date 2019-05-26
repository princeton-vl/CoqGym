Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class Functor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
{ fmap : forall {A B : Type@{d}}, (A -> B) -> F A -> F B }.

Polymorphic Definition ID@{d} {T : Type@{d}} (f : T -> T) : Prop :=
  forall x : T, f x = x.

Polymorphic Class PFunctor@{d c p} (F : Type@{d} -> Type@{c}) : Type :=
{ FunP : Type@{d} -> Type@{p}
; pfmap : forall {A B : Type@{d}} {P : FunP B}, (A -> B) -> F A -> F B
}.

Existing Class FunP.
Hint Extern 0 (@FunP _ _ _) => progress (simpl FunP) : typeclass_instances.

(** TODO: This is due to a but in current 8.5 **)
Polymorphic Definition PFunctor_From_Functor@{d c p}
       (F : Type@{d} -> Type@{c}) (FunF : Functor@{d c} F) : PFunctor@{d c p} F :=
{| FunP := Any
; pfmap := fun _ _ _ f x => fmap f x
|}.
Global Existing Instance PFunctor_From_Functor.

Module FunctorNotation.
  Notation "f <$> x" := (@pfmap _ _ _ _ _ f x) (at level 51, right associativity).
End FunctorNotation.
