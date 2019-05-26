Require Import ExtLib.Core.Any.

Set Implicit Arguments.
Set Strict Implicit.

Section functor.

  Polymorphic Class CoFunctor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
  { cofmap : forall {A B : Type@{d}}, (B -> A) -> F A -> F B }.

  Polymorphic Class CoPFunctor@{d c p} (F : Type@{d} -> Type@{c}) : Type :=
  { CoFunP : Type@{d} -> Type@{p}
  ; copfmap : forall {A B : Type@{d}} {P : CoFunP B}, (B -> A) -> F A -> F B
  }.

  Existing Class CoFunP.
  Hint Extern 0 (@CoFunP _ _ _) => progress (simpl CoFunP) : typeclass_instances.

  Polymorphic Definition CoPFunctor_From_CoFunctor@{d c p} (F : Type@{d} -> Type@{c}) (F_ : CoFunctor@{d c} F) : CoPFunctor@{d c p} F :=
  {| CoFunP := Any@{p}
   ; copfmap := fun _ _ _ f x => cofmap f x
   |}.
  Global Existing Instance CoPFunctor_From_CoFunctor.
End functor.
