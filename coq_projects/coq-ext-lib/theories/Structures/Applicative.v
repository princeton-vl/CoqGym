Set Implicit Arguments.
Set Maximal Implicit Insertion.

Polymorphic Class PApplicative@{d c p} (T : Type@{d} -> Type@{c}) :=
{ AppP : Type@{d} -> Type@{p}
; ppure : forall {A : Type@{d}} {P : AppP A}, A -> T A
; pap : forall {A B : Type@{d}} {P : AppP B}, T (A -> B) -> T A -> T B
}.

Polymorphic Class Applicative@{d c} (T : Type@{d} -> Type@{c}) :=
{ pure : forall {A : Type@{d}}, A -> T A
; ap : forall {A B : Type@{d}}, T (A -> B) -> T A -> T B
}.

Module ApplicativeNotation.
  Notation "f <*> x" := (ap f x) (at level 51, right associativity).
End ApplicativeNotation.
Import ApplicativeNotation.

Section applicative.
  Polymorphic Definition liftA@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B : Type@{d}} (f:A -> B) (aT:T A) : T B := pure f <*> aT.
  Polymorphic Definition liftA2@{d c} {T : Type@{d} -> Type@{c}} {AT:Applicative@{d c} T} {A B C : Type@{d}} (f:A -> B -> C) (aT:T A) (bT:T B) : T C := liftA f aT <*> bT.
End applicative.
