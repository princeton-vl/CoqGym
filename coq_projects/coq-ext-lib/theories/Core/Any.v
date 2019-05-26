Set Implicit Arguments.
Set Strict Implicit.

(** This class should be used when no requirements are needed **)
Polymorphic Class Any (T : Type) : Type.

Global Polymorphic Instance Any_a (T : Type) : Any T := {}.

Polymorphic Definition RESOLVE (T : Type) : Type := T.

Existing Class RESOLVE.

Hint Extern 0 (RESOLVE _) => unfold RESOLVE : typeclass_instances.
