From QuickChick Require Import QuickChick.
Set Warnings "-extraction-opaque-accessed,-extraction".

(* TODO: better naming *)

Inductive foo {A : Type} :=
| bar : A -> foo -> foo
| baz : foo
.

Derive (Arbitrary, Show) for foo.
Sample (arbitrary : G foo).

Section Sanity.

  Inductive qux : Type :=
  | Qux: forall {A: Type}, A -> qux.

  Definition quux: qux -> bool :=
    fun a => match a with | Qux a => true end.

End Sanity.

Section Failures.

  Set Asymmetric Patterns.

  Fail Definition quux': qux -> bool :=
    fun a => match a with | Qux a => true end.

End Failures.
