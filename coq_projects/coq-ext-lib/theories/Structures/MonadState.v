Require Import ExtLib.Structures.Monad.

Set Universe Polymorphism.
Set Printing Universes.

Class MonadState@{s d c} (T : Type@{s}) (m : Type@{d} -> Type@{c}) : Type :=
{ get : m T
; put : T -> m unit
}.

Arguments get {_ m MS} : rename.
Arguments put {_ m MS} _ : rename.

Section monadic.
  Polymorphic Universes s d c.
  Context {m : Type@{d} -> Type@{c}}.
  Context {M : Monad@{d c} m}.
  Context {T : Type@{s}}.
  Context {MS : MonadState@{s d c} T m}.

  Definition modify (f : T -> T) : m T :=
    bind get (fun x => bind (put (f x)) (fun _ => ret x)).

  Definition gets {U} (f : T -> U) : m U :=
    bind get (fun x => ret (f x)).

End monadic.

Section SubState.
  Polymorphic Universes s d c.
  Context {m : Type@{d} -> Type@{c}}.
  Context {M : Monad@{d c} m}.
  Context {T S : Type@{s}}.
  Context {MS : MonadState@{s d c} T m}.

  Definition StateProd (f : T -> S) (g : S -> T -> T)
    : MonadState S m :=
  {| get := @gets m M T MS S f
   ; put := fun x => bind get (fun s => put (g x s))
   |}.
End SubState.
