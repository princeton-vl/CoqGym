Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.Monoid.

Set Universe Polymorphism.
Set Printing Universes.

Class MonadWriter@{d c s} (T : Type@{s}) (M : Monoid T)
            (m : Type@{d} -> Type@{c}) : Type :=
{ tell : T -> m unit
; listen : forall {A : Type@{d}}, m A -> m (A * T)%type
; pass : forall {A : Type@{d}}, m (A * (T -> T))%type -> m A
}.

Arguments tell {T MT m _} _ : rename.
Arguments listen {T MT m _ _} _ : rename.
Arguments pass {T MT m _} {_} _ : rename.
Arguments MonadWriter {T} MT _ : rename.


Definition listens@{d c s}
           {m : Type@{d} -> Type@{c}}
           {S : Type@{s}}
           {Monad_m : Monad m}
           {Monoid_S : Monoid S}
           {Writer_m : MonadWriter Monoid_S m}
           {A B : Type@{d}} (f : S -> B) (c : m A) : m (A * B)%type :=
  liftM (fun x => (fst x, f (snd x))) (listen c).

Definition censor@{d c s}
           {m : Type@{d} -> Type@{c}}
           {S : Type@{s}}
           {Monad_m : Monad m}
           {Monoid_S : Monoid S}
           {Writer_m : MonadWriter Monoid_S m}
           {A : Type@{d}} (f : S -> S) (c : m A) : m A :=
  pass (liftM (fun x => (x, f)) c).
