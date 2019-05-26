Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.CoMonad.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Definition Lazy (t : Type) : Type := unit -> t.

(** Note: in order for this to have the right behavior, it must
 ** be beta-delta reduced.
 **)
Definition _lazy {T : Type} (l : T) : Lazy T := fun _ => l.

Definition force {T : Type} (l : Lazy T) : T := l tt.

Global Instance CoMonad_Lazy : CoMonad Lazy :=
{ coret := @force
; cobind _A _B a b := fun x : unit => b a
}.

Global Instance Functor_Lazy : Functor Lazy :=
{ fmap _A _B f l := fun x => f (l x) }.

Global Instance Monad_Lazy : Monad Lazy :=
{ ret := @_lazy
; bind _A _B a b := fun x => b (a x) x
}.

Notation "'lazy' x" := (fun _ : unit => x) (x at next level, at level 50).
