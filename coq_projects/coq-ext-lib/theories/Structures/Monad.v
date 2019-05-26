Require Import ExtLib.Core.Any.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Set Implicit Arguments.
Set Strict Implicit.

Polymorphic Class Monad@{d c} (m : Type@{d} -> Type@{c}) : Type :=
{ ret : forall {t : Type@{d}}, t -> m t
; bind : forall {t u : Type@{d}}, m t -> (t -> m u) -> m u
}.

Polymorphic Class PMonad@{d c p} (m : Type@{d} -> Type@{c}) : Type :=
{ MonP : Type@{d} -> Type@{p}
; pret : forall {t : Type@{d}} {Pt : MonP t}, t -> m t
; pbind : forall {t u : Type@{d}} {Pu : MonP u}, m t -> (t -> m u) -> m u
}.

Existing Class MonP.
Hint Extern 0 (@MonP _ _ _) => progress (simpl MonP) : typeclass_instances.

Global Polymorphic Instance PMonad_Monad m (M : Monad m) : PMonad m :=
{ MonP := Any
; pret := fun _ _ x => ret x
; pbind := fun _ _ _ c f => bind c f
}.

Section monadic.

  Polymorphic Definition liftM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U : Type@{d}} (f : T -> U) : m T -> m U :=
    fun x => bind x (fun x => ret (f x)).

  Polymorphic Definition liftM2@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V : Type@{d}} (f : T -> U -> V) : m T -> m U -> m V :=
    Eval cbv beta iota zeta delta [ liftM ] in
      fun x y => bind x (fun x => liftM (f x) y).

  Polymorphic Definition liftM3@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {T U V W : Type@{d}} (f : T -> U -> V -> W) : m T -> m U -> m V -> m W :=
    Eval cbv beta iota zeta delta [ liftM2 ] in
      fun x y z => bind x (fun x => liftM2 (f x) y z).

  Polymorphic Definition apM@{d c}
              {m : Type@{d} -> Type@{c}}
              {M : Monad m}
              {A B : Type@{d}} (fM:m (A -> B)) (aM:m A) : m B :=
    bind fM (fun f => liftM f aM).

  (* Left-to-right composition of Kleisli arrows. *)
  Definition mcompose@{c d}
             {m:Type@{d}->Type@{c}}
             {M: Monad m}
             {T U V:Type@{d}}
             (f: T -> m U) (g: U -> m V): (T -> m V) :=
    fun x => bind (f x) g.

End monadic.

Module MonadNotation.

  Delimit Scope monad_scope with monad.

  Notation "c >>= f" := (@pbind _ _ _ _ _ c f) (at level 50, left associativity) : monad_scope.
  Notation "f =<< c" := (@pbind _ _ _ _ _ c f) (at level 51, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 50, left associativity) : monad_scope.

  Notation "x <- c1 ;; c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
    (at level 100, c1 at next level, right associativity) : monad_scope.

  Notation "e1 ;; e2" := (_ <- e1%monad ;; e2%monad)%monad
    (at level 100, right associativity) : monad_scope.

  Notation "' pat <- c1 ;; c2" :=
    (@pbind _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level, right associativity) : monad_scope.

End MonadNotation.

Polymorphic Instance Functor_Monad {m} {M:Monad m} : Functor m :=
{ fmap := @liftM _ _ }.

Polymorphic Instance PFunctor_PMonad {m} {M : PMonad m} : PFunctor m :=
{ FunP := MonP
; pfmap := fun _ _ _ f a =>
  pbind a (fun x => pret (f x))
}.

Polymorphic Instance PApplicative_PMonad {m} {M:PMonad m} : PApplicative m :=
{ AppP := MonP
; ppure := fun _ _ x => pret x
; pap := fun _ _ _ f x =>
  pbind f (fun f => pbind x (fun x => pret (f x)))
}.

Polymorphic Instance Applicative_Monad {m} {M:Monad m} : Applicative m :=
{ pure := @ret _ _
; ap := @apM _ _
}.
