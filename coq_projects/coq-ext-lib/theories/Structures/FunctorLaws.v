Require Import Coq.Relations.Relations.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Identity.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

Section laws.

  Polymorphic Class FunctorLaws@{t u X}
              (F : Type@{t} -> Type@{u})
              (Functor_F : Functor F)
              (Feq : type1@{t u X} F)
  : Type :=
  { fmap_id : forall (T : Type@{t}) (tT : type@{t} T)
      (tTo : typeOk@{t} tT) (f : T -> T),
        IsIdent f ->
        equal (fmap f) (@id (F T))
  ; fmap_compose : forall (T U V : Type@{t})
                          (tT : type@{t} T) (tU : type@{t} U) (tV : type@{t} V),
      typeOk tT -> typeOk tU -> typeOk tV ->
      forall (f : T -> U) (g : U -> V),
        proper f -> proper g ->
        equal (fmap (compose g f)) (compose (fmap g) (fmap f))
  ; fmap_proper :> forall (T : Type@{t}) (U : Type@{u}) (tT : type T) (tU : type U),
      typeOk@{t} tT -> typeOk@{u} tU ->
      proper (@fmap _ _ T U)
  }.
End laws.
