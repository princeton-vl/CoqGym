Require Import Coq.Classes.RelationClasses.
Require Import ExtLib.Structures.BinOps.
Require Import ExtLib.Structures.Monad.

Set Implicit Arguments.
Set Strict Implicit.

Class Reducible (T E : Type) : Type :=
  reduce : forall {A} (base : A) (single : E -> A) (join : A -> A -> A), T -> A.

Class Foldable (T E : Type) : Type :=
  fold : forall {A} (add : E -> A -> A) (base : A), T -> A.

Section RedFold.
  Variables T E : Type.

  Global Instance Reducible_from_Foldable (R : Foldable T E) : Reducible T E | 100 :=
    fun A base single join =>
      @fold _ _ R A (fun x => join (single x)) base.
End RedFold.

Section foldM.
  Context {T E : Type}.
  Context {Foldable_te : Foldable T E}.
  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.

  Definition foldM {A} (add : E -> A -> m A) (base : m A) (t : T) : m A :=
    fold (fun x acc => bind acc (add x)) base t.
End foldM.

Section reduceM.
  Context {T E : Type}.
  Context {Reducible_te : Reducible T E}.
  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.

  Definition reduceM {A} (base : m A) (single : E -> m A) (join : A -> A -> m A)  (t : T) : m A :=
    reduce base single (fun x y => bind x (fun x => bind y (fun y => join x y))) t.
End reduceM.

Section iterM.
  Context {T E : Type}.
  Context {U V : Type}.

  Context {m : Type -> Type}.
  Context {Monad_m : Monad m}.
  Context {Red_te : Reducible T E}.

  Variable f : E -> m unit.

  Definition iterM : T -> m unit :=
    reduce (ret tt) f (fun x y => bind x (fun _ => y)).
End iterM.

(*
Section Laws.
  Context (T E : Type).
  Context (R : Reducible T E).

  Class ReducibleLaw : Prop :=
    reduce_spec : forall A
      (unit : A)
      (single : E -> A)
      (join : A -> A -> A)
      (eqA : A -> A -> Prop),
      LeftUnit join unit eqA ->
      RightUnit join unit eqA ->
      Commutative join eqA ->
      Associative join eqA ->
      forall t, eqA (reduce unit single join t)
                    (fold_right (fun acc x => join acc (single x)) ?? unit)
*)