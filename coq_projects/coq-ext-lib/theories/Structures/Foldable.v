Require Import Coq.Lists.List.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monoid.

Set Implicit Arguments.
Set Strict Implicit.

Section foldable.
  Variable T A : Type.

  Class Foldable : Type :=
  { fold_mon : forall m {M : Monoid m}, (A -> m) -> T -> m }.

  Variable Foldable_T : Foldable.

  Definition fold (R : Type) (f : A -> R -> R) (init : R) (s : T) : R :=
    @fold_mon Foldable_T (R -> R)
              {| monoid_plus := fun f g x => f (g x)
               ; monoid_unit := fun x => x
               |} f s init.

  Definition toList : T -> list A :=
    fold_mon (M := {| monoid_plus := @List.app A
                    ; monoid_unit := nil |}) (fun x => x :: nil).

  Variable Add : A -> T -> T -> Prop.

  Class FoldableOk : Type :=
  { fold_ind : forall m (M : Monoid m) (t : type m) (ML : MonoidLaws M) (P : m -> Prop) f u,
                 P (monoid_unit M) ->
                 (forall x y z,
                    Add x y z ->
                    P (@fold_mon Foldable_T m M f y) ->
                    P (monoid_plus M (f x) (@fold_mon Foldable_T m M f z))) ->
                 P (@fold_mon Foldable_T m M f u)
  }.

End foldable.
