Require Import Coq.Bool.Bool.
Require Import ExtLib.Structures.Sets.
Require Import ExtLib.Structures.Reducible.
Require Import ExtLib.Structures.Functor.

Set Implicit Arguments.
Set Strict Implicit.

(** Program with respect to the set interface **)
Section with_set.
  Variable V : Type.
  Context {set : Type}.
  Context {Set_set : DSet set V}.

  Definition contains_both (v1 v2 : V) (s : set) : bool :=
    contains v1 s && contains v2 s.

  (** Iteration requires foldability **)
  Context {Foldable_set : Foldable set V}.

  Definition toList (s : set) : list V :=
    fold (@cons _) nil s.

End with_set.

(** Instantiate the set **)
Require Import ExtLib.Data.Set.ListSet.
Require Import ExtLib.ExtLib.

Eval compute in contains_both 0 1 empty.

Eval compute in toList (add true (add true empty)).

Eval compute in fmap negb (add true empty).