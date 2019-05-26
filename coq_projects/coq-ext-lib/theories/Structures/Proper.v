Require Coq.Setoids.Setoid.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

(*
Class Proper (T : Type) : Type :=
  proper : T -> Prop.
*)

Section relations.
  Context {T : Type} (wf : T -> Prop) (R : relation T).

  Class PReflexive : Prop :=
    preflexive : forall x : T, wf x -> R x x.

  Global Instance PReflexive_Reflexive (r : Reflexive R) : PReflexive.
  Proof. red; intros; reflexivity. Qed.

  Class PSymmetric : Prop :=
    psymmetric : forall x y, wf x -> wf y -> R x y -> R y x.

  Global Instance PSymmetric_Symmetric (r : Symmetric R) : PSymmetric.
  Proof. red; intros; symmetry; auto. Qed.

  Class PTransitive : Prop :=
    ptransitive : forall x y z, wf x -> wf y -> wf z ->
      R x y -> R y z -> R x z.

  Global Instance PTransitive_Transitive (r : Transitive R) : PTransitive.
  Proof. intro; intros; etransitivity; eauto. Qed.

End relations.

Arguments PReflexive {T} wf R.
Arguments PSymmetric {T} wf R.
Arguments PTransitive {T} wf R.
