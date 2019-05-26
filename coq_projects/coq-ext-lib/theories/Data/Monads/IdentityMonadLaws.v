Require Import Coq.Classes.RelationClasses.
Require Import Setoid.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Data.Monads.IdentityMonad.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section with_T.
  Context {T : Type} (e : type T).

  Definition equal_ident (a b : ident T) : Prop :=
    equal (unIdent a) (unIdent b).

  Global Instance type_ident : type (ident T) :=
  { equal := equal_ident
  ; proper := fun x => proper (unIdent x)
  }.

  Global Instance typeOk_ident (tT : typeOk e) : typeOk type_ident.
  Proof.
    constructor.
    { unfold equal, proper, type_ident, equal_ident; simpl; intros.
      apply only_proper; auto. }
    { red. destruct x. intros.
      red; simpl. red; simpl.
      eapply preflexive with (wf := proper); eauto with typeclass_instances. }
    { red. simpl. unfold equal_ident. intros.
      symmetry. assumption. }
    { red; simpl. unfold equal_ident. intros.
      etransitivity; eassumption. }
  Qed.

  Global Instance proper_unIdent : proper unIdent.
  Proof. red; simpl; red; simpl. destruct x; compute; auto. Qed.

  Global Instance proper_mkIdent : proper mkIdent.
  Proof. do 7 red. compute; auto. Qed.

End with_T.

(*
Global Instance FunctorOrder_fmleq : FunctorOrder _ (@Identity_leq) _.
Proof.
  constructor; eauto with typeclass_instances.
Qed.
*)

Require Import ExtLib.Tactics.TypeTac.

Global Instance MonadLaws_GFix : MonadLaws Monad_ident (@type_ident).
Proof.
  constructor; eauto with typeclass_instances; try solve [ compute; intuition ].
  { unfold equal; simpl. intros. red in H2. red; simpl.
    eapply H2. eapply preflexive with (wf := proper); auto.
    eapply equiv_prefl; auto. }
  { unfold proper, equal; simpl. eauto with typeclass_instances. }
  { simpl; intros. red. solve_equal. }
  { unfold bind, Monad_ident. do 6 red; intros. solve_equal. }
Qed.
*)