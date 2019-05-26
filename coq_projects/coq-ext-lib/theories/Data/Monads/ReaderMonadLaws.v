Require Import RelationClasses.
Require Import Setoid.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.Monads.ReaderMonad.
Require Import ExtLib.Tactics.TypeTac.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section Laws.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.
  Variable mtype : forall T, type T -> type (m T).
  Variable mtypeOk : forall T (tT : type T), typeOk tT -> typeOk (mtype tT).
  Variable ML_m : MonadLaws Monad_m mtype.

  Variable S : Type.
  Variable type_S : type S.
  Variable typeOk_S : typeOk type_S.

  Definition readerT_eq T (tT : type T) (a b : readerT S m T) : Prop :=
    equal (runReaderT a) (runReaderT b).

  Global Instance type_readerT (T : Type) (tT : type T) : type (readerT S m T) :=
    type_from_equal (readerT_eq tT).

  Global Instance typeOk_readerT (T : Type) (tT : type T) (tOkT : typeOk tT) 
    : typeOk  (type_readerT tT).
  Proof.
    eapply typeOk_from_equal.
    { simpl. unfold readerT_eq. intros.
      generalize (only_proper _ _ _ H); intros.
      split; do 4 red; intuition. }
    { red. unfold equal; simpl. unfold readerT_eq; simpl.
      unfold Morphisms.respectful; simpl. firstorder. }
    { red. unfold equal; simpl. unfold readerT_eq; simpl.
      unfold Morphisms.respectful; simpl. intros.
      etransitivity. eapply H; eauto.
      destruct (only_proper _ _ _ H1).
      eapply H0. eapply preflexive; eauto with typeclass_instances. }
  Qed.

  Theorem mproper_red : forall (C : Type) (tC : type C) (o : readerT S m C),
    proper o ->
    proper (runReaderT o).
  Proof. clear. intros. apply H. Qed.

  Global Instance proper_runReaderT T (tT : type T) : proper (@runReaderT S m T).
  Proof.
    repeat red; intros.
    apply H in H0. apply H0.
  Qed.

  Global Instance proper_mkReaderT T (tT : type T) : proper (@mkReaderT S m T).
  Proof.
    repeat red; intros.
    apply H in H0. apply H0.
  Qed.

  Ltac unfold_readerT :=
    red; simpl; intros; do 2 (red; simpl); intros.

  Global Instance MonadLaws_readerT : MonadLaws (@Monad_readerT S _ Monad_m) _.
  Proof.
    constructor.
    { (* bind_of_return *)
      unfold_readerT.
      erewrite bind_of_return; eauto with typeclass_instances; type_tac. }
    { (* return_of_bind *)
      unfold_readerT.
      rewrite return_of_bind; intros; eauto with typeclass_instances.
      intros. eapply H0. eassumption. }
    { (* bind_associativity *)
      unfold_readerT.
      rewrite bind_associativity; eauto with typeclass_instances; type_tac. }
    { unfold_readerT. red; intros.
      type_tac. }
    { intros. unfold bind; simpl. red; intros. red; intros. 
      red; simpl. red; simpl; intros. solve_equal. }
  Qed.

(*
  Global Instance MonadTLaws_readerT : @MonadTLaws (readerT S m) (@Monad_readerT S m _)
    r_mleq m Monad_m (@MonadT_readerT _ m).
  Proof.
    constructor; intros; simpl; eapply lower_meq; unfold liftM; simpl; monad_norm;
      reflexivity.
  Qed.
*)

End Laws.
*)