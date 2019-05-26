Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Tactics.TypeTac.

Set Implicit Arguments.
Set Strict Implicit.

(*
Section monad.
  Context {m : Type -> Type}.
  Variable meq : forall T {tT : type T}, type (m T).
  Variable meqOk : forall T (tT : type T), typeOk tT -> typeOk (meq tT).
  Context {M : Monad m} (ML : MonadLaws M meq).

  Theorem bind_rw_0 : forall A B (tA : type A) (tB : type B),
    typeOk tA -> typeOk tB ->
    forall (x z : m A) (y : A -> m B),
      equal x z ->
      proper y ->
      equal (bind x y) (bind z y).
  Proof.
    intros. eapply bind_proper; eauto.
  Qed.

  Theorem bind_rw_1 : forall A B (tA : type A) (tB : type B),
    typeOk tA -> typeOk tB ->
    forall (x z : A -> m B) (y : m A),
      (forall a b, equal a b -> equal (x a) (z b)) ->
      proper y ->
      equal (bind y x) (bind y z).
  Proof.
    intros. eapply bind_proper; eauto. solve_equal.
  Qed.
End monad.
*)