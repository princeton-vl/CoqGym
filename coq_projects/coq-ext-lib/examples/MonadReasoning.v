Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Structures.MonadLaws.
Require Import ExtLib.Data.PreFun.
Require Import ExtLib.Data.Fun.

Set Implicit Arguments.
Set Strict Implicit.

(** Currently not ported due to universes *)

(*
Section with_m.
  Variable m : Type -> Type.
  Variable Monad_m : Monad m.

  Variable meq : forall {T}, type T -> type (m T).
  Variable meqOk : forall {T} (tT : type T), typeOk tT -> typeOk (meq tT).

  Variable MonadLaws_m : @MonadLaws m Monad_m meq.

  Variable T : Type.
  Variable type_T : type T.
  Variable typeOk_T : typeOk type_T.

  Lemma proper_eta
  : forall T U (f : T -> U)
           (type_T : type T)
           (type_U : type U),
      proper f ->
      proper (fun x => f x).
  Proof.
    intros; do 3 red; intros.
    eapply H. assumption.
    Qed.

  Goal forall x : T, proper x ->
    equal (bind (ret x) (fun x => ret x)) (ret x).
  Proof.
    intros.
    etransitivity.
    { eapply bind_of_return; eauto.
      eapply proper_eta. eapply ret_proper; eauto. }
    { eapply ret_proper; eauto.
      eapply equiv_prefl; eauto. }
  Qed.

  Goal forall x : T, proper x ->
    equal (bind (ret x) (fun x => ret x)) (ret x).
  Proof.
    intros.
    etransitivity.
    { eapply bind_of_return; eauto.
      eapply proper_eta. eapply ret_proper; eauto. }
    { eapply ret_proper; eauto.
      eapply equiv_prefl; eauto. }
  Qed.

End with_m.
*)