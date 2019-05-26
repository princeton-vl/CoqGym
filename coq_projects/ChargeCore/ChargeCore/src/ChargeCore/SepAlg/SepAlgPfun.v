Require Import Setoid Morphisms Coq.Strings.String Coq.Lists.List.
From ChargeCore.SepAlg Require Import SepAlg UUSepAlg.

Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Unset Strict Implicit.
Set Maximal Implicit Insertion.

Section PartialFun.

  (* A partial function is a function from X -> option Y where X equality of members
     of type X is decidable. *)

  Context {X Y : Type}.
  Context {RelDec_X : RelDec (@eq X)}.
  Context {RDC : RelDec_Correct RelDec_X}.

  Definition pfun := X -> option Y.

  Definition pfun_eq (f1 f2 : pfun) := forall s, (f1 s) = (f2 s).

  Global Instance EquivalencePfun : Equivalence pfun_eq.
  Proof.
    split; intuition congruence.
  Qed.

  Definition emptyFun : pfun := fun _ => None.

  Definition pfun_update (f : pfun) (x : X) (y : Y) :=
    fun z => if x ?[ eq ] z then Some y else f z.

  Definition pfun_in (f : pfun) (x : X) : Prop := exists y, f x = Some y.

  Lemma update_shadow (f : pfun) (x : X) (y1 y2 : Y) :
    pfun_eq (pfun_update (pfun_update f x y1) x y2) (pfun_update f x y2).
  Proof.
      unfold pfun_update; intro z.
      consider (x ?[ eq ] z); intro; reflexivity.
  Qed.

  Lemma update_lookup (f : pfun) (x : X) (y : Y) :
    (pfun_update f x y) x = Some y.
  Proof.
    unfold pfun_update.
    consider (x ?[ eq ] x); intros; [reflexivity|].
    contradiction H. reflexivity.
  Qed.

  Lemma update_lookup_neq (f : pfun) (x z : X) (y : Y) (H: x <> z) :
    (pfun_update f x y) z = f z.
  Proof.
    unfold pfun_update.
    consider (x ?[ eq ] z); intros; [|reflexivity].
    contradiction H.
  Qed.

  Lemma update_commute (f : X -> option Y) (x1 x2 : X) (y1 y2 : Y) (H : x1 <> x2) :
    pfun_eq (pfun_update (pfun_update f x1 y1) x2 y2) (pfun_update (pfun_update f x2 y2) x1 y1).
  Proof.
    unfold pfun_update; intro z.
    consider (x2 ?[ eq ] z); consider (x1 ?[ eq ] z); try reflexivity; intros; subst; firstorder.
  Qed.

  Ltac SepOpSolve :=
    match goal with
      | H : (match ?f ?x with | Some _ => _ | None => _ end) |- _ =>
        let e := fresh "e" in let y := fresh "y" in remember (f x) as e;
            destruct e as [y |]; SepOpSolve
      | H : _ \/ _ |- _ => destruct H as [H | H]; SepOpSolve
      | H : _ /\ _ |- _ => let H1 := fresh "H" in destruct H as [H H1]; SepOpSolve
      | H : ?f ?x = _ |- context [match ?f ?x with | Some _ => _ | None => _ end] =>
        rewrite H; SepOpSolve
      | H : forall x : X, _ |- _ =>
                   match goal with
                       | x : X |- _ => specialize (H x)
                   end; SepOpSolve
      | _ => subst; try intuition congruence
    end.

  (* We can create a separation algebra for partial functions with the following
     definitions for sa_unit and sa_mul *)

  Global Instance PFunSepAlgOps : SepAlgOps (X -> option Y) := {
     sa_unit f := pfun_eq f emptyFun;
     sa_mul    := fun a b c => forall x,
                    match c x with
                      | Some y => (a x = Some y /\ b x = None) \/
                                     (b x = Some y /\ a x = None)
                      | None => a x = None /\ b x = None
                    end

  }.

  (* Proving that partial functions actually form a separation algebra is straightforward
     modulo some LTac magic. *)

  Global Instance PFunSepAlg : SepAlg (rel := pfun_eq) (X -> option Y).
  Proof.
    esplit; simpl.
    + eapply Equivalence.pointwise_equivalence; eauto with typeclass_instances.
    + intros * H x. SepOpSolve.
    + intros * H1 H2.
      exists (fun x =>
                match b x with
                | Some y => Some y
             | Undefined => c x
              end).
      split; intro x; SepOpSolve.
    + intros; exists emptyFun. split; [reflexivity | intros x].
      remember (a x) as p; destruct p; simpl; intuition.
    + intros * H H1. unfold equiv, pfun_eq, emptyFun in H. simpl in H.
      intros k. SepOpSolve.
    + intros a b Hab; split; intros H1 x; unfold emptyFun in *; specialize (H1 x); simpl in H1;
      SepOpSolve.
    + intros * Hab H1 x; SepOpSolve.
 Defined.

  Definition UUPFunSepAlg : @UUSepAlg (X -> option Y) pfun_eq _.
  Proof.
    split.
    + apply _.
    + intros m u Hu x. simpl in Hu. remember (m x) as e. destruct e.
      * left; split; [intuition|]. specialize (Hu x); intuition.
      * split; [intuition|]. specialize (Hu x). intuition.
  Qed.

  Lemma pfun_in_sa_mulR (a b c : X -> option Y) (x : X) (H : sa_mul a b c) (Hin : pfun_in c x) : pfun_in a x \/ pfun_in b x.
  Proof.
    destruct Hin as [d Hin]; unfold sa_mul in H; simpl in H.
    specialize (H x); rewrite Hin in H.
    unfold pfun_in.
    destruct H as [[H1 H2] | [H1 H2]]; subst.
    + left; exists d; assumption.
    + right; exists d; assumption.
  Qed.

  Lemma pfun_mapsto_sa_mulR (a b c : X -> option Y) (x : X) (y : Y) (H : sa_mul a b c) (Hmap : c x = Some y) : a x = Some y \/ b x = Some y.
  Proof.
    specialize (H x); simpl in H; rewrite Hmap in H.
    unfold pfun_in.
    destruct H as [[H1 H2] | [H1 H2]]; subst.
    + left; assumption.
    + right; assumption.
  Qed.

End PartialFun.