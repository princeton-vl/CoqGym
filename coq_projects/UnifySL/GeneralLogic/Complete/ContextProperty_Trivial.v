Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Lemma maximal_consistent_spec :
  forall Phi, maximal consistent Phi <-> consistent Phi /\ forall x, consistent (Union _ Phi (Singleton _ x)) -> Phi x.
Proof.
  intros.
  split; intros [? ?]; split; auto.
  + intros.
    specialize (H0 _ H1).
    specialize (H0 (fun x H => Union_introl _ _ _ _ H)).
    specialize (H0 x).
    apply H0; right; constructor.
  + intros.
    hnf; intros.
    apply H0.
    unfold consistent in*.
    destruct H1 as [y ?].
    exists y.
    intro; apply H1.
    eapply deduction_weaken; [| exact H4].
    intros ? [? | ?]; auto.
    destruct H5; auto.
Qed.

Lemma maximal_consistent_derivable_closed:
  forall (Phi: context),
  maximal consistent Phi ->
  derivable_closed Phi.
Proof.
  intros.
  hnf; intros.
  assert (consistent (Union _ Phi (Singleton _ x))).
  Focus 1. {
    destruct H as [[y ?] _].
    exists y.
    intro.
    pose proof deduction_subst1 _ _ _ H0 H1.
    auto.
  } Unfocus.
  destruct H.
  specialize (H2 _ H1).
  specialize (H2 (fun x H => Union_introl _ _ _ x H)).
  apply H2.
  right; constructor.
Qed.

Lemma MCS_element_derivable:
  forall(Phi: context),
  maximal consistent Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  apply derivable_closed_element_derivable, maximal_consistent_derivable_closed.
  auto.
Qed.

End ContextProperty.
