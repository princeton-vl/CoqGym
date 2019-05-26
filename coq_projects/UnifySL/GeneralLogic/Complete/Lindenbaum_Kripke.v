Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.

Section Lindenbaum.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Lemma Lindenbaum_for_derivable_closed: forall P,
  Lindenbaum_preserves P ->
  derivable_subset_preserved P ->
  Lindenbaum_ensures P derivable_closed.
Proof.
  intros; hnf; intros; hnf; intros.
  pose proof H CA _ H1.
  destruct (im_inj _ _ CA x) as [n ?].
  rewrite <- Lindenbaum_pointwise_finite_decided by eauto.
  simpl; right; split; auto.
  eapply H0; [| exact H3].
  unfold Included, Ensembles.In; intros.
  eapply deduction_subst; eauto.
  eapply deduction_weaken; eauto.
  rewrite Union_Included; split.
  + eapply Included_trans; [| apply left_Included_Union].
    apply Lindenbaum_included_n_omega.
  + eapply Included_trans; [| apply right_Included_Union].
    intros ? ?.
    inversion H6; subst; auto.
Qed.

End Lindenbaum.
