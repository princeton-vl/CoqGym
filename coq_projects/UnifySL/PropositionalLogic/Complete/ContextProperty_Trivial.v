Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Trivial.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section ContextProperties.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {cpSC: ClassicalPropositionalSequentCalculus L Gamma}.

Lemma classical_derivable_spec: forall (Phi: context) (x: expr),
  Phi |-- x <-> ~ consistent (Union _ Phi (Singleton _ (~~ x))).
Proof.
  intros.
  unfold consistent.
  AddAxiomatization Gamma.
  fold (@consistent L Gamma (Phi;; ~~ x)).
  rewrite <- (double_negp x) at 1.
  unfold negp at 1.
  rewrite <- deduction_theorem.
  rewrite consistent_spec.
  tauto.
Qed.

Lemma MCS_nonelement_inconsistent: forall (Phi: context),
  maximal consistent Phi ->
  (forall x: expr, ~ Phi x <-> Phi |-- x --> FF).
Proof.
  intros.
  split; intros.
  + destruct H.
    specialize (H1 (Union _ Phi (Singleton _ x))).
    rewrite consistent_spec in H1.
    rewrite deduction_theorem in H1.
    assert (Included expr Phi (Union expr Phi (Singleton expr x))) by (intros ? ?; left; auto).
    assert (~ Included expr (Union expr Phi (Singleton expr x)) Phi) by (intros HH; specialize (HH x); apply H0, HH; right; constructor).
    tauto.
  + intro.
    pose proof derivable_assum Phi x H1.
    pose proof deduction_modus_ponens _ _ _ H2 H0.
    destruct H as [? _].
    rewrite consistent_spec in H; auto.
Qed.

Lemma maximal_consistent_orp_witnessed: forall (Phi: context),
  maximal consistent Phi -> orp_witnessed Phi.
Proof.
  intros.
  hnf; intros.
  rewrite MCS_element_derivable in H0 by auto.
  apply NNPP; intro.
  apply not_or_and in H1.
  destruct H1.
  rewrite MCS_nonelement_inconsistent in H1, H2 by eauto.
  destruct H as [? _]; rewrite consistent_spec in H.
  apply H.
  eapply deduction_modus_ponens; [exact H0 |].
  apply deduction_orp_elim'; auto.
Qed.

Lemma MCS_andp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x && y) <-> (Phi x /\ Phi y)).
Proof.
  intros.
  apply maximal_consistent_derivable_closed in H.
  apply DCS_andp_iff; auto.
Qed.

Lemma MCS_orp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x || y) <-> (Phi x \/ Phi y)).
Proof.
  intros.
  apply DCS_orp_iff; auto.
  + apply maximal_consistent_derivable_closed; auto.
  + apply maximal_consistent_orp_witnessed; auto.
Qed.

Lemma MCS_impp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x y: expr, Phi (x --> y) <-> (Phi x -> Phi y)).
Proof.
  intros.
  split; intros.
  + rewrite MCS_element_derivable in H0, H1 |- * by auto.
    apply (deduction_modus_ponens _ x y); auto.
  + pose proof derivable_excluded_middle Phi y.
    rewrite <- MCS_element_derivable in H1 by auto.
    rewrite MCS_orp_iff in H1 by auto.
    pose proof derivable_excluded_middle Phi x.
    rewrite <- MCS_element_derivable in H2 by auto.
    rewrite MCS_orp_iff in H2 by auto.
    destruct H1; [| destruct H2].
    - rewrite MCS_element_derivable in H1 |- * by auto.
      apply deduction_left_impp_intros; auto.
    - exfalso.
      apply H0 in H2.
      rewrite MCS_element_derivable in H1, H2 by auto.
      pose proof deduction_modus_ponens _ _ _ H2 H1.
      destruct H as [? _].
      rewrite consistent_spec in H; auto.
    - rewrite MCS_element_derivable in H2 |- * by auto.
      unfold negp in H2.
      rewrite <- deduction_theorem in H2 |- *.
      pose proof deduction_falsep_elim _ y H2.
      auto.
Qed.

Lemma MCS_negp_iff: forall (Phi: context),
  maximal consistent Phi ->
  (forall x: expr, Phi (~~ x) <-> ~ Phi x).
Proof.
  intros.
  unfold negp.
  rewrite MCS_impp_iff by auto.
  assert (~ Phi FF); [| tauto].
  pose proof proj1 H.
  rewrite consistent_spec, <- MCS_element_derivable in H0 by auto.
  auto.
Qed.

Lemma DDCS_MCS: forall (Phi: context),
  derivable_closed Phi ->
  orp_witnessed Phi ->
  consistent Phi ->
  maximal consistent Phi.
Proof.
  intros.
  split; auto.
  intros.
  unfold Included, Ensembles.In; intros.
  pose proof derivable_excluded_middle Phi x.
  apply H in H5.
  apply H0 in H5.
  destruct H5; auto.
  exfalso.
  apply H3 in H5; unfold Ensembles.In in H5.
  rewrite consistent_spec in H2.
  apply H2; clear H2.
  apply derivable_assum in H4.
  apply derivable_assum in H5.
  eapply deduction_modus_ponens.
  - apply H4.
  - apply H5.
Qed.

End ContextProperties.
