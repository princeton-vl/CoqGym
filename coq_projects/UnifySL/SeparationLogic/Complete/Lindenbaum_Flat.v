Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section Lindenbaum_Flat.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {AX: NormalAxiomatization L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}.

Lemma Lindenbaum_preserves_context_sepcon_included_l: forall Phi2 Psi,
  Lindenbaum_preserves (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  apply Lindenbaum_preserves_by_finiteness.
  + apply context_sepcon_included_l_finite_captured.
  + apply context_sepcon_included_l_subset_preserved.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_derivable_closed: forall Phi Psi,
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) derivable_closed.
Proof.
  intros.
  apply Lindenbaum_for_derivable_closed.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + apply context_sepcon_included_l_derivable_subset_preserved.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_orp_witnessed: forall Phi Psi
      (DC: derivable_closed Psi)
      (OW: orp_witnessed Psi),
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) orp_witnessed.
Proof.
  intros.
  apply Lindenbaum_for_orp_witnessed.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + apply context_sepcon_included_l_subset_preserved.
  + apply context_sepcon_included_l_context_orp_captured; auto.
  + apply Lindenbaum_context_sepcon_included_l_ensures_derivable_closed.
Qed.

Lemma Lindenbaum_context_sepcon_included_l_ensures_consistent: forall Phi Psi
  (CONSI: consistent Psi),
  Lindenbaum_ensures (context_sepcon_included_l Phi Psi) consistent.
Proof.
  intros.
  apply Lindenbaum_for_consistent.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + intros Phi' ?.
    eapply context_sepcon_consistent_rev_left; eauto.
Qed.

End Lindenbaum_Flat.
