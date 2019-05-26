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

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section Lindenbaum_Kripke.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}.

Lemma Lindenbaum_for_orp_witnessed: forall P,
  Lindenbaum_preserves P ->
  subset_preserved P ->
  context_orp_captured P ->
  Lindenbaum_ensures P derivable_closed ->
  Lindenbaum_ensures P orp_witnessed.
Proof.
  intros; hnf; intros.
  specialize (H2 CA init H3).
  rename H2 into DC.
  hnf; intros.
  pose proof H0.
  apply subset_preserved_same_set_preserved in H4.
  pose proof H CA _ H3.
  destruct (im_inj _ _ CA x) as [n ?].
  destruct (im_inj _ _ CA y) as [m ?].
  rewrite <- !Lindenbaum_pointwise_finite_decided' by eauto.
  apply H1.
  eapply H0; [| exact H5].
  unfold Included, Ensembles.In; intros z ?.
  destruct H8 as [x0 [y0 [? [? ?]]]]; subst z.
  apply deduction_orp_intros1 with (y1 := y0) in H9.
  apply deduction_orp_intros2 with (x1 := x0) in H10.
  rewrite deduction_theorem in H9, H10.
  eapply deduction_weaken in H9; [| apply Lindenbaum_included_n_omega].
  eapply deduction_weaken in H10; [| apply Lindenbaum_included_n_omega].
  pose proof deduction_orp_elim' _ _ _ _ H9 H10.
  apply derivable_assum in H2.
  pose proof deduction_modus_ponens _ _ _ H2 H8.
  apply DC; auto.
Qed.

Lemma Lindenbaum_cannot_derive_ensures_orp_witnessed {AX: NormalAxiomatization L Gamma}: forall x, Lindenbaum_ensures (cannot_derive x) orp_witnessed.
Proof.
  intros.
  apply Lindenbaum_for_orp_witnessed.
  - apply Lindenbaum_preserves_cannot_derive.
  - apply cannot_derive_subset_preserved.
  - apply cannot_derive_context_orp_captured.
  - apply Lindenbaum_cannot_derive_ensures_derivable_closed.
Qed.

Lemma Lindenbaum_for_consistent: forall P,
  Lindenbaum_preserves P ->
  at_least consistent P ->
  Lindenbaum_ensures P consistent.
Proof.
  intros.
  hnf; intros.
  apply H0.
  apply H; auto.
Qed.

Lemma Lindenbaum_cannot_derive_ensures_consistent {AX: NormalAxiomatization L Gamma}: forall x, Lindenbaum_ensures (cannot_derive x) consistent.
Proof.
  intros.
  apply Lindenbaum_for_consistent.
  - apply Lindenbaum_preserves_cannot_derive.
  - unfold cannot_derive.
    hnf; intros.
    exists x; auto.
Qed.

End Lindenbaum_Kripke.
