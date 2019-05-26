Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimunLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Truth_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.ProofTheories.
Require Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context {Sigma: PropositionalLanguage.PropositionalVariables}
        {CV: Countable PropositionalLanguage.Var}.

Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Existing Instances KripkeSemantics.MD KripkeSemantics.kMD KripkeSemantics.R KripkeSemantics.SM KripkeSemantics.kminSM KripkeSemantics.kpSM.

Section General_Completeness.

Context {Gamma: ProofTheory PropositionalLanguage.L}.

Definition cP : context -> Prop := Intersection _ (Intersection _ derivable_closed orp_witnessed) consistent.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.

Lemma AL_OW: at_least orp_witnessed cP.
Proof. solve_at_least. Qed.

Lemma AL_CONSI: at_least consistent cP.
Proof. solve_at_least. Qed.

Context {SC: NormalSequentCalculus _ Gamma}
        {bSC: BasicSequentCalculus _ Gamma}
        {fwSC: FiniteWitnessedSequentCalculus _ Gamma}
        {minSC: MinimunSequentCalculus _ Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus _ Gamma}
        {AX: NormalAxiomatization _ Gamma}
        {minAX: MinimunAxiomatization _ Gamma}
        {ipGamma: IntuitionisticPropositionalLogic _ Gamma}.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply PropositionalLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    - apply Lindenbaum_cannot_derive_ensures_derivable_closed.
    - apply Lindenbaum_cannot_derive_ensures_orp_witnessed.
    - apply Lindenbaum_cannot_derive_ensures_consistent.
Qed.

Definition canonical_frame: KripkeSemantics.frame :=
  KripkeSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).

Definition canonical_eval: PropositionalLanguage.Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (PropositionalLanguage.varp p).

Definition canonical_Kmodel: @Kmodel KripkeSemantics.MD KripkeSemantics.kMD :=
  KripkeSemantics.Build_Kmodel canonical_frame canonical_eval.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Definition H_R:
  forall m n Phi Psi, rel m Phi -> rel n Psi ->
    (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).
Proof.
  intros.
  change (m = Phi) in H.
  change (n = Psi) in H0.
  subst; reflexivity.
Qed.
Existing Instances PropositionalLanguage.L PropositionalLanguage.minL PropositionalLanguage.pL.

Lemma TRUTH:
  forall x:  expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_andp cP rel AL_DC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_orp cP rel AL_DC AL_OW x1 x2 IHx1 IHx2).
  + exact (truth_lemma_impp cP rel H_R AL_DC LIN_CD x1 x2 IHx1 IHx2).
  + exact (truth_lemma_falsep cP rel AL_CONSI).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

End General_Completeness.

Section Intuitionistic_Completeness.

Existing Instances ProofTheories.IntuitionisticPropositionalLogic.G ProofTheories.IntuitionisticPropositionalLogic.AX ProofTheories.IntuitionisticPropositionalLogic.minAX ProofTheories.IntuitionisticPropositionalLogic.ipG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_intuitionistic_Kripke_all:
  strongly_complete ProofTheories.IntuitionisticPropositionalLogic.G KripkeSemantics.SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  constructor; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R cP rel H_R).
Qed.

End Intuitionistic_Completeness.

Section DeMorgan_Completeness.

Existing Instances ProofTheories.DeMorganPropositionalLogic.G ProofTheories.DeMorganPropositionalLogic.AX ProofTheories.DeMorganPropositionalLogic.minAX ProofTheories.DeMorganPropositionalLogic.ipG  ProofTheories.DeMorganPropositionalLogic.dmpG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_DeMorgan_Kripke_branch_join:
  strongly_complete ProofTheories.DeMorganPropositionalLogic.G KripkeSemantics.SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_BranchJoin)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R cP rel H_R).
  + exact (DeMorgan_canonical_branch_join cP rel H_R AL_DC AL_OW AL_CONSI LIN_CD).
Qed.

End DeMorgan_Completeness.

Section GodelDummett_Completeness.

Existing Instances ProofTheories.GodelDummettPropositionalLogic.G ProofTheories.GodelDummettPropositionalLogic.AX ProofTheories.GodelDummettPropositionalLogic.minAX ProofTheories.GodelDummettPropositionalLogic.ipG  ProofTheories.GodelDummettPropositionalLogic.gdpG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_GodelDummett_Kripke_no_branch:
  strongly_complete ProofTheories.GodelDummettPropositionalLogic.G KripkeSemantics.SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_NoBranch)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R cP rel H_R).
  + exact (GodelDummett_canonical_no_branch cP rel H_R AL_DC AL_OW).
Qed.

End GodelDummett_Completeness.

Section Classical_Completeness.

Import Logic.PropositionalLogic.DeepEmbedded.KripkeSemantics.

Existing Instances ProofTheories.ClassicalPropositionalLogic.G ProofTheories.ClassicalPropositionalLogic.AX ProofTheories.ClassicalPropositionalLogic.minAX ProofTheories.ClassicalPropositionalLogic.ipG  ProofTheories.ClassicalPropositionalLogic.cpG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC Axiomatization2SequentCalculus_cpSC.

Theorem complete_Classical_Kripke_identity:
  strongly_complete ProofTheories.ClassicalPropositionalLogic.G KripkeSemantics.SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder + Kmodel_Identity)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  constructor; [split |]; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (PropositionalLanguage.varp v)
             (TRUTH (PropositionalLanguage.varp v))).
  + exact (po_R cP rel H_R).
  + exact (classical_canonical_ident cP rel H_R AL_DC AL_OW AL_CONSI).
Qed.

End Classical_Completeness.

End Complete.
