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
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.
Require Import Logic.SeparationLogic.Complete.Lindenbaum_Flat.
Require Import Logic.SeparationLogic.Complete.Truth_Flat.
Require Import Logic.SeparationLogic.Complete.Canonical_Flat.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Logic.SeparationLogic.DeepEmbedded.FlatSemantics.
Require Logic.SeparationLogic.DeepEmbedded.ParametricSeparationLogic.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context {Sigma: SeparationEmpLanguage.PropositionalVariables}
        {CV: Countable SeparationEmpLanguage.Var}
        (SLP: SL_Parameter).

Existing Instances SeparationEmpLanguage.L SeparationEmpLanguage.minL SeparationEmpLanguage.pL SeparationEmpLanguage.sL SeparationEmpLanguage.s'L.

Existing Instances ParametricSeparationLogic.G ParametricSeparationLogic.AX ParametricSeparationLogic.minAX  ParametricSeparationLogic.ipG ParametricSeparationLogic.sG ParametricSeparationLogic.eG ParametricSeparationLogic.ParG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC Axiomatization2SequentCalculus_cpSC.

Existing Instances FlatSemantics.MD FlatSemantics.kMD FlatSemantics.R FlatSemantics.J FlatSemantics.SM FlatSemantics.kminSM FlatSemantics.kpSM FlatSemantics.fsSM FlatSemantics.feSM.

Definition cP : context -> Prop := Intersection _ (Intersection _ derivable_closed orp_witnessed) consistent.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.

Lemma AL_OW: at_least orp_witnessed cP.
Proof. solve_at_least. Qed.

Lemma AL_CONSI: at_least consistent cP.
Proof. solve_at_least. Qed.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply SeparationEmpLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    - apply Lindenbaum_cannot_derive_ensures_derivable_closed.
    - apply Lindenbaum_cannot_derive_ensures_orp_witnessed.
    - apply Lindenbaum_cannot_derive_ensures_consistent.
Qed.

Lemma LIN_SL: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_l Phi (proj1_sig Psi)) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply SeparationEmpLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_context_sepcon_included_l.
  + unfold cP.
    repeat apply Lindenbaum_ensures_by_conjunct.
    - apply Lindenbaum_context_sepcon_included_l_ensures_derivable_closed.
    - apply Lindenbaum_context_sepcon_included_l_ensures_orp_witnessed.
      * apply AL_DC, (proj2_sig Psi).
      * apply AL_OW, (proj2_sig Psi).
    - apply Lindenbaum_context_sepcon_included_l_ensures_consistent.
      apply AL_CONSI, (proj2_sig Psi).
Qed.

Lemma LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP.
Proof.
  intros.
  eapply Lindenbaum_constructable_Same_set.
  + symmetry.
    apply context_sepcon_included_equiv.
    apply AL_DC, (proj2_sig Psi).
  + apply LIN_SL.
Qed.

Definition canonical_frame: FlatSemantics.frame :=
  FlatSemantics.Build_frame (sig cP)
    (fun a b => Included _ (proj1_sig a) (proj1_sig b))
    (fun a b c => Included _ (context_sepcon (proj1_sig a) (proj1_sig b)) (proj1_sig c)).

Definition canonical_eval: SeparationEmpLanguage.Var -> FlatSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (SeparationEmpLanguage.varp p).

Definition canonical_Kmodel: @Kmodel FlatSemantics.MD FlatSemantics.kMD :=
  FlatSemantics.Build_Kmodel canonical_frame canonical_eval.

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

Definition H_J:
  forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi ->
    (join m1 m2 m <-> Included _ (context_sepcon (proj1_sig Phi1) (proj1_sig Phi2)) (proj1_sig Phi)).
Proof.
  intros.
  change (m = Phi) in H1.
  change (m1 = Phi1) in H.
  change (m2 = Phi2) in H0.
  subst; reflexivity.
Qed.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_andp cP rel AL_DC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_orp cP rel AL_DC AL_OW x1 x2 IHx1 IHx2).
  + exact (truth_lemma_impp cP rel H_R AL_DC LIN_CD x1 x2 IHx1 IHx2).
  + exact (truth_lemma_sepcon cP rel H_J AL_DC LIN_SL LIN_SR x1 x2 IHx1 IHx2).
  + exact (truth_lemma_wand cP rel H_J AL_DC LIN_CD LIN_SR x1 x2 IHx1 IHx2).
  + exact (truth_lemma_emp cP rel H_R H_J AL_DC LIN_CD LIN_SR).
  + exact (truth_lemma_falsep cP rel AL_CONSI).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Context (SAP: SA_Parameter).

Hypothesis PC: Parameter_coincide SLP SAP.

Theorem ParametricCompleteness:
  strongly_complete (ParametricSeparationLogic.G SLP) FlatSemantics.SM
    (KripkeModelClass _
      (FlatSemantics.Kmodel_Monotonic +
       FlatSemantics.Kmodel_PreOrder +
       FlatSemantics.Kmodel_SeparationAlgebra +
       FlatSemantics.Kmodel_UpwardsClosed +
       FlatSemantics.Kmodel_DownwardsClosed +
       FlatSemantics.Kmodel_Unital +
       FlatSemantics.Parametric_Kmodel_Class SAP)).
Proof.
  apply (@general_completeness _ _ _ _ _ _ _ _ cP rel LIN_CD TRUTH).
  split; [split; [split; [split; [split; [split |] |] |] |] |].
  + hnf; intros.
    exact (denote_monotonic cP rel H_R
             (SeparationEmpLanguage.varp v)
             (TRUTH (SeparationEmpLanguage.varp v))).
  + exact (po_R cP rel H_R).
  + exact (SA cP rel H_J AL_DC LIN_SR).
  + exact (uSA cP rel H_R H_J AL_DC).
  + exact (dSA cP rel H_R H_J AL_DC).
  + exact (unitSA cP rel H_R H_J AL_DC LIN_SR TRUTH).
  + inversion PC.
    constructor; intros HH; rewrite HH in *.
    - pose proof ParametricSeparationLogic.Parametric_C H.
      exact (classical_canonical_ident cP rel H_R AL_DC AL_OW AL_CONSI).
    - pose proof ParametricSeparationLogic.Parametric_GD H0.
      exact (GodelDummett_canonical_no_branch cP rel H_R AL_DC AL_OW).
    - pose proof ParametricSeparationLogic.Parametric_DM H1.
      exact (DeMorgan_canonical_branch_join cP rel H_R AL_DC AL_OW AL_CONSI LIN_CD).
    - pose proof ParametricSeparationLogic.Parametric_GC H2.
      exact (garbage_collected_canonical_increaing cP rel H_R H_J AL_DC).
    - pose proof ParametricSeparationLogic.Parametric_NE H3.
      exact (nonsplit_canonical_split_smaller cP rel H_R H_J AL_DC TRUTH).
    - pose proof ParametricSeparationLogic.Parametric_ED H4.
      exact (dup_canonical_incr_join cP rel H_J AL_DC TRUTH).
Qed.

End Complete.
