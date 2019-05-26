Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Canonical_Kripke.
Require Import Logic.GeneralLogic.Complete.Complete_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Truth_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLanguage.
Require Logic.MinimunLogic.DeepEmbedded.MinimunLogic.
Require Logic.MinimunLogic.DeepEmbedded.KripkeSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Local Open Scope kripke_model_class.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.
Import KripkeModelClass.

Section Complete.

Context (Var: Type) (CV: Countable Var).

Instance L: Language := MinimunLanguage.L Var.
Instance minL: MinimunLanguage L := MinimunLanguage.minL Var.

Instance G: ProofTheory L := MinimunLogic.G Var.
Instance AX: NormalAxiomatization L G := MinimunLogic.AX Var.
Instance minAX: MinimunAxiomatization L G := MinimunLogic.minAX Var.
Instance SC: NormalSequentCalculus L G := MinimunLogic.SC Var.
Instance bSC: BasicSequentCalculus L G := MinimunLogic.bSC Var.
Instance fwSC: FiniteWitnessedSequentCalculus L G := MinimunLogic.fwSC Var.
Instance minSC: MinimunSequentCalculus L G := MinimunLogic.minSC Var.
Instance Kripke_MD: Model := KripkeSemantics.MD Var.
Instance Kripke_kMD: KripkeModel Kripke_MD := KripkeSemantics.kMD Var.
Instance Kripke_R (M: Kmodel): Relation (Kworlds M) := KripkeSemantics.R Var M.
Instance Kripke_SM: Semantics L Kripke_MD := KripkeSemantics.SM Var.
Instance Kripke_kminSM (M: Kmodel): KripkeMinimunSemantics L Kripke_MD M Kripke_SM := KripkeSemantics.kminSM Var M.

Definition cP: context -> Prop := derivable_closed.

Lemma AL_DC: at_least derivable_closed cP.
Proof. solve_at_least. Qed.

Lemma LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Proof.
  intros.
  apply Lindenbaum_constructable_suffice; auto.
  + apply MinimunLanguage.formula_countable; auto.
  + apply Lindenbaum_preserves_cannot_derive.
  + unfold cP.
    apply Lindenbaum_cannot_derive_ensures_derivable_closed.
Qed.

Definition canonical_frame: KripkeSemantics.frame :=
  KripkeSemantics.Build_frame (sig cP) (fun a b => Included _ (proj1_sig a) (proj1_sig b)).

Definition canonical_eval: Var -> KripkeSemantics.sem canonical_frame :=
  fun p a => proj1_sig a (MinimunLanguage.varp p).

Definition canonical_Kmodel: @Kmodel (KripkeSemantics.MD Var) (KripkeSemantics.kMD Var) :=
  KripkeSemantics.Build_Kmodel Var canonical_frame canonical_eval.

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

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_impp cP rel H_R AL_DC LIN_CD x1 x2 IHx1 IHx2).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Import Logic.MinimunLogic.DeepEmbedded.KripkeSemantics.

Theorem complete_MinimunLogic_Kripke_all:
  strongly_complete G Kripke_SM
    (KripkeModelClass _ (Kmodel_Monotonic + Kmodel_PreOrder)).
Proof.
  apply (general_completeness cP rel LIN_CD TRUTH).
  constructor; hnf.
  + intros.
    exact (denote_monotonic cP rel H_R
             (MinimunLanguage.varp v)
             (TRUTH (MinimunLanguage.varp v))).
  + exact (po_R cP rel H_R).
Qed.

End Complete.
