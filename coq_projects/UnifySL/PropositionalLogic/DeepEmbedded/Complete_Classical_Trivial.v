Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Trivial.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.PropositionalLogic.Complete.Lindenbaum_Trivial.
Require Import Logic.PropositionalLogic.Complete.Truth_Trivial.
Require Import Logic.PropositionalLogic.Complete.Complete_Trivial.
Require Logic.PropositionalLogic.DeepEmbedded.PropositionalLanguage.
Require Logic.PropositionalLogic.DeepEmbedded.ProofTheories.
Require Logic.PropositionalLogic.DeepEmbedded.TrivialSemantics.

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

Existing Instances TrivialSemantics.MD TrivialSemantics.SM TrivialSemantics.tminSM TrivialSemantics.tpSM.

Existing Instances ProofTheories.ClassicalPropositionalLogic.G ProofTheories.ClassicalPropositionalLogic.AX ProofTheories.ClassicalPropositionalLogic.minAX ProofTheories.ClassicalPropositionalLogic.ipG  ProofTheories.ClassicalPropositionalLogic.cpG.

Existing Instances Axiomatization2SequentCalculus_SC Axiomatization2SequentCalculus_bSC Axiomatization2SequentCalculus_fwSC Axiomatization2SequentCalculus_minSC Axiomatization2SequentCalculus_ipSC Axiomatization2SequentCalculus_cpSC.

Definition cP: context -> Prop := maximal consistent.

Lemma AL_MC: at_least (maximal consistent) cP.
Proof. solve_at_least. Qed.

Lemma LIN_CONSI: Lindenbaum_constructable consistent cP.
Proof.
  eapply Lindenbaum_constructable_Same_set.
  + rewrite Same_set_spec.
    intros Phi.
    apply consistent_spec.
  + apply Lindenbaum_constructable_suffice.
    - apply PropositionalLanguage.formula_countable; auto.
    - apply Lindenbaum_preserves_cannot_derive.
    - apply Lindenbaum_cannot_derive_ensures_max_consistent.
Qed.

Definition canonical_frame: Type := sig cP.

Definition canonical_eval: PropositionalLanguage.Var -> canonical_frame -> Prop :=
  fun p a => proj1_sig a (PropositionalLanguage.varp p).

Definition kMD: KripkeModel TrivialSemantics.MD :=
  Build_KripkeModel TrivialSemantics.MD
    unit (fun _ => canonical_frame) (fun u a v => canonical_eval v a).

Definition canonical_Kmodel: @Kmodel TrivialSemantics.MD kMD := tt.

Definition rel: bijection (Kworlds canonical_Kmodel) (sig cP) := bijection_refl.

Lemma TRUTH:
  forall x: expr, forall m Phi, rel m Phi ->
    (KRIPKE: canonical_Kmodel, m |= x <-> proj1_sig Phi x).
Proof.
  induction x.
  + exact (truth_lemma_andp cP rel AL_MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_orp cP rel AL_MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_impp cP rel AL_MC x1 x2 IHx1 IHx2).
  + exact (truth_lemma_falsep cP rel AL_MC).
  + intros; change (m = Phi) in H; subst; reflexivity.
Qed.

Existing Instance kMD.

Theorem complete_Classical_Trivial:
  strongly_complete ProofTheories.ClassicalPropositionalLogic.G TrivialSemantics.SM (AllModel _).
Proof.
  assert (strongly_complete ProofTheories.ClassicalPropositionalLogic.G TrivialSemantics.SM
           (KripkeModelClass _ (fun _ => True))).
  Focus 2. {
    hnf; intros.
    apply (H Phi x).
    hnf; intros.
    apply H0; auto.
    hnf; auto.
  } Unfocus.
  apply (@general_completeness PropositionalLanguage.L _ _ ProofTheories.ClassicalPropositionalLogic.G _ _ _ _
           _ _ _ TrivialSemantics.SM _ _ _ _ rel LIN_CONSI TRUTH); auto.
Qed.

End Complete.
