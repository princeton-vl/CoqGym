Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kminSM: KripkeMinimunSemantics L MD M SM}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Lemma truth_lemma_impp
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x --> y <-> proj1_sig Phi (x --> y)).
Proof.
  intros.
  rewrite sat_impp.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    rewrite <- deduction_theorem.
    apply NNPP; intro.
    apply LIN_CD in H1.
    destruct H1 as [Psi [? ?]].
    apply H2; clear H2.
    assert (Included _ (proj1_sig Phi) (proj1_sig Psi)) by (intros ? ?; apply H1; left; auto).
    assert (proj1_sig Psi x) by (apply H1; right; constructor; auto).
    clear H1.
    destruct (su_bij _ _ rel Psi) as [n ?].
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Psi)).
    rewrite <- (IHx _ _ H1) in H3.
    rewrite <- (IHy _ _ H1).
    apply H0; auto.
    erewrite H_R by eauto.
    auto.
  + destruct (im_bij _ _ rel n) as [Psi ?].
    rewrite (IHx _ _ H3) in H2.
    rewrite (IHy _ _ H3).
    rewrite derivable_closed_element_derivable in H2 |- * by (apply AL_DC, (proj2_sig Psi)).
    eapply deduction_modus_ponens; [exact H2 |].
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Psi)).
    erewrite H_R in H1 by eauto.
    apply H1; auto.
Qed.

End TruthLemma.


