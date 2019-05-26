Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.SeparationLogic.Complete.ContextProperty_Flat.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section TruthLemma.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}
        {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {AX: NormalAxiomatization L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {J: Join (Kworlds M)}
        {SM: Semantics L MD}
        {fsSM: SeparatingSemantics L MD M SM}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis H_R: forall m n Phi Psi, rel m Phi -> rel n Psi -> (m <= n <-> Included _ (proj1_sig Phi) (proj1_sig Psi)).

Hypothesis H_J: forall m1 m2 m Phi1 Phi2 Phi, rel m1 Phi1 -> rel m2 Phi2 -> rel m Phi -> (join m1 m2 m <-> Included _ (context_sepcon (proj1_sig Phi1) (proj1_sig Phi2)) (proj1_sig Phi)).

Lemma truth_lemma_sepcon
      (AL_DC: at_least derivable_closed cP)
      (LIN_SL: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_l Phi (proj1_sig Psi)) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x * y <-> proj1_sig Phi (x * y)).
Proof.
  intros.
  rewrite sat_sepcon.
  split; intros.
  + destruct H0 as [m1 [m2 [? [? ?]]]].
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHx in H1 by eauto.
    erewrite IHy in H2 by eauto.
    erewrite H_J in H0 by eauto.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    apply derivable_assum.
    apply H0.
    exists x, y; split; [| split]; auto; apply derivable_assum; auto.
  + apply derivable_assum in H0.
    assert (Included _ (context_sepcon (Union _ empty_context (Singleton _ x))
             (Union _ empty_context (Singleton _ y))) (proj1_sig Phi)).
    Focus 1. {
      hnf; intros z ?.
      destruct H1 as [x0 [y0 [? [? ?]]]].
      rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
      rewrite deduction_theorem, <- provable_derivable in H2, H3.
      subst z; rewrite <- H2, <- H3.
      auto.
     } Unfocus.
    apply LIN_SL in H1.
    destruct H1 as [Phi1 [? ?]].
    apply LIN_SR in H2.
    destruct H2 as [Phi2 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    exists m1, m2.
    erewrite H_J, IHx, IHy by eauto.
    split; [| split]; auto.
    - apply H1; right; constructor.
    - apply H2; right; constructor.
Qed.

Lemma truth_lemma_wand
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP)
      (x y: expr)
      (IHx: forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x))
      (IHy: forall m Phi, rel m Phi -> (KRIPKE: M, m |= y <-> proj1_sig Phi y)):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= x -* y <-> proj1_sig Phi (x -* y)).
Proof.
  intros.
  rewrite sat_wand.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)); auto.
    rewrite <- wand_deduction_theorem.
    apply NNPP; intro.
    apply LIN_CD in H1.
    destruct H1 as [Phi2 [? ?]].
    apply H2; clear H2.
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)); auto.
    apply LIN_SR in H1.
    destruct H1 as [Phi1 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    erewrite <- IHy by eauto.
    unfold context_sepcon_included_r in H2; erewrite <- H_J in H2 by eauto.
    apply (H0 _ _ H2).
    erewrite IHx by eauto.
    apply H1; right; constructor.
  + destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    erewrite IHy by eauto.
    erewrite IHx in H2 by eauto.
    erewrite H_J in H1 by eauto.
    rewrite derivable_closed_element_derivable in H0 by (apply AL_DC, (proj2_sig Phi)).
    rewrite derivable_closed_element_derivable in H2 by (apply AL_DC, (proj2_sig Phi1)).
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)).
    rewrite <- provable_wand_sepcon_modus_ponens1 with (x0 := x).
    apply derivable_assum; apply H1.
    exists (x -* y), x; split; [| split]; auto.
Qed.

Context {s'L: SeparationEmpLanguage L}
        {eGamma: EmpSeparationLogic L Gamma}
        {feSM: EmpSemantics L MD M SM}.

Lemma truth_lemma_emp
      (AL_DC: at_least derivable_closed cP)
      (LIN_CD: forall x, Lindenbaum_constructable (cannot_derive x) cP)
      (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP):
  forall m Phi, rel m Phi -> (KRIPKE: M, m |= emp <-> proj1_sig Phi emp).
Proof.
  intros.
  rewrite sat_emp.
  split; intros.
  + rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)); auto.
    rewrite <- (provable_wand_sepcon_modus_ponens1 emp).
    rewrite sepcon_emp.
    apply wand_deduction_theorem.
    apply NNPP; intro.
    apply LIN_CD in H1.
    destruct H1 as [Phi2 [? ?]].
    apply H2; clear H2.
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)); auto.
    apply LIN_SR in H1.
    destruct H1 as [Phi1 [? ?]].
    destruct (su_bij _ _ rel Phi1) as [m1 ?].
    destruct (su_bij _ _ rel Phi2) as [m2 ?].
    unfold context_sepcon_included_r in H2; erewrite <- H_J in H2 by eauto.
    apply H0 in H2.
    erewrite H_R in H2 by eauto.
    apply H2, H1; right; constructor.
  + hnf; intros n1 n2 ?.
    destruct (im_bij _ _ rel n1) as [Phi1 ?].
    destruct (im_bij _ _ rel n2) as [Phi2 ?].
    erewrite H_R by eauto.
    erewrite H_J in H1 by eauto.
    intros x; unfold Ensembles.In; intros.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi2)); auto.
    rewrite derivable_closed_element_derivable in H4 by (apply AL_DC, (proj2_sig Phi1)); auto.
    rewrite derivable_closed_element_derivable in H0 by (apply AL_DC, (proj2_sig Phi)); auto.
    rewrite <- sepcon_emp, sepcon_comm.
    apply derivable_assum; apply H1.
    exists emp, x; split; [| split]; auto.
Qed.

End TruthLemma.
