Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
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
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Complete.Canonical_Kripke.
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

Section Canonical.

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

Instance SA
         (AL_DC: at_least derivable_closed cP)
         (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP):
  SeparationAlgebra (Kworlds M).
Proof.
  constructor.
  + intros.
    destruct (im_bij _ _ rel m1) as [Phi1 ?].
    destruct (im_bij _ _ rel m2) as [Phi2 ?].
    destruct (im_bij _ _ rel m) as [Phi ?].
    erewrite H_J in H |- * by eauto.
    hnf; intros.
    destruct H3 as [y [z [? [? ?]]]].
    subst.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    rewrite sepcon_comm.
    rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    apply H.
    exists z, y; split; [| split]; auto.
  + intros.
    destruct (im_bij _ _ rel mx) as [Phi_x ?].
    destruct (im_bij _ _ rel my) as [Phi_y ?].
    destruct (im_bij _ _ rel mz) as [Phi_z ?].
    destruct (im_bij _ _ rel mxy) as [Phi_xy ?].
    destruct (im_bij _ _ rel mxyz) as [Phi_xyz ?].
    erewrite H_J in H, H0 by eauto.
    assert (Included _ (context_sepcon (proj1_sig Phi_x)
             (context_sepcon (proj1_sig Phi_y) (proj1_sig Phi_z))) (proj1_sig Phi_xyz)).
    - hnf; intros xyz ?.
      destruct H6 as [x [yz [? [? ?]]]]; subst xyz.
      apply context_sepcon_derivable in H8.
      destruct H8 as [y [z [? [? ?]]]].
      rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi_xyz)).
      rewrite <- H6, sepcon_assoc.
      rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi_xyz)).
      apply H0.
      exists (x * y), z; split; [| split]; auto.
      rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi_xy)).
      apply H.
      exists x, y; split; [| split]; auto.
    - apply LIN_SR in H6.
      destruct H6 as [Phi_yz [? ?]].
      unfold context_sepcon_included_r in H7.
      destruct (su_bij _ _ rel Phi_yz) as [myz ?].
      exists myz.
      erewrite !H_J by eauto.
      auto.
Qed.

Instance uSA
         (AL_DC: at_least derivable_closed cP):
  UpwardsClosedSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  exists m1, m2.
  destruct (im_bij _ _ rel n) as [Psi ?].
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H |- * by eauto.
  erewrite H_R in H0 by eauto.
  do 2 erewrite H_R by eauto.
  split; [| split].
  + eapply Included_trans; eauto.
  + hnf; intros; auto.
  + hnf; intros; auto.
Qed.

Instance dSA
         (AL_DC: at_least derivable_closed cP):
  DownwardsClosedSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  exists m.
  destruct (im_bij _ _ rel n1) as [Psi1 ?].
  destruct (im_bij _ _ rel n2) as [Psi2 ?].
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H |- * by eauto.
  erewrite H_R in H0, H1 |- * by eauto.
  split.
  + eapply Included_trans; eauto.
    hnf; intros z [x [y [? [? ?]]]]; subst.
    exists x, y.
    split; [| split]; auto.
    - eapply deduction_weaken; eauto.
    - eapply deduction_weaken; eauto.
  + hnf; intros; auto.
Qed.

Lemma garbage_collected_canonical_increaing
      {gcsGamma: GarbageCollectSeparationLogic L Gamma}
      (AL_DC: at_least derivable_closed cP):
  IncreasingSeparationAlgebra (Kworlds M).
Proof.
  constructor.
  intros m; hnf; intros n1 n2 ?.
  destruct (im_bij _ _ rel n1) as [Psi1 ?].
  destruct (im_bij _ _ rel n2) as [Psi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_R by eauto.
  erewrite H_J in H by eauto.
  unfold Included, Ensembles.In; intros.
  rewrite derivable_closed_element_derivable in H3 by (apply AL_DC, (proj2_sig Psi1)).
  rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Psi2)).
  rewrite <- (sepcon_elim2 TT).
  rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Psi2)).
  apply H; auto.
  exists TT, x; split; [| split]; auto.
  apply derivable_impp_refl.
Qed.

Lemma ext_canonical_residual
      {ExtSGamma: ExtSeparationLogic L Gamma}
      (AL_DC: at_least derivable_closed cP)
      (LIN_SL: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_l Phi (proj1_sig Psi)) cP):
  ResidualSeparationAlgebra (Kworlds M).
Proof.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  assert (Included _ (context_sepcon (Union _ empty_context (Singleton _ TT)) (proj1_sig Phi)) (proj1_sig Phi)).
  + hnf; intros.
    destruct H0 as [y [z [? [? ?]]]].
    rewrite deduction_theorem, <- provable_derivable in H1.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    subst; rewrite <- H1.
    rewrite <- sepcon_comm, <- sepcon_ext; auto.
  + apply LIN_SL in H0.
    destruct H0 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    exists n; split.
    - erewrite H_J by eauto.
      auto.
    - erewrite H_R by eauto.
      hnf; intros; auto.
Qed.

Context {s'L: SeparationEmpLanguage L}
        {EmpsGamma: EmpSeparationLogic L Gamma}
        {feSM: EmpSemantics L MD M SM}.

Instance unitSA
         (AL_DC: at_least derivable_closed cP)
         (LIN_SR: forall (Phi: context) (Psi: sig cP), Lindenbaum_constructable (context_sepcon_included_r Phi (proj1_sig Psi)) cP)
         (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  UnitalSeparationAlgebra (Kworlds M).
Proof.
  intros.
  constructor.
  intros.
  destruct (im_bij _ _ rel n) as [Phi ?].
  assert (Included _ (context_sepcon (proj1_sig Phi) (Union _ empty_context (Singleton _ emp))) (proj1_sig Phi)).
  + hnf; intros.
    destruct H0 as [y [z [? [? ?]]]].
    rewrite deduction_theorem, <- provable_derivable in H2.
    rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    subst; rewrite <- H2, sepcon_emp; auto.
  + apply LIN_SR in H0.
    destruct H0 as [Psi [? ?]].
    destruct (su_bij _ _ rel Psi) as [m ?].
    exists m.
    split; [exists n; split |].
    - apply (@join_comm _ _ (SA AL_DC LIN_SR)).
      erewrite H_J by eauto.
      auto.
    - erewrite H_R by eauto.
      hnf; intros; auto.
    - clear H1 n Phi H.
      specialize (H0 emp ltac:(right; constructor)).
      unfold Ensembles.In in H0.
      rewrite <- (TRUTH emp) in H0 by eauto.
      rewrite sat_emp in H0; auto.
Qed.

Lemma nonsplit_canonical_split_smaller
      {nssGamma: NonsplitEmpSeparationLogic L Gamma}
      (AL_DC: at_least derivable_closed cP)
      (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  IncreasingSplitSmallerSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  destruct (im_bij _ _ rel m1) as [Phi1 ?].
  destruct (im_bij _ _ rel m2) as [Phi2 ?].
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J in H0 by eauto.
  erewrite H_R by eauto.
  unfold Included, Ensembles.In; intros x ?.
  rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
  rewrite <- (emp_sepcon_truep_elim x).
  apply deduction_andp_intros.
  + apply derivable_assum; apply H0.
    exists x, TT; split; [| split]; auto.
    - apply derivable_assum; auto.
    - apply derivable_impp_refl.
  + rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)).
    rewrite <- (TRUTH emp) by eauto.
    rewrite sat_emp; auto.
Qed.

Lemma dup_canonical_incr_join
      {desGamma: DupEmpSeparationLogic L Gamma}
      (AL_DC: at_least derivable_closed cP)
      (TRUTH: forall x, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x)):
  IncreasingJoinSelfSeparationAlgebra (Kworlds M).
Proof.
  hnf; intros.
  destruct (im_bij _ _ rel m) as [Phi ?].
  erewrite H_J by eauto.
  intros z [x [y [? [? ?]]]]; subst.
  rewrite derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)); auto.
  rewrite <- (andp_elim1 x y).
  rewrite <- (andp_elim2 x y) at 2.
  rewrite <- emp_dup.
  apply deduction_andp_intros; [apply deduction_andp_intros |]; auto.
  rewrite <- derivable_closed_element_derivable by (apply AL_DC, (proj2_sig Phi)); auto.
  unfold Ensembles.In; rewrite <- (TRUTH emp) by eauto.
  rewrite sat_emp; auto.
Qed.

End Canonical.
