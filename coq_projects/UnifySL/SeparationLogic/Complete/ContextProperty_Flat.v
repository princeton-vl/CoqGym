Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.Complete.ContextProperty_Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Section ContextProperties.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {Gamma: ProofTheory L}.

Definition context_sepcon (Phi Psi: context): context :=
  fun z => exists x y, z = x * y /\ Phi |-- x /\ Psi |-- y.

Definition context_sepcon_included_l (Phi2 Psi: context): context -> Prop :=
  fun Phi1 => Included _ (context_sepcon Phi1 Phi2) Psi.

Definition context_sepcon_included_r (Phi1 Psi: context): context -> Prop :=
  fun Phi2 => Included _ (context_sepcon Phi1 Phi2) Psi.

Context {SC: NormalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}
        {minSC: MinimunSequentCalculus L Gamma}
        {ipSC: IntuitionisticPropositionalSequentCalculus L Gamma}
        {AX: NormalAxiomatization L Gamma}
        {minAX: MinimunAxiomatization L Gamma}
        {ipGamma: IntuitionisticPropositionalLogic L Gamma}
        {sGamma: SeparationLogic L Gamma}.

Lemma context_sepcon_derivable:
  forall (Phi Psi: context) z,
    context_sepcon Phi Psi |-- z ->
    exists x y, |-- x * y --> z /\ Phi |-- x /\ Psi |-- y.
Proof.
  intros.
  rewrite derivable_provable in H.
  destruct H as [xs [? ?]].
  revert z H0; induction H; intros.
  + exists TT, TT.
    split; [| split].
    - apply aux_minimun_rule00; auto.
    - apply derivable_impp_refl.
    - apply derivable_impp_refl.
  + pose proof provable_multi_imp_arg_switch1 l x z.
    pose proof modus_ponens _ _ H2 H1.
    specialize (IHForall _ H3); clear H1 H2 H3.
    destruct H as [x' [y' [? [? ?]]]]; subst x.
    destruct IHForall as [x [y [? [? ?]]]].
    exists (x && x'), (y && y').
    split; [| split].
    - clear l H0 H1 H2 H3 H4.
      rewrite (provable_sepcon_andp_right (x && x') y y').
      rewrite (provable_sepcon_andp_left x x' y).
      rewrite (provable_sepcon_andp_left x x' y').
      rewrite (andp_elim1 (x * y) _).
      rewrite (andp_elim2 _ (x' * y')).
      rewrite <- impp_curry_uncurry.
      auto.
    - apply deduction_andp_intros; auto.
    - apply deduction_andp_intros; auto.
Qed.

Lemma context_sepcon_consistent_rev_left:
  forall (Phi1 Phi2 Psi: context),
    Included _ (context_sepcon Phi1 Phi2) Psi ->
    consistent Psi ->
    consistent Phi1.
Proof.
  intros.
  rewrite consistent_spec in H0 |- *.
  intro; apply H0; clear H0.
  rewrite <- (falsep_sepcon TT).
  apply derivable_assum.
  apply H; exists FF, TT; split; [| split]; auto.
  apply derivable_impp_refl.
Qed.

Lemma context_sepcon_included_l_derivable_subset_preserved: forall Phi2 Psi,
  derivable_subset_preserved (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros Phi1 Phi1' ? ?.
  eapply Included_trans; [clear Psi H0 | exact H0].
  unfold Included, Ensembles.In; intros z ?.
  destruct H0 as [x [y [? [? ?]]]].
  exists x, y; split; [| split]; auto.
  apply H; auto.
Qed.

Lemma context_sepcon_included_l_subset_preserved: forall Phi2 Psi,
  subset_preserved (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  apply derivable_subset_preserved_subset_preserved.
  apply context_sepcon_included_l_derivable_subset_preserved.
Qed.

Lemma context_sepcon_included_l_finite_captured: forall Phi2 Psi,
  finite_captured (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros.
  unfold Included, Ensembles.In; intros z ?.
  destruct H0 as [x [y [? [? ?]]]].
  apply derivable_finite_witnessed in H1.
  destruct H1 as [xs [? ?]].
  specialize (H _ H1).
  subst z.
  apply H; auto; unfold Ensembles.In.
  exists x, y; split; [| split]; auto.
Qed.

Lemma context_sepcon_included_l_context_orp_captured: forall Phi2 Psi
      (DC: derivable_closed Psi)
      (OW: orp_witnessed Psi),
  context_orp_captured (context_sepcon_included_l Phi2 Psi).
Proof.
  intros.
  unfold context_sepcon_included_l.
  hnf; intros Phi1 Phi1' ?.
  assert (forall z1 z2,
            context_sepcon Phi1 Phi2 z1  ->
            ~ Psi z1 ->
            context_sepcon Phi1' Phi2 z2 ->
            ~ Psi z2 ->
            False) as HH.
  Focus 2. {
    clear - HH; unfold Included, Ensembles.In.
    apply NNPP; intro.
    apply not_or_and in H; destruct H.
    apply not_all_ex_not in H.
    apply not_all_ex_not in H0.
    destruct H as [z1 ?], H0 as [z2 ?].
    specialize (HH z1 z2).
    tauto.
  } Unfocus.
  intros.
  destruct H0 as [x1 [y1 [? [? ?]]]], H2 as [x2 [y2 [? [? ?]]]].
  subst z1 z2.
  assert (context_orp Phi1 Phi1' (x1 || x2));
  [| assert (context_sepcon (context_orp Phi1 Phi1') Phi2 ((x1 || x2) * (y1 && y2)));
     [| assert (Psi |-- (x1 * y1) || (x2 * y2))]].
  + exists x1, x2.
    split; [| split]; auto.
  + exists (x1 || x2), (y1 && y2).
    split; [| split]; auto.
    - apply derivable_assum; auto.
    - apply deduction_andp_intros; auto.
  + apply H in H2.
    apply derivable_assum in H2.
    rewrite sepcon_orp_distr_l in H2.
    rewrite (andp_elim1 y1 y2) in H2 at 1.
    rewrite (andp_elim2 y1 y2) in H2 at 1.
    auto.
  + rewrite <- derivable_closed_element_derivable in H8 by auto.
    apply OW in H8.
    tauto.
Qed.

Lemma wand_deduction_theorem:
  forall (Phi: context) x y,
    context_sepcon Phi (Union _ empty_context (Singleton _ x)) |-- y <->
    Phi |-- x -* y.
Proof.
  intros.
  split; intros.
  + apply context_sepcon_derivable in H.
    destruct H as [x' [y' [? [? ?]]]].
    rewrite deduction_theorem, <- provable_derivable in H1.
    rewrite <- H1 in H.
    apply wand_sepcon_adjoint in H.
    rewrite H in H0; auto.
  + rewrite <- (provable_wand_sepcon_modus_ponens1 x y).
    apply derivable_assum.
    exists (x -* y), x.
    split; [| split]; auto.
    rewrite deduction_theorem.
    apply derivable_impp_refl.
Qed.

Lemma context_sepcon_included_equiv: forall Phi Psi,
  derivable_closed Psi ->
  Same_set _ (context_sepcon_included_l Phi Psi) (context_sepcon_included_r Phi Psi).
Proof.
  intros.
  rewrite Same_set_spec; intros Phi'; split; intros.
  + hnf; intros.
    destruct H1 as [y [z [? [? ?]]]].
    subst x.
    apply H.
    rewrite <- sepcon_comm.
    apply derivable_assum.
    apply H0.
    exists z, y; split; [| split]; auto.
  + hnf; intros.
    destruct H1 as [y [z [? [? ?]]]].
    subst x.
    apply H.
    rewrite <- sepcon_comm.
    apply derivable_assum.
    apply H0.
    exists z, y; split; [| split]; auto.
Qed.

End ContextProperties.
