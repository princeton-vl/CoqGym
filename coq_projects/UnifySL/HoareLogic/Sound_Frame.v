Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.HoareLogic.ImperativeLanguage.
Require Import Logic.HoareLogic.ProgramState.
Require Import Logic.HoareLogic.BigStepSemantics.
Require Import Logic.HoareLogic.HoareTriple_BigStepSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelSingleNotation.
Import KripkeModelNotation_Intuitionistic.

Section soundness.

Existing Instance unit_kMD.

Context {P: ProgrammingLanguage}
        {MD: Model}
        {BSS: BigStepSemantics P model}
        {J: Join model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {SA_BSS: SABigStepSemantics P model BSS}.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {fsSM: FlatSemantics.SeparatingSemantics L MD tt SM}.

Lemma hoare_frame_partial_sound: forall c P Q F,
  triple_partial_valid P c Q ->
  triple_partial_valid (P * F) c (Q * F).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros m' _n' ? ?.
  rewrite FlatSemantics.sat_sepcon in H0.
  destruct H0 as [m [mf [? [? ?]]]].
  assert (SAFE: safe m c) by exact (H m Error H2).
  destruct (frame_property _ _ _ _ _ H0 H1) as [_n [nf [? [? ?]]]].
  destruct _n' as [| | n'].
  + inversion H5; subst.
    revert H6; apply SAFE.
  + auto.
  + rewrite FlatSemantics.sat_sepcon.
    inversion H5; subst.
    - exfalso; revert H6; apply SAFE.
    - rename x into n.
      exists n, nf.
      split; [| split]; auto.
      * apply (H m _ H2 H6).
      * eapply sat_mono; eauto.
Qed.

Lemma hoare_frame_total_sound: forall c P Q F,
  triple_total_valid P c Q ->
  triple_total_valid (P * F) c (Q * F).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros m' _n' ? ?.
  rewrite FlatSemantics.sat_sepcon in H0.
  destruct H0 as [m [mf [? [? ?]]]].
  assert (SAFE: safe m c) by exact (H m Error H2).
  assert (TERM: term_norm m c) by exact (conj (H m Error H2) (H m NonTerminating H2)).
  destruct (frame_property _ _ _ _ _ H0 H1) as [_n [nf [? [? ?]]]].
  destruct _n' as [| | n'].
  + inversion H5; subst.
    revert H6; apply SAFE.
  + inversion H5; subst.
    - revert H6; apply SAFE.
    - revert H6; apply TERM.
  + rewrite FlatSemantics.sat_sepcon.
    inversion H5; subst.
    - exfalso; revert H6; apply SAFE.
    - rename x into n.
      exists n, nf.
      split; [| split]; auto.
      * apply (H m _ H2 H6).
      * eapply sat_mono; eauto.
Qed.

End soundness.
