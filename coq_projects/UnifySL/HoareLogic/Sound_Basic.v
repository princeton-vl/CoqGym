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
        {BSS: BigStepSemantics P model}.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {sL: SeparationLanguage L} {SM: Semantics L MD} {R: Relation model} {po_R: PreOrder Krelation} {kiSM: KripkeIntuitionisticSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {kminSM: KripkeMinimunSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM} {kpSM: KripkePropositionalSemantics L MD (tt: @Kmodel MD (unit_kMD _)) SM}.

Lemma hoare_consequence_partial_sound: forall c P1 P2 Q1 Q2,
  valid (AllModel _) (P2 --> P1) ->
  valid (AllModel _) (Q1 --> Q2) ->
  triple_partial_valid P1 c Q1 ->
  triple_partial_valid P2 c Q2.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  specialize (H1 s ms).
  specialize (H (KRIPKE: s) I).
  rewrite sat_impp in H.
  apply (H s) in H2; [| reflexivity].
  specialize (H1 H2 H3); clear H2 H3.
  destruct ms as [| | s']; auto.
  specialize (H0 (KRIPKE: s') I).
  rewrite sat_impp in H0.
  apply (H0 s'); auto.
  reflexivity.
Qed.

Lemma hoare_consequence_total_sound: forall c P1 P2 Q1 Q2,
  valid (AllModel _) (P2 --> P1) ->
  valid (AllModel _) (Q1 --> Q2) ->
  triple_total_valid P1 c Q1 ->
  triple_total_valid P2 c Q2.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  specialize (H1 s ms).
  specialize (H (KRIPKE: s) I).
  rewrite sat_impp in H.
  apply (H s) in H2; [| reflexivity].
  specialize (H1 H2 H3); clear H2 H3.
  destruct ms as [| | s']; auto.
  specialize (H0 (KRIPKE: s') I).
  rewrite sat_impp in H0.
  apply (H0 s'); auto.
  reflexivity.
Qed.

Lemma hoare_conjunction_partial_sound: forall c P1 P2 Q1 Q2,
    triple_partial_valid P1 c Q1 ->
    triple_partial_valid P2 c Q2 ->
    triple_partial_valid (P1 && P2) c (Q1 && Q2).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros.
  specialize (H s_pre ms_post).
  specialize (H0 s_pre ms_post).
  rewrite sat_andp in H1. destruct H1.
  apply H in H1; auto.
  apply H0 in H3; auto.
  destruct ms_post; auto.
  apply sat_andp. split; assumption.
Qed.

Lemma hoare_conjuntion_total_sound: forall c P1 P2 Q1 Q2,
    triple_total_valid P1 c Q1 ->
    triple_total_valid P2 c Q2 ->
    triple_total_valid (P1 && P2) c (Q1 && Q2).
Proof.
  intros.
  unfold triple_total_valid in *.
  intros.
  specialize (H s_pre ms_post).
  specialize (H0 s_pre ms_post).
  apply sat_andp in H1. destruct H1.
  apply H in H1; auto.
  apply H0 in H3; auto.
  destruct ms_post; auto.
  apply sat_andp. split; assumption.
Qed.

Lemma hoare_disjunction_parial_sound: forall c P1 P2 Q1 Q2,
    triple_partial_valid P1 c Q1 ->
    triple_partial_valid P2 c Q2 ->
    triple_partial_valid (P1 || P2) c (Q1 || Q2).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros.
  specialize (H s_pre ms_post).
  specialize (H0 s_pre ms_post).
  rewrite sat_orp in H1. destruct H1.
  - apply H in H1; auto.
    destruct ms_post; auto.
    apply sat_orp. left. assumption.
  - apply H0 in H1; auto.
    destruct ms_post; auto.
    apply sat_orp. right. assumption.
Qed.

Lemma hoare_disjunction_total_sound: forall c P1 P2 Q1 Q2,
    triple_total_valid P1 c Q1 ->
    triple_total_valid P2 c Q2 ->
    triple_total_valid (P1 || P2) c (Q1 || Q2).
Proof.
  intros.
  unfold triple_total_valid in *.
  intros.
  specialize (H s_pre ms_post).
  specialize (H0 s_pre ms_post).
  rewrite sat_orp in H1. destruct H1.
  - apply H in H1; auto.
    destruct ms_post; auto.
    rewrite sat_orp. left. assumption.
  - apply H0 in H1; auto.
    destruct ms_post; auto.
    rewrite sat_orp. right. assumption.
Qed.

End soundness.
