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

Section partial_soundness.

Existing Instance unit_kMD.
Import Partial.

Context {P: ProgrammingLanguage}
        {iP: ImperativeProgrammingLanguage P}
        {MD: Model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {BSS: BigStepSemantics P model}
        {iBSS: ImpBigStepSemantics P model BSS}.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {kminSM: KripkeMinimunSemantics L MD tt SM} {kpSM: KripkePropositionalSemantics L MD tt SM}.

Lemma hoare_seq_partial_sound: forall c1 c2 P1 P2 P3,
  triple_partial_valid P1 c1 P2 ->
  triple_partial_valid P2 c2 P3 ->
  triple_partial_valid P1 (Ssequence c1 c2) P3.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Ssequence in H2.
  destruct H2 as [ms' [ms'' [? [? ?]]]].
  specialize (H s ms' H1 H2).
  destruct ms' as [| | s'].
  + inversion H.
  + inversion H3; subst ms''; clear H3.
    inversion H4; auto.
  + inversion H3; subst.
    - apply lift_relation_forward in H4.
      subst ms; auto.
    - eapply sat_mono in H; [| exact H6].
      clear H2 H6 H3 s'; rename y into s'.
      apply (H0 s' ms); auto.
      inversion H4; auto.
Qed.

Lemma hoare_if_partial_sound: forall b c1 c2 B P1 P2,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_partial_valid (P1 && B) c1 P2 ->
  triple_partial_valid (P1 && ~~ B) c2 P2 ->
  triple_partial_valid P1 (Sifthenelse b c1 c2) P2.
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Sifthenelse in H3.
  destruct H3 as [[? [s' [? ?]]] | [? [s' [? ?]]]].
  + assert (KRIPKE: s |= P1 && B) by (rewrite sat_andp; firstorder).
    inversion H4; subst.
    - apply lift_relation_forward in H5; subst; auto.
    - eapply sat_mono in H6; [| eassumption].
      inversion H5; subst.
      apply (H0 y); auto.
  + assert (KRIPKE: s |= P1 && ~~ B).
    Focus 1. {
      rewrite sat_andp; split; auto.
      unfold negp; rewrite sat_impp.
      intros.
      rewrite H in H7.
      pose proof eval_bool_stable b _ _ H6.
      simpl in H7, H8.
      rewrite <- H8 in H7; exfalso; auto.
    } Unfocus.
    inversion H4; subst.
    - apply lift_relation_forward in H5; subst; auto.
    - eapply sat_mono in H6; [| eassumption].
      inversion H5; subst.
      apply (H1 y); auto.
Qed.

Lemma hoare_while_partial_sound: forall b c B P,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_partial_valid (P && B) c P ->
  triple_partial_valid P (Swhile b c) (P && ~~ B).
Proof.
  intros.
  unfold triple_partial_valid in *.
  intros s ms ? ?.
  apply access_Swhile in H2.
  inversion H2; subst; clear H2; auto.

  induction H3.
  + inversion H3.
    - subst.
      auto.
    - subst.
      eapply sat_mono; [eassumption |].
      rewrite sat_andp.
      split; auto.
      unfold negp.
      rewrite sat_impp; intros.
      rewrite H in H6.
      pose proof eval_bool_stable b _ _ H4.
      simpl in H6, H7.
      tauto.
  + assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
    inversion H3.
    - subst.
      apply lift_relation_forward in H4; subst.
      auto.
    - subst.
      eapply sat_mono in H6; [| eassumption].
      inversion H4; subst.
      specialize (H0 _ _ H6 H9).
      destruct H5; subst; auto.
  + apply IHloop_access_fin; clear IHloop_access_fin H6.
    assert (KRIPKE: s1 |= P0 && B) by (rewrite sat_andp; firstorder).
    eapply sat_mono in H6; [| eassumption].
    eapply sat_mono; [eassumption |].
    exact (H0 _ _ H6 H4).
  + destruct H3.
    subst; auto.
Qed.

End partial_soundness.

Section total_soundness.

Existing Instance unit_kMD.
Import Total.

Context {P: ProgrammingLanguage}
        {iP: ImperativeProgrammingLanguage P}
        {MD: Model}
        {R: Relation model}
        {po_R: PreOrder Krelation}
        {BSS: BigStepSemantics P model}
        {iBSS: ImpBigStepSemantics P model BSS}.

Context {L: Language} {minL: MinimunLanguage L} {pL: PropositionalLanguage L} {SL: SeparationLanguage L} {SM: Semantics L MD} {kiSM: KripkeIntuitionisticSemantics L MD tt SM} {kminSM: KripkeMinimunSemantics L MD tt SM} {kpSM: KripkePropositionalSemantics L MD tt SM}.


Lemma hoare_seq_total_sound: forall c1 c2 P1 P2 P3,
  triple_total_valid P1 c1 P2 ->
  triple_total_valid P2 c2 P3 ->
  triple_total_valid P1 (Ssequence c1 c2) P3.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Ssequence in H2.
  destruct H2 as [ms' [ms'' [? [? ?]]]].
  specialize (H s ms' H1 H2).
  destruct ms' as [| | s'].
  + inversion H.
  + inversion H.
  + inversion H3; subst.
    eapply sat_mono in H; [| exact H6].
    clear H2 H6 H3 s'; rename y into s'.
    apply (H0 s' ms); auto.
    inversion H4; auto.
Qed.

Lemma hoare_if_total_sound: forall b c1 c2 B P1 P2,
  (forall s, s |= B <-> eval_bool s b) ->
  triple_total_valid (P1 && B) c1 P2 ->
  triple_total_valid (P1 && ~~ B) c2 P2 ->
  triple_total_valid P1 (Sifthenelse b c1 c2) P2.
Proof.
  intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Sifthenelse in H3.
  destruct H3; destruct H3 as [? [s' [? ?]]].
  + assert (KRIPKE: s |= P1 && B) by (rewrite sat_andp; firstorder).
    inversion H4; subst.
    inversion H5; subst.
    eapply sat_mono in H6; [| eassumption].
    apply (H0 y); auto.
  + assert (KRIPKE: s |= P1 && ~~ B).
    Focus 1. {
      rewrite sat_andp; split; auto.
      unfold negp; rewrite sat_impp.
      intros.
      rewrite H in H7.
      pose proof eval_bool_stable b _ _ H6.
      simpl in H7, H8.
      tauto.
    } Unfocus.
    inversion H4; subst.
    inversion H5; subst.
    eapply sat_mono in H6; [| eassumption].
    apply (H1 y); auto.
Qed.

Lemma hoare_while_total_sound:
  forall {A: Type} (R: A -> A -> Prop) (Wf: well_founded R) (EQ LE: A -> expr) (D: model -> A),
    (forall s v, s |= EQ v <-> D s = v) ->
    (forall s v, s |= LE v <-> R (D s) v) ->
    (forall s1 s2, s1 <= s2 -> D s1 = D s2) ->
    forall b c B P,
     (forall s, s |= B <-> eval_bool s b) ->
     (forall v, triple_total_valid (P && B && EQ v) c (P && LE v)) ->
     triple_total_valid P (Swhile b c) (P && ~~ B).
Proof.
  intros ? ? WF ? ? ? H_EQ H_LE H_F; intros.
  unfold triple_total_valid in *.
  intros s ms ? ?.
  apply access_Swhile in H2.
  inversion H2; subst; clear H2; auto.

  Focus 1. {
  induction H3.
  + inversion H3; subst.
    eapply sat_mono; [eassumption |].
    rewrite sat_andp.
    split; auto.
    unfold negp.
    rewrite sat_impp; intros.
    rewrite H in H6.
    pose proof eval_bool_stable b _ _ H4.
    simpl in H6, H7.
    tauto.
  + inversion H3; subst.
    inversion H4; subst.
    assert (KRIPKE: s1 |= P0 && B && EQ (D y)).
    - rewrite !sat_andp.
      rewrite H_EQ, H, <- (H_F _ _ H7).
      simpl; tauto.
    - eapply sat_mono in H6; [| eassumption].
      specialize (H0 _ _ _ H6 H8).
      destruct H5; subst; auto.
  + apply IHloop_access_fin; clear IHloop_access_fin H6.
    assert (KRIPKE: s1 |= P0 && B && EQ (D s2)).
    - rewrite !sat_andp.
      rewrite H_EQ, H, <- (H_F _ _ H3).
      simpl; tauto.
    - eapply sat_mono in H6; [| eassumption].
      eapply sat_mono; [eassumption |].
      specialize (H0 _ _ _ H6 H4).
      rewrite sat_andp in H0.
      tauto.
  } Unfocus.
  Focus 1. {
    destruct H3; subst.
    inversion H2; subst; clear H2.
    specialize (WF (D (s1 0))).
    set (n := 0) in WF, H1; clearbody n.
    remember (D (s1 n)) as D0 eqn:?H.
    revert n H1 H2.
    induction WF.

    intros.
    subst x.
    assert (KRIPKE: s1 n |= P0 && B && EQ (D (s1 n))).
    - rewrite !sat_andp.
      rewrite H_EQ, H.
      specialize (H3 n).
      simpl; tauto.
    - eapply sat_mono in H8; [| apply H4].
      specialize (H0 _ _ _ H8 (H5 _)).
      eapply sat_mono in H0; [| apply H6].
      rewrite sat_andp in H0; destruct H0.
      rewrite H_LE in H9; simpl in H9.
      exact (H2 _ H9 (S n) H0 eq_refl).
  } Unfocus.
Qed.

End total_soundness.
