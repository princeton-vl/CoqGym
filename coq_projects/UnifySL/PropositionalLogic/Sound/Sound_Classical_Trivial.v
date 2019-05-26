Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Section Sound.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {MD: Model}
        {SM: Semantics L MD}
        {tminSM: TrivialMinimunSemantics L MD SM}
        {tpSM: TrivialPropositionalSemantics L MD SM}.

Lemma sound_andp_intros:
  forall x y m,
    m |= x --> y --> x && y.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  simpl; intros ? ?.
  auto.
Qed.

Lemma sound_andp_elim1:
  forall x y m,
    m |= x && y --> x.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  intros [? ?].
  auto.
Qed.

Lemma sound_andp_elim2:
  forall x y m,
    m |= x && y --> y.
Proof.
  intros.
  rewrite !sat_impp, sat_andp.
  intros [? ?].
  auto.
Qed.

Lemma sound_orp_intros1:
  forall x y m,
    m |= x --> x || y.
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  auto.
Qed.

Lemma sound_orp_intros2:
  forall x y m,
      m |= y --> x || y.
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  auto.
Qed.

Lemma sound_orp_elim:
  forall x y z m,
    m |= (x --> z) --> (y --> z) --> (x || y --> z).
Proof.
  intros.
  rewrite !sat_impp, sat_orp.
  tauto.
Qed.

Lemma sound_falsep_elim:
  forall x m,
    m |= FF --> x.
Proof.
  intros.
  rewrite sat_impp, sat_falsep.
  intros [].
Qed.

Lemma sound_excluded_middle:
  forall x m,
    m |= x || (x --> FF).
Proof.
  intros.
  rewrite sat_orp, sat_impp, sat_falsep.
  tauto.
Qed.

End Sound.
