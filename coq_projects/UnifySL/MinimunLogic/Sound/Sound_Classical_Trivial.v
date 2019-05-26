Require Import Coq.Logic.Classical_Prop.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.

Section Sound.

Context {L: Language}
        {minL: MinimunLanguage L}
        {MD: Model}
        {SM: Semantics L MD}
        {tminSM: TrivialMinimunSemantics L MD SM}.

Lemma sound_modus_ponens:
  forall x y m,
    m |= (x --> y) -> m |= x -> m |= y.
Proof.
  intros.
  rewrite sat_impp in H.
  apply H; auto.
Qed.

Lemma sound_axiom1:
  forall x y m,
    m |= x --> y --> x.
Proof.
  intros.
  rewrite !sat_impp.
  intros ? ?; auto.
Qed.

Lemma sound_axiom2:
  forall x y z m,
    m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite !sat_impp.
  intros ? ? ?.
  specialize (H H1).
  specialize (H0 H1).
  auto.
Qed.

End Sound.
