Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Sound_Kripke.

Context {L: Language}
        {minL: MinimunLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {kminSM: KripkeMinimunSemantics L MD M SM}.

Lemma sound_modus_ponens:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= (x --> y) -> KRIPKE: M, m |= x -> KRIPKE: M, m |= y.
Proof.
  intros.
  rewrite sat_impp in H.
  specialize (H m).
  apply H; auto.
  reflexivity.
Qed.

Lemma sound_axiom1:
  forall x y: expr,
    forall m,
      KRIPKE: M, m |= x --> y --> x.
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  eapply sat_mono; eauto.
Qed.

Lemma sound_axiom2:
  forall x y z: expr,
    forall m,
      KRIPKE: M, m |= (x --> y --> z) --> (x --> y) --> (x --> z).
Proof.
  intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  rewrite sat_impp; intros.
  assert (n <= n1) by (etransitivity; eauto).

  rewrite sat_impp in H0.
  specialize (H0 n1 H5 H4).
  rewrite sat_impp in H2.
  specialize (H2 n1 H3 H4).

  rewrite sat_impp in H0.
  specialize (H0 n1 ltac:(reflexivity) H2).
  auto.
Qed.

End Sound_Kripke.
