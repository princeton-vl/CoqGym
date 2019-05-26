Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Trivial.
Require Import Logic.ModalLogic.Syntax.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.ModalLogic.Semantics.Kripke.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.

Section Sound_Kripke.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {mL: ModalLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {tminSM: TrivialMinimunSemantics L MD SM}
        {tpSM: TrivialPropositionalSemantics L MD SM}
        {kmSM: KripkeModalSemantics L MD M SM}.

Lemma sound_axiom_K:
  forall x y (m: Kworlds M),
    KRIPKE: M, m |= boxp (x --> y) --> (boxp x --> boxp y).
Proof.
  intros.
  rewrite !sat_impp, !sat_boxp.
  intros.
  specialize (H _ H1).
  specialize (H0 _ H1).
  rewrite sat_impp in H.
  auto.
Qed.

Lemma sound_rule_N:
  forall x,
    (forall (m: Kworlds M), KRIPKE: M, m |= x) ->
    (forall (m: Kworlds M), KRIPKE: M, m |= boxp x).
Proof.
  intros.
  rewrite sat_boxp.
  intros; apply H; auto.
Qed.

Lemma sound_boxp_orp {pf_R: PartialFunctional KM.Krelation}:
  forall x y (m: Kworlds M),
    KRIPKE: M, m |= boxp (x || y) <--> (boxp x || boxp y).
Proof.
  intros.
  unfold iffp.
  rewrite sat_andp, !sat_impp, !sat_orp, !sat_boxp.
  split; intros.
  + apply NNPP.
    intro.
    apply not_or_and in H0; destruct H0.
    apply not_all_ex_not in H0; destruct H0 as [n1 ?].
    apply not_all_ex_not in H1; destruct H1 as [n2 ?].
    apply imply_to_and in H0; destruct H0.
    apply imply_to_and in H1; destruct H1.
    pose proof partial_functionality _ _ _ H0 H1.
    subst n2; clear H1.
    specialize (H _ H0).
    rewrite sat_orp in H.
    tauto.
  + rewrite sat_orp.
    destruct H; [left | right]; auto.
Qed.

End Sound_Kripke.
