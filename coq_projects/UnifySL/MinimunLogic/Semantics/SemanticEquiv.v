Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Logic.MinimunLogic.Semantics.Kripke.
Require Logic.MinimunLogic.Semantics.Trivial.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section SemanticEquiv.

Context {L: Language}
        {minL: MinimunLanguage L}
        {MD: Model}
        {SM: Semantics L MD}.

Lemma eqR_KripkeIntuitionistic: @Kripke.KripkeIntuitionisticSemantics L MD (unit_kMD _) tt eq SM.
Proof.
  constructor.
  intros; hnf; intros.
  hnf in H; subst.
  auto.
Qed.

Lemma Trivial2Kripke {tpSM: Trivial.TrivialMinimunSemantics L MD SM}: 
  @Kripke.KripkeMinimunSemantics L minL MD (unit_kMD _) tt eq SM.
Proof.
  constructor.
  + intros.
    change (@Kdenotation L MD (unit_kMD _) tt SM) with denotation.
    rewrite Trivial.denote_impp.
    split; unfold Included, Ensembles.In; intros.
    - hnf; intros.
      hnf in H0; subst.
      apply H, H1.
    - hnf; intros; apply (H x0); auto.
      reflexivity.
Qed.

End SemanticEquiv.
