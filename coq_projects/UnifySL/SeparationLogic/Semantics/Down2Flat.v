Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.
Require Import Logic.SeparationLogic.Model.UpwardsClosure.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.
Require Import Logic.SeparationLogic.Semantics.DownwardsSemantics.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Down2Flat.
Section Down2Flat.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {sL: SeparationLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {po_R: PreOrder Krelation}
        {J: Join (Kworlds M)}
        {SA: SeparationAlgebra (Kworlds M)}
        {dSA: DownwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {dsSM: DownwardsSemantics.SeparatingSemantics L MD M SM}.

Definition fsSM: @FlatSemantics.SeparatingSemantics L _ MD _ M _ UpwardsClosure_J SM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    unfold WeakSemantics.sepcon.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (DownwardsSemantics.denote_sepcon _ _) m) in H.
      destruct H as [m0 [m1 [m2 [? [? [? ?]]]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m0; split; auto.
    - rewrite (app_same_set (DownwardsSemantics.denote_sepcon _ _) m).
      destruct H as [m1 [m2 [[n [? ?]] [? ?]]]].
      exists n, m1, m2.
      split; [| split; [| split]]; auto.
  + (* sat_wand *)
    intros.
    unfold WeakSemantics.wand.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (DownwardsSemantics.denote_wand _ _) m) in H.
      intros.
      destruct H0 as [m2' [? ?]].
      eapply sat_mono; eauto.
      eapply H; eauto.
    - rewrite (app_same_set (DownwardsSemantics.denote_wand _ _) m).
      hnf; intros.
      apply (H m1 m2); auto.
      exists m2; split; auto.
      reflexivity.
Qed.

Definition feSM {s'L: SeparationEmpLanguage L} {USA: UnitalSeparationAlgebra (Kworlds M)} {deSM: DownwardsSemantics.EmpSemantics L MD M SM}: @FlatSemantics.EmpSemantics L _ _ MD _ M _ UpwardsClosure_J SM.
Proof.
  split; intros m; unfold Ensembles.In; unfold WeakSemantics.emp;
  rewrite <- UpwardsClosure_increasing;
  apply DownwardsSemantics.denote_emp.
Qed.

End Down2Flat.
End Down2Flat.
