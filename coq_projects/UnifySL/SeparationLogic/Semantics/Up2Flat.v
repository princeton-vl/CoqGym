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
Require Import Logic.SeparationLogic.Model.DownwardsClosure.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.Semantics.StrongSemantics.
Require Import Logic.SeparationLogic.Semantics.UpwardsSemantics.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.
Import KripkeModelFamilyNotation.

Module Up2Flat.
Section Up2Flat.

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
        {uSA: UpwardsClosedSeparationAlgebra (Kworlds M)}
        {SM: Semantics L MD}
        {kiSM: KripkeIntuitionisticSemantics L MD M SM}
        {usSM: UpwardsSemantics.SeparatingSemantics L MD M SM}.

Definition fsSM: @FlatSemantics.SeparatingSemantics L sL MD kMD M _ (DownwardsClosure_J) SM.
Proof.
  constructor.
  + (* sat_sepcon *)
    intros.
    unfold WeakSemantics.sepcon.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (UpwardsSemantics.denote_sepcon _ _) m) in H.
      destruct H as [m1 [m2 [? [? ?]]]].
      exists m1, m2.
      split; [| split]; auto.
      exists m1, m2.
      split; [| split]; auto; reflexivity.
    - rewrite (app_same_set (UpwardsSemantics.denote_sepcon _ _) m).
      destruct H as [m1 [m2 [[n1 [n2 [? [? ?]]]] [? ?]]]].
      exists n1, n2.
      split; [| split]; auto; eapply sat_mono; eauto.
  + (* sat_wand *)
    intros.
    unfold WeakSemantics.wand.
    split; unfold Included, Ensembles.In; intros m ?.
    - rewrite (app_same_set (UpwardsSemantics.denote_wand _ _) m) in H.
      intros.
      destruct H0 as [m' [m1' [? [? ?]]]].
      apply (H  _ _ _ H0 H3).
      eapply sat_mono; eauto.
    - rewrite (app_same_set (UpwardsSemantics.denote_wand _ _) m).
      hnf; intros.
      apply (H m1 m2); auto.
      exists m0, m1.
      split; [| split]; auto.
      reflexivity.
Qed.

Definition feSM {s'L: SeparationEmpLanguage L} {USA': UnitalSeparationAlgebra' (Kworlds M)} {ueSM: UpwardsSemantics.EmpSemantics L MD M SM}: @FlatSemantics.EmpSemantics L _ _ MD _ M _ (DownwardsClosure_J) SM.
Proof.
  constructor;
  intros m; simpl; unfold Ensembles.In; unfold WeakSemantics.emp;
  rewrite <- DownwardsClosure_increasing;
  apply UpwardsSemantics.denote_emp.
Qed.

End Up2Flat.
End Up2Flat.
