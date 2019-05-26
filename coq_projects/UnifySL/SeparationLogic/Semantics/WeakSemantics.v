Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sets.Ensembles.
Require Import Logic.lib.Coqlib.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.Model.OrderedSA.

Local Open Scope kripke_model.
Import KripkeModelNotation_Intuitionistic.

Module WeakSemantics.

Definition sepcon {worlds: Type} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => exists m1 m2, join m1 m2 m /\ X m1 /\ Y m2.

Definition wand {worlds: Type} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall m1 m2, join m m1 m2 -> X m1 -> Y m2.

Definition emp {worlds: Type} {R: Relation worlds} {J: Join worlds}: Ensemble worlds := increasing.

Lemma sepcon_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (sepcon X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  destruct H2 as [n1 [n2 [? [? ?]]]].
  destruct (join_Korder_up _ _ _ _ H2 H1) as [m1 [m2 [? [? ?]]]].
  exists m1, m2.
  split; [| split]; auto.
  + apply (H n1); auto.
  + apply (H0 n2); auto.
Qed.

Lemma wand_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (wand X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros.
  destruct (join_Korder_down _ _ _ _ _ H3 H1 ltac:(reflexivity)) as [m2' [? ?]].
  apply (H0 m2'); auto.
  apply (H2 m1); auto.
Qed.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  intros.
  destruct (join_Korder_down _ _ _ _ _ H1 H ltac:(reflexivity)) as [n'' [? ?]].
  etransitivity; eauto.
Qed.

End WeakSemantics.

Module WeakSemanticsMono.

Program Definition sepcon
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {uSA: UpwardsClosedSeparationAlgebra worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  WeakSemantics.sepcon X Y.
Next Obligation.
  apply (@WeakSemantics.sepcon_closed worlds R po_R J SA uSA);
  apply (proj2_sig _).
Defined.

Program Definition wand
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  WeakSemantics.wand X Y.
Next Obligation.
  apply (@WeakSemantics.wand_closed worlds R po_R J SA dSA);
  apply (proj2_sig _).
Defined.

Program Definition emp
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      {SA: SeparationAlgebra worlds}
      {dSA: DownwardsClosedSeparationAlgebra worlds}: MonoEnsemble worlds :=
  WeakSemantics.emp.
Next Obligation.
  apply (@WeakSemantics.emp_closed worlds R po_R J SA dSA);
  apply (proj2_sig _).
Defined.

End WeakSemanticsMono.
