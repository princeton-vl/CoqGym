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

Module StrongSemantics.

Definition sepcon {worlds: Type} {R: Relation worlds} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => exists m0 m1 m2, m0 <= m /\ join m1 m2 m0 /\ X m1 /\ Y m2.

Definition wand {worlds: Type} {R: Relation worlds} {J: Join worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall m0 m1 m2, m <= m0 -> join m0 m1 m2 -> X m1 -> Y m2.

Definition emp {worlds: Type} {R: Relation worlds} {J: Join worlds}: Ensemble worlds := increasing'.

Lemma sepcon_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (sepcon X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  destruct H2 as [n0 [n1 [n2 [? [? [? ?]]]]]].
  exists n0, n1, n2; split; [| split; [| split]]; auto.
  etransitivity; eauto.
Qed.

Lemma wand_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (wand X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros ? ? ? ?; apply H2.
  etransitivity; eauto.
Qed.

Lemma emp_closed
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}:
  upwards_closed_Kdenote emp.
Proof.
  intros.
  hnf; intros.
  hnf in H0 |- *.
  intros ? ?; apply H0.
  etransitivity; eauto.
Qed.

End StrongSemantics.

Module StrongSemanticsMono.

Program Definition sepcon
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  StrongSemantics.sepcon X Y.
Next Obligation.
  apply (@StrongSemantics.sepcon_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.

Program Definition wand
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}
      (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  StrongSemantics.wand X Y.
Next Obligation.
  apply (@StrongSemantics.wand_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.

Program Definition emp
      {worlds: Type}
      {R: Relation worlds}
      {po_R: PreOrder Krelation}
      {J: Join worlds}: MonoEnsemble worlds :=
  StrongSemantics.emp.
Next Obligation.
  apply (@StrongSemantics.emp_closed worlds R po_R J);
  apply (proj2_sig _).
Defined.

End StrongSemanticsMono.
