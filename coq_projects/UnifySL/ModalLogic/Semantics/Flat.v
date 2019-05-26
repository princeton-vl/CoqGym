Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.ModalLogic.Model.OrderedKripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Semantics.

Definition boxp {worlds: Type} {R: KM.Relation worlds} (X: Ensemble worlds): Ensemble worlds :=
  fun m => forall n, KM.Krelation m n -> X n.

Lemma boxp_closed
      {worlds: Type}
      {R1: KI.Relation worlds}
      {po_R1: PreOrder KI.Krelation}
      {R2: KM.Relation worlds}
      {ukmM: UpwardsClosedOrderedKripkeModel worlds}:
  forall (X: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote (boxp X).
Proof.
  intros.
  hnf.
  intros m1 m2 ? ?.
  hnf in H1 |- *.
  intros n2 ?.
  destruct (KM_relation_up _ _ _ H0 H2) as [n1 [? ?]].
  apply (H n1); auto.
Qed.

End Semantics.

Module SemanticsMono.

Program Definition boxp
      {worlds: Type}
      {R1: KI.Relation worlds}
      {po_R1: PreOrder KI.Krelation}
      {R2: KM.Relation worlds}
      {ukmM: UpwardsClosedOrderedKripkeModel worlds}
      (X: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.boxp X.
Next Obligation.
  apply (@Semantics.boxp_closed worlds R1 po_R1 R2 ukmM);
  apply (proj2_sig _).
Defined.

End SemanticsMono.

Class FlatModalSemantics (L: Language) {minL: MinimunLanguage L} {mL: ModalLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} (SM: Semantics L MD) : Type := {
  denote_boxp: forall x, Same_set _ (Kdenotation M (boxp x)) (Semantics.boxp (Kdenotation M x))
}.

Lemma sat_boxp {L: Language} {minL: MinimunLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R1: KI.Relation (Kworlds M)} {R2: KM.Relation (Kworlds M)} {SM: Semantics L MD} {fmSM: FlatModalSemantics L MD M SM}: forall m x, KRIPKE: M , m |= boxp x <-> (forall n, KM.Krelation m n -> KRIPKE: M , n |= x).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_boxp x).
  split; [apply H | apply H0].
Qed.

