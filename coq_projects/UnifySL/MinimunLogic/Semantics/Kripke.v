Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Module Semantics.

Definition impp {worlds: Type} {R: Relation worlds} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => forall n, m <= n -> X n -> Y n.

Lemma impp_closed {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (impp X Y).
Proof.
  intros.
  hnf; intros.
  hnf in H2 |- *.
  intros ? ?; apply H2.
  etransitivity; eauto.
Qed.

End Semantics.

Module SemanticsMono.

Program Definition impp {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.impp X Y.
Next Obligation.
  apply (@Semantics.impp_closed worlds R po_R);
  apply (proj2_sig _).
Defined.

End SemanticsMono.

Class KripkeMinimunSemantics (L: Language) {minL: MinimunLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD) : Type := {
  denote_impp: forall x y, Same_set _ (Kdenotation M (x --> y)) (Semantics.impp (Kdenotation M x) (Kdenotation M y))
}.

Lemma sat_impp {L: Language} {minL: MinimunLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {kminSM: KripkeMinimunSemantics L MD M SM}: forall m x y, KRIPKE: M , m |= x --> y <-> (forall n, m <= n -> KRIPKE: M , n |= x -> KRIPKE: M , n |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_impp x y).
  split; [apply H | apply H0].
Qed.

