Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.Semantics.Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Kripke.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

(* TODO: It is so obvious that this file is very similar with Trivial.v. The should be merged. The obstacle is the way that we formalize Kripke Semantics. See the "TODO" in GeneralLogic/Semantics/Kripke.v *)
Module Semantics.

Definition andp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m /\ Y m.

Definition orp {worlds: Type} (X: Ensemble worlds) (Y: Ensemble worlds): Ensemble worlds :=
  fun m => X m \/ Y m.

Definition falsep {worlds: Type}: Ensemble worlds := fun m => False.

Lemma andp_closed {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (andp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2.
  split.
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma orp_closed {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation}:
  forall (X: Ensemble worlds) (Y: Ensemble worlds),
    upwards_closed_Kdenote X ->
    upwards_closed_Kdenote Y ->
    upwards_closed_Kdenote (orp X Y).
Proof.
  intros.
  hnf; intros.
  destruct H2; [left | right].
  + apply (H n); auto.
  + apply (H0 n); auto.
Qed.

Lemma falsep_closed {worlds: Type} {R: Relation worlds}:
  upwards_closed_Kdenote falsep.
Proof.
  intros.
  hnf; intros.
  inversion H0.
Qed.

End Semantics.

Module SemanticsMono.

Program Definition andp {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.andp X Y.
Next Obligation.
  apply (@Semantics.andp_closed worlds R po_R);
  apply (proj2_sig _).
Defined.

Program Definition orp {worlds: Type} {R: Relation worlds} {po_R: PreOrder Krelation} (X Y: MonoEnsemble worlds): MonoEnsemble worlds :=
  Semantics.orp X Y.
Next Obligation.
  apply (@Semantics.orp_closed worlds R po_R);
  apply (proj2_sig _).
Defined.

Program Definition falsep {worlds: Type} {R: Relation worlds}: MonoEnsemble worlds :=
  Semantics.falsep.
Next Obligation.
  apply (@Semantics.falsep_closed worlds R);
  apply (proj2_sig _).
Defined.

End SemanticsMono.

Class KripkePropositionalSemantics (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD) {kminSM: KripkeMinimunSemantics L MD M SM}: Type := {
  denote_andp: forall x y, Same_set _ (Kdenotation M (x && y)) (Semantics.andp (Kdenotation M x) (Kdenotation M y));
  denote_orp: forall x y, Same_set _ (Kdenotation M (x || y)) (Semantics.orp (Kdenotation M x) (Kdenotation M y));
  denote_falsep: Same_set _ (Kdenotation M FF) Semantics.falsep
}.

Section KripkeSemantics.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kminSM: KripkeMinimunSemantics L MD M SM}
        {kpSM: KripkePropositionalSemantics L MD M SM}.

Lemma sat_andp: forall m x y, KRIPKE: M , m |= x && y <-> (KRIPKE: M , m |= x /\ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_andp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_orp: forall m x y, KRIPKE: M , m |= x || y <-> (KRIPKE: M , m |= x \/ KRIPKE: M , m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_orp x y).
  split; [apply H | apply H0].
Qed.

Lemma sat_falsep: forall m, KRIPKE: M , m |= FF <-> False.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_falsep.
  split; [apply H | apply H0].
Qed.

End KripkeSemantics.
