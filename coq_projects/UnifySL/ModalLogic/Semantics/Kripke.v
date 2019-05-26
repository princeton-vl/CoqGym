Require Import Logic.GeneralLogic.Base.
Require Import Logic.ModalLogic.Model.KripkeModel.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.ModalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Local Open Scope kripke_model.
Import PropositionalLanguageNotation.
Import ModalLanguageNotation.
Import KripkeModelFamilyNotation.

Module Semantics.

Definition boxp {worlds: Type} {R: KM.Relation worlds} (X: Ensemble worlds): Ensemble worlds :=
  fun m => forall n, Krelation m n -> X n.

End Semantics.

Class KripkeModalSemantics (L: Language) {minL: MinimunLanguage L} {mL: ModalLanguage L} (MD: Model) {kMD: KripkeModel MD} (M: Kmodel) {R: Relation (Kworlds M)} (SM: Semantics L MD): Type := {
  denote_boxp: forall x: expr, Same_set _ (Kdenotation M (boxp x)) (Semantics.boxp (Kdenotation M x))
}.

Lemma sat_boxp {L: Language} {minL: MinimunLanguage L} {mL: ModalLanguage L} {MD: Model} {kMD: KripkeModel MD} {M: Kmodel} {R: Relation (Kworlds M)} {SM: Semantics L MD} {kmSM: KripkeModalSemantics L MD M SM}: forall m x, KRIPKE: M , m |= boxp x <-> (forall n, KM.Krelation m n -> KRIPKE: M , n |= x).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_boxp x).
  split; [apply H | apply H0].
Qed.

