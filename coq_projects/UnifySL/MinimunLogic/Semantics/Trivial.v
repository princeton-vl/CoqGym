Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Module Semantics.

Definition impp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m -> Y m.

End Semantics.

Class TrivialMinimunSemantics (L: Language) {minL: MinimunLanguage L} (MD: Model) (SM: Semantics L MD): Type := {
  denote_impp: forall x y, Same_set _ (denotation (x --> y)) (Semantics.impp (denotation x) (denotation y))
}.

Lemma sat_impp {L: Language} {minL: MinimunLanguage L} {MD: Model} {SM: Semantics L MD} {tminSM: TrivialMinimunSemantics L MD SM}: forall m x y, m |= x --> y <-> (m |= x -> m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_impp x y).
  split; auto; [apply H | apply H0].
Qed.

