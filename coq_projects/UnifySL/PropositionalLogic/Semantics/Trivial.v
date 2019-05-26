Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.Semantics.Trivial.
Require Import Logic.PropositionalLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Module Semantics.

Definition andp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m /\ Y m.

Definition orp {model: Type} (X: Ensemble model) (Y: Ensemble model): Ensemble model :=
  fun m => X m \/ Y m.

Definition falsep {model: Type}: Ensemble model := fun m => False.

End Semantics.

Class TrivialPropositionalSemantics (L: Language) {minL: MinimunLanguage L} {pL: PropositionalLanguage L} (MD: Model) (SM: Semantics L MD): Type := {
  denote_andp: forall x y, Same_set _ (denotation (x && y)) (Semantics.andp (denotation x) (denotation y));
  denote_orp: forall x y, Same_set _ (denotation (x || y)) (Semantics.orp (denotation x) (denotation y));
  denote_falsep: Same_set _ (denotation FF) Semantics.falsep
}.

Section Trivial.

Context {L: Language}
        {minL: MinimunLanguage L}
        {pL: PropositionalLanguage L}
        {MD: Model}
        {SM: Semantics L MD}
        {tpSM: TrivialPropositionalSemantics L MD SM}.

Lemma sat_andp: forall m x y, m |= x && y <-> (m |= x /\ m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_andp x y).
  split; auto; [apply H | apply H0].
Qed.

Lemma sat_orp: forall m x y, m |= x || y <-> (m |= x \/ m |= y).
Proof.
  intros; simpl.
  unfold satisfies.
  destruct (denote_orp x y).
  split; auto; [apply H | apply H0].
Qed.

Lemma sat_falsep: forall m, m |= FF <-> False.
Proof.
  intros; simpl.
  unfold satisfies.
  destruct denote_falsep.
  split; auto; [apply H | apply H0].
Qed.

End Trivial.
