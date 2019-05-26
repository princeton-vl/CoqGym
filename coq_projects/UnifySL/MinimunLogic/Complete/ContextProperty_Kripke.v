Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}.

Lemma can_derive_finite_witnessed: forall x,
  finite_witnessed (can_derive x).
Proof.
  intros; hnf; intros.
  apply derivable_finite_witnessed; auto.
Qed.

Lemma cannot_derive_finite_captured: forall x,
  finite_captured (cannot_derive x).
Proof.
  intros.
  apply (not_finite_witnessed_finite_captured _ (can_derive_finite_witnessed x)).
Qed.

End ContextProperty.
