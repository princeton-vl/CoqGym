Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.Lindenbaum_Kripke.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.
Require Import Logic.MinimunLogic.Syntax.
Require Import Logic.MinimunLogic.ProofTheory.Minimun.
Require Import Logic.MinimunLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.

Section Lindenbaum_Kripke.

Context {L: Language}
        {minL: MinimunLanguage L}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {fwSC: FiniteWitnessedSequentCalculus L Gamma}.

Lemma Lindenbaum_preserves_cannot_derive: forall x, Lindenbaum_preserves (cannot_derive x).
Proof.
  intros.
  apply Lindenbaum_preserves_by_finiteness.
  - apply cannot_derive_finite_captured.
  - apply cannot_derive_subset_preserved.
Qed.

Lemma Lindenbaum_cannot_derive_ensures_derivable_closed: forall x, Lindenbaum_ensures (cannot_derive x) derivable_closed.
Proof.
  intros.
  apply Lindenbaum_for_derivable_closed.
  - apply Lindenbaum_preserves_cannot_derive.
  - apply cannot_derive_derivable_subset_preserved.
Qed.

End Lindenbaum_Kripke.
