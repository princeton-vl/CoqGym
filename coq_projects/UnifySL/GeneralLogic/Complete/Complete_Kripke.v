Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.KripkeModel.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.Complete.Lindenbaum.
Require Import Logic.GeneralLogic.Complete.ContextProperty.
Require Import Logic.GeneralLogic.Complete.ContextProperty_Kripke.

Local Open Scope logic_base.
Local Open Scope kripke_model.
Import KripkeModelFamilyNotation.
Import KripkeModelNotation_Intuitionistic.

Section Completeness.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}
        {MD: Model}
        {kMD: KripkeModel MD}
        {M: Kmodel}
        {R: Relation (Kworlds M)}
        {SM: Semantics L MD}
        {kMC: Kmodel -> Prop}.

Context (cP: context -> Prop)
        (rel: bijection (Kworlds M) (sig cP)).

Hypothesis LIN_CD: forall x: expr, Lindenbaum_constructable (cannot_derive x) cP.
Hypothesis TRUTH: forall x: expr, forall m Phi, rel m Phi -> (KRIPKE: M, m |= x <-> proj1_sig Phi x).
Hypothesis CANON: kMC M.

Lemma general_completeness: strongly_complete Gamma SM (KripkeModelClass _ kMC).
Proof.
  intros.
  assert (forall Phi x, ~ Phi |-- x -> ~ consequence (KripkeModelClass _ kMC) Phi x).
  Focus 2. {
    hnf; intros.
    apply Classical_Prop.NNPP; intro; revert H0.
    apply H; auto.
  } Unfocus.

  intros.
  destruct (LIN_CD x _ H) as [Psi [? ?]].
  destruct (su_bij _ _ rel Psi) as [n HH].
  specialize (fun x => TRUTH x _ _ HH); clear HH.
  assert ((forall x, Phi x -> KRIPKE: M, n |= x) /\ ~ KRIPKE: M, n |= x).
  Focus 2. {
    intro.
    specialize (H3 (KRIPKE: M, n) ltac:(constructor; apply CANON)).
    tauto.
  } Unfocus.

  split.
  + intros.
    rewrite TRUTH.
    apply H0; auto.
  + rewrite TRUTH.
    intro; apply H1; clear H1.
    apply derivable_assum; auto.
Qed.

End Completeness.
