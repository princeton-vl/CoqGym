Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimunLogic.Syntax.

Local Open Scope logic_base.
Local Open Scope syntax.

Section PropertiesOfSequentCalculus.

Context (L: Language)
        (Gamma: ProofTheory L)
        {minL: MinimunLanguage L}.

Definition DeductionMP: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x -> Phi |-- x --> y -> Phi |-- y.

Definition DeductionImpIntro: Prop :=
  forall (Phi: context) (x y: expr), Phi;; x |-- y -> Phi |-- x --> y.

Definition DeductionImpElim: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x --> y -> Phi;; x |-- y.

End PropertiesOfSequentCalculus.

Section TheoryOfSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}
        {minL: MinimunLanguage L}.

Lemma DeductionMP_DerivableAssu_DeductionWeaken_2_DeductionImpElim:
  DeductionMP L Gamma ->
  DerivableAssu L Gamma ->
  DeductionWeaken L Gamma ->
  DeductionImpElim L Gamma.
Proof.
  intros.
  intros ? ? ? ?.
  eapply H.
  + apply H0.
    right.
    constructor.
  + eapply H1; [| exact H2].
    intros ? ?.
    left.
    auto.
Qed.

Lemma DeductionImpIntro_DeductionMP_2_DeductionSubst1:
  DeductionImpIntro L Gamma ->
  DeductionMP L Gamma ->
  DeductionSubst1 L Gamma.
Proof.
  intros.
  intros ? ? ? ? ?.
  apply H in H2.
  revert H1 H2; apply H0.
Qed.

Lemma DeductionImpElim_DeductionSubst1_2_DeductionMP:
  DeductionImpElim L Gamma ->
  DeductionSubst1 L Gamma ->
  DeductionMP L Gamma.
Proof.
  intros.
  intros ? ? ? ? ?.
  apply H in H2.
  revert H1 H2; apply H0.
Qed.

End TheoryOfSequentCalculus.
