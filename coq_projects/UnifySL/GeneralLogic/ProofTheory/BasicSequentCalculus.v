Require Import Logic.lib.Coqlib.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.

Local Open Scope logic_base.

Class NormalSequentCalculus (L: Language) (Gamma: ProofTheory L): Type := {
  provable_derivable: forall x, provable x <-> derivable empty_context x
}.

Class BasicSequentCalculus (L: Language) (Gamma: ProofTheory L) := {
  deduction_weaken: forall Phi Psi x, Included _ Phi Psi -> Phi |-- x -> Psi |-- x;
  derivable_assum: forall Phi x, Ensembles.In _ Phi x -> Phi |-- x;
  deduction_subst: forall (Phi Psi: context) y, (forall x, Psi x -> Phi |-- x) -> Union _ Phi Psi |-- y -> Phi |-- y
}.

Class FiniteWitnessedSequentCalculus (L: Language) (Gamma: ProofTheory L) := {
  derivable_finite_witnessed: forall (Phi: context) (y: expr), Phi |-- y -> exists xs, Forall Phi xs /\ (fun x => In x xs) |-- y
}.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Lemma deduction_subst1: forall Phi x y, Phi |-- x -> Phi;; x |-- y -> Phi |-- y.
Proof.
  intros.
  apply deduction_subst with (Singleton _ x); auto.
  intros.
  inversion H1; subst.
  auto.
Qed.

Lemma derivable_trans: forall (Phi Psi: context) y, (forall x, Psi x -> Phi |-- x) -> Psi |-- y -> Phi |-- y.
Proof.
  intros.
  eapply deduction_subst; eauto.
  eapply deduction_weaken; eauto.
  apply right_Included_Union.
Qed.

Lemma deduction_weaken1: forall Phi x y,
  Phi |-- y ->
  Phi;; x |-- y.
Proof.
  intros.
  eapply deduction_weaken; eauto.
  intros ? ?; left; auto.
Qed.

Lemma derivable_assum1: forall (Phi: context) (x: expr), Phi;; x |-- x.
Proof.
  intros.
  apply derivable_assum.
  right; constructor.
Qed.

Lemma contextual_derivable_finite_witnessed {fwSC: FiniteWitnessedSequentCalculus L Gamma}: forall (Phi Psi: context) (y: expr), Union _ Phi Psi |-- y -> exists xs, Forall Psi xs /\ Union _ Phi (fun x => In x xs) |-- y.
Proof.
  apply DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed.
  + hnf; intros; eapply deduction_weaken; eauto.
  + hnf; intros; eapply derivable_finite_witnessed; eauto.
Qed.

Lemma deduction_weaken0 {SC: NormalSequentCalculus L Gamma}: forall Phi y,
  |-- y ->
  Phi |-- y.
Proof.
  intros.
  rewrite provable_derivable in H.
  eapply deduction_weaken; eauto.
  intros ? [].
Qed.

End DerivableRulesFromSequentCalculus.

Ltac solve_assum :=
  (first [apply derivable_assum1 | assumption | apply deduction_weaken1; solve_assum] || fail 1000 "Cannot find the conclusion in assumption").

