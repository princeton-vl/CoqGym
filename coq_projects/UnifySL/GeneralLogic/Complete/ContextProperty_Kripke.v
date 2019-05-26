Require Import Logic.lib.EnsemblesProperties.
Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Local Open Scope logic_base.

Section ContextProperty.

Context {L: Language}
        {Gamma: ProofTheory L}
        {bSC: BasicSequentCalculus L Gamma}.

Lemma Included_derivable: forall (Phi: context),
  Included _ Phi (derivable Phi).
Proof.
  intros; hnf; intros.
  apply derivable_assum; auto.
Qed.

Lemma derivable_mono: forall (Phi Psi: context),
  Included _ Phi Psi ->
  Included _ (derivable Phi) (derivable Psi).
Proof.
  intros.
  hnf; intros.
  eapply deduction_weaken; eauto.
Qed.

Lemma derivable_derivable: forall (Phi: context),
  Included _ (derivable (derivable Phi)) (derivable Phi).
Proof.
  intros.
  hnf; unfold Ensembles.In; intros.
  eapply derivable_trans with (derivable Phi); auto.
Qed.

Lemma derivable_derivable_Same_set: forall (Phi: context),
  Same_set _ (derivable (derivable Phi)) (derivable Phi).
Proof.
  intros; split.
  + apply derivable_derivable.
  + apply Included_derivable.
Qed.

End ContextProperty.

Section CanonicalProperties.

Context {L: Language}
        {Gamma: ProofTheory L}.

Definition derivable_closed : context -> Prop :=
  fun Phi => forall x, derivable Phi x -> Phi x.

Definition derivable_superset_preserved (P: context -> Prop): Prop :=
  forall Phi Psi, Included _ (derivable Phi) (derivable Psi) -> P Phi -> P Psi.

Definition derivable_subset_preserved (P: context -> Prop): Prop :=
  forall Phi Psi, Included _ (derivable Phi) (derivable Psi) -> P Psi -> P Phi.

Lemma not_derivable_superset_preserved_derivable_subset_preserved: forall P,
  derivable_superset_preserved P ->
  derivable_subset_preserved (fun X => ~ P X).
Proof.
  intros.
  hnf; intros.
  intro; apply H1; clear H1.
  eapply H; [| exact H2].
  auto.
Qed.

Context {bSC: BasicSequentCalculus L Gamma}.

Lemma derivable_subset_preserved_subset_preserved: forall P,
  derivable_subset_preserved P ->
  subset_preserved P.
Proof.
  intros.
  hnf in H |- *.
  intros ? ? ?; apply H.
  intros ? ?.
  eapply deduction_weaken; eauto.
Qed.

Lemma derivable_superset_preserved_superset_preserved: forall P,
  derivable_superset_preserved P ->
  superset_preserved P.
Proof.
  intros.
  hnf in H |- *.
  intros ? ? ?; apply H.
  intros ? ?.
  eapply deduction_weaken; eauto.
Qed.

Lemma derivable_closed_element_derivable: forall (Phi: context),
  derivable_closed Phi ->
  (forall x: expr, Phi x <-> Phi |-- x).
Proof.
  intros.
  split; intros; auto.
  apply derivable_assum; auto.
Qed.

End CanonicalProperties.

Section ContextProperties.

Context {L: Language}
        {Gamma: ProofTheory L}.

Definition can_derive (x: expr): context -> Prop :=
  fun Phi => Phi |-- x.

Definition cannot_derive (x: expr): context -> Prop :=
  fun Phi => ~ Phi |-- x.

Lemma can_derive_derivable_superset_preserved: forall x,
  derivable_superset_preserved (can_derive x).
Proof.
  intros.
  unfold can_derive.
  hnf; intros.
  apply H; auto.
Qed.

Lemma cannot_derive_derivable_subset_preserved: forall x,
  derivable_subset_preserved (cannot_derive x).
Proof.
  intros.
  apply (not_derivable_superset_preserved_derivable_subset_preserved _ (can_derive_derivable_superset_preserved x)).
Qed.

Context {bSC: BasicSequentCalculus L Gamma}.

Lemma can_derive_superset_preserved: forall x,
  superset_preserved (can_derive x).
Proof.
  intros.
  unfold can_derive.
  hnf; intros.
  eapply deduction_weaken; eauto.
Qed.

Lemma cannot_derive_subset_preserved: forall x,
  subset_preserved (cannot_derive x).
Proof.
  intros.
  apply (not_superset_preserved_subset_preserved _ (can_derive_superset_preserved x)).
Qed.

End ContextProperties.
