Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.GeneralLogic.Base.

Local Open Scope logic_base.

Section PropertiesOfSequentCalculus.

Context (L: Language)
        (Gamma: ProofTheory L).

Definition DerivableRefl: Prop :=
  forall x: expr, empty_context;; x |-- x.

Definition DeductionWeaken: Prop :=
  forall (Phi Psi: context) (x: expr), Included _ Phi Psi -> Phi |-- x -> Psi |-- x.

Definition DerivableAssu: Prop :=
  forall (Phi: context) (x: expr), Ensembles.In _ Phi x -> Phi |-- x.

Definition DeductionSubst1: Prop :=
  forall (Phi: context) (x y: expr), Phi |-- x -> Phi;; x |-- y -> Phi |-- y.

Definition DeductionSubst: Prop :=
  forall (Phi Psi: context) (y: expr), (forall x, Psi x -> Phi |-- x) -> Union _ Phi Psi |-- y -> Phi |-- y.

Definition DerivableFiniteWitnessed: Prop :=
  forall (Phi: context) (y: expr), Phi |-- y -> exists xs, Forall Phi xs /\ (fun x => In x xs) |-- y.

Definition ContextualDerivableFiniteWitnessed: Prop :=
  forall (Phi Psi: context) (y: expr), Union _ Phi Psi |-- y -> exists xs, Forall Psi xs /\ Union _ Phi (fun x => In x xs) |-- y.

End PropertiesOfSequentCalculus.

Section TheoryOfSequentCalculus.

Context {L: Language}
        {Gamma: ProofTheory L}.

Lemma DeductionWeaken_DerivableFiniteWitnessed_2_ContextualDerivableFiniteWitnessed:
  DeductionWeaken L Gamma ->
  DerivableFiniteWitnessed L Gamma ->
  ContextualDerivableFiniteWitnessed L Gamma.
Proof.
  intros.
  hnf; intros.
  apply H0 in H1; clear H0.
  destruct H1 as [xs [? ?]].
  assert (exists xs', (forall x, In x xs -> Phi x \/ In x xs') /\ forall x, In x xs' -> Psi x).
  + clear H1.
    induction H0.
    - exists nil.
      split; simpl; intros; tauto.
    - destruct IHForall as [xs' [? ?]].
      rewrite Union_spec in H0; destruct H0; [exists xs' | exists (x :: xs')]; split; intros.
      * destruct H4; [subst; auto |].
        apply H2; auto.
      * apply H3; auto.
      * destruct H4; [simpl; auto |].
        apply H2 in H4.
        simpl; tauto.
      * destruct H4; [subst; auto |].
        apply H3; auto.
  + destruct H2 as [xs' [? ?]].
    exists xs'.
    split.
    - rewrite Forall_forall; auto.
    - eapply H; eauto.
      unfold Included, Ensembles.In; intro; rewrite Union_spec; auto.
Qed.

Lemma DeductionWeaken_ContextualDerivableFiniteWitnessed_2_DerivableFiniteWitnessed:
  DeductionWeaken L Gamma ->
  ContextualDerivableFiniteWitnessed L Gamma ->
  DerivableFiniteWitnessed L Gamma.
Proof.
  intros.
  hnf; intros.
  eapply H in H1; [| rewrite <- (Union_Empty_left Phi); apply Included_refl].
  apply H0 in H1; clear H0.
  destruct H1 as [xs [? ?]]; exists xs; split; auto.
  eapply H in H1; [| rewrite Union_Empty_left; apply Included_refl].
  auto.
Qed.

Lemma DeductionSubst_2_DeductionSubst1:
  DeductionSubst L Gamma ->
  DeductionSubst1 L Gamma.
Proof.
  intros.
  hnf; intros.
  apply H with (Singleton _ x); auto.
  intros.
  inversion H2; subst.
  auto.
Qed.

Lemma DeductionWeaken_ContextualDerivableFiniteWitnessed_DeductionSubst1_2_DeductionSubst:
  DeductionWeaken L Gamma ->
  ContextualDerivableFiniteWitnessed L Gamma ->
  DeductionSubst1 L Gamma ->
  DeductionSubst L Gamma.
Proof.
  intros; hnf; intros.
  apply H0 in H3.
  destruct H3 as [xs [? ?]].
  eapply Forall_impl in H3; [| exact H2]; clear H2.
  induction H3.
  + eapply H; eauto.
    unfold Included, Ensembles.In; intro; rewrite Union_spec; simpl; tauto.
  + apply IHForall.
    apply H1 with x.
    - eapply H; eauto.
      unfold Included, Ensembles.In; intro; rewrite Union_spec; simpl; tauto.
    - eapply H; eauto.
      unfold Included, Ensembles.In; intro; rewrite !Union_spec; simpl.
      intros [? | [? | ?]]; auto.
      right; subst; constructor.
Qed.

Lemma DerivableRefl_DeductionWeaken_2_DerivableAssu:
  DerivableRefl L Gamma ->
  DeductionWeaken L Gamma ->
  DerivableAssu L Gamma.
Proof.
  intros.
  intros ? ? ?.
  eapply H0; [| apply H].
  intros ? ?.
  destruct H2.
  + destruct H2.
  + destruct H2; auto.
Qed.

Lemma DerivableAssu_2_DerivableRefl:
  DerivableAssu L Gamma ->
  DerivableRefl L Gamma.
Proof.
  intros.
  intros ?.
  apply H.
  right.
  constructor.
Qed.

End TheoryOfSequentCalculus.
