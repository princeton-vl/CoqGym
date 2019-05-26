Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Sets.Ensembles.
Require Export Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import Logic.lib.Bijection.
Require Import Logic.lib.Countable.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.lib.EnsemblesProperties.

Section Lindenbaum.

Context {A: Type}
        (CA: Countable A)
        (init: Ensemble A)
        (P: Ensemble A -> Prop).

Fixpoint LindenbaumChain (n: nat): Ensemble A :=
  match n with
  | 0 => init
  | S n => fun a => LindenbaumChain n a \/ CA a n /\ P (Union _ (LindenbaumChain n) (Singleton _ a))
  end.

Definition LindenbaumConstruction: Ensemble A :=
  fun a => exists n, LindenbaumChain n a.

Lemma Lindenbaum_included_n_m: forall n m,
  n <= m ->
  Included _ (LindenbaumChain n) (LindenbaumChain m).
Proof.
  intros.
  induction H.
  + exact (fun x H => H).
  + refine (fun x H => _ (IHle x H)).
    clear.
    unfold Ensembles.In; intros; simpl.
    left.
    auto.
Qed.

Lemma Lindenbaum_included_n_omega: forall n,
  Included _ (LindenbaumChain n) LindenbaumConstruction.
Proof.
  intros.
  intros ? ?.
  exists n; auto.
Qed.

Lemma Lindenbaum_included:
  Included _ init LindenbaumConstruction.
Proof.
  apply (Lindenbaum_included_n_omega 0).
Qed.

Lemma Lindenbaum_pointwise_finite_decided: forall a n,
  CA a n ->
  (LindenbaumChain (S n) a) <-> (LindenbaumConstruction a).
Proof.
  intros.
  split; [apply (Lindenbaum_included_n_omega (S n)) | intros].
  destruct H0 as [m ?].
  destruct (le_dec m (S n)); [revert H0; apply Lindenbaum_included_n_m; auto |].
  assert (S n <= m) by omega; clear n0.
  induction H1; auto.
  apply IHle; clear IHle.
  simpl in H0.
  destruct H0; auto.
  destruct H0 as [? _]; exfalso.
  pose proof pf_inj _ _ CA a _ _ H H0.
  omega.
Qed.

Lemma Lindenbaum_finite_witness:
  forall xs, Forall LindenbaumConstruction xs ->
    exists n, Forall (LindenbaumChain n) xs.
Proof.
  intros.
  induction H.
  + exists 0.
    constructor.
  + destruct IHForall as [n ?H].
    destruct (im_inj _ _ CA x) as [m ?].
    exists (max n (S m)).
    constructor.
    - erewrite <- Lindenbaum_pointwise_finite_decided in H by eauto.
      revert H; apply (Lindenbaum_included_n_m (S m)).
      apply Max.le_max_r.
    - revert H1.
      apply Forall_impl; intro.
      apply Lindenbaum_included_n_m.
      apply Max.le_max_l.
Qed.

Hypothesis H_init: P init.

Lemma Lindenbaum_preserve_n:
  Proper (Same_set A ==> iff) P ->
  forall n, P (LindenbaumChain n).
Proof.
  intros P_Proper n.
  induction n; auto.
  simpl.
  destruct (classic (exists a, CA a n /\ P (Union A (LindenbaumChain n) (Singleton A a)))).
  + destruct H as [a [? ?]].
    eapply P_Proper; [| exact H0].
    rewrite Same_set_spec.
    intros a0.
    rewrite Union_spec, Singleton_spec.
    assert (CA a0 n -> a = a0).
    {
      intros.
      apply (in_inj _ _ CA a a0 n); auto.
    }
    assert (a = a0 -> P (Union A (LindenbaumChain n) (Singleton A a0))).
    {
      intros.
      subst; auto.
    }
    assert (a = a0 -> CA a0 n).
    {
      intros.
      subst; auto.
    }
    tauto.
  + eapply P_Proper; [| exact IHn].
    rewrite Same_set_spec.
    intros a0.
    firstorder.
Qed.

Lemma Lindenbaum_preserve_omega:
  finite_captured P ->
  subset_preserved P ->
  P LindenbaumConstruction.
Proof.
  intros.
  apply H.
  intros.
  apply Lindenbaum_finite_witness in H1.
  destruct H1 as [n ?].
  rewrite Forall_forall in H1.
  eapply H0; [exact H1 |].
  apply Lindenbaum_preserve_n, subset_preserved_same_set_preserved; auto.
Qed.

Lemma Lindenbaum_pointwise_finite_decided': forall a n,
  CA a n ->
  Proper (Same_set A ==> iff) P ->
  P (Union _ (LindenbaumChain n) (Singleton _ a)) <-> (LindenbaumConstruction a).
Proof.
  intros.
  rewrite <- Lindenbaum_pointwise_finite_decided by eauto.
  simpl.
  split; intros; auto.
  destruct H1 as [? | [? ?]]; auto.
  eapply H0; [| apply (Lindenbaum_preserve_n H0 n)].
  rewrite Same_set_spec; intros a0.
  rewrite Union_spec.
  split; intros; [| auto].
  destruct H2; auto.
  inversion H2; subst.
  auto.
Qed.

End Lindenbaum.

Definition Lindenbaum_preserves {A: Type} (P: Ensemble A -> Prop): Prop :=
  forall (CA: Countable A) init, P init -> P (LindenbaumConstruction CA init P).

Definition Lindenbaum_ensures {A: Type} (P cP: Ensemble A -> Prop): Prop :=
  forall (CA: Countable A) init, P init -> cP (LindenbaumConstruction CA init P).

Definition Lindenbaum_constructable {A: Type} (P cP: Ensemble A -> Prop): Prop :=
  forall Phi, P Phi -> exists Psi: sig cP, Included _ Phi (proj1_sig Psi) /\ P (proj1_sig Psi).

Lemma Lindenbaum_constructable_Same_set {A: Type}: forall P Q cP: Ensemble A -> Prop,
  Same_set _ P Q ->
  (Lindenbaum_constructable P cP <-> Lindenbaum_constructable Q cP).
Proof.
  intros.
  pose proof H.
  rewrite Same_set_spec in H.
  apply Morphisms_Prop.all_iff_morphism.
  intros Phi.
  apply Morphisms_Prop.iff_iff_iff_impl_morphism_obligation_1; auto.
  apply Morphisms_Prop.ex_iff_morphism.
  intros [Psi ?H].
  apply Morphisms_Prop.and_iff_morphism; [tauto |].
  auto.
Qed.

Lemma Lindenbaum_constructable_suffice {A: Type} (P cP: Ensemble A -> Prop):
  Countable A ->
  Lindenbaum_preserves P ->
  Lindenbaum_ensures P cP ->
  Lindenbaum_constructable P cP.
Proof.
  intros.
  hnf; intros.
  specialize (H X _ H1).
  specialize (H0 X _ H1).
  exists (exist _ _ H0).
  split; auto.
  apply Lindenbaum_included.
Qed.

Lemma Lindenbaum_preserves_by_finiteness {A: Type}: forall P: Ensemble A -> Prop,
  finite_captured P ->
  subset_preserved P ->
  Lindenbaum_preserves P.
Proof.
  intros.
  hnf; intros.
  apply Lindenbaum_preserve_omega; auto.
Qed.

Lemma Lindenbaum_ensures_by_conjunct {A: Type}: forall P cP1 cP2: Ensemble A -> Prop,
  Lindenbaum_ensures P cP1 ->
  Lindenbaum_ensures P cP2 ->
  Lindenbaum_ensures P (Intersection _ cP1 cP2).
Proof.
  intros.
  hnf.
  intros.
  rewrite Intersection_spec; auto.
Qed.

