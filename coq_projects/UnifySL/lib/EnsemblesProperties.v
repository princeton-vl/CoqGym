Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Logic.lib.Ensembles_ext.

Section Properties.

Context {A: Type}.

Definition finite_captured (P: Ensemble A -> Prop): Prop :=
  forall (Phi: Ensemble A),
    (forall xs: list A, Forall Phi xs -> P (fun x => In x xs)) ->
      P Phi.

Definition finite_witnessed (P: Ensemble A -> Prop): Prop :=
  forall (Phi: Ensemble A), P Phi ->
    exists xs: list A, Forall Phi xs /\ P (fun x => In x xs).

Definition subset_preserved (P: Ensemble A -> Prop): Prop :=
  forall (Phi Psi: Ensemble A),
    Included _ Phi Psi -> P Psi -> P Phi.

Definition superset_preserved (P: Ensemble A -> Prop): Prop :=
  forall (Phi Psi: Ensemble A),
    Included _ Phi Psi -> P Phi -> P Psi.

Lemma not_finite_witnessed_finite_captured: forall P,
  finite_witnessed P ->
  finite_captured (fun X => ~ P X).
Proof.
  intros.
  hnf in H |- *.
  intros.
  intro.
  specialize (H Phi H1).
  firstorder.
Qed.

Lemma not_superset_preserved_subset_preserved: forall P,
  superset_preserved P ->
  subset_preserved (fun X => ~ P X).
Proof.
  intros.
  hnf in H |- *.
  firstorder.
Qed.

Lemma superset_preserved_same_set_preserved: forall P,
  superset_preserved P ->
  Proper (Same_set _ ==> iff) P.
Proof.
  intros.
  hnf; intros.
  rewrite Same_set_spec in H0.
  split; apply H.
  + unfold Included, Ensembles.In.
    hnf in H0.
    firstorder.
  + unfold Included, Ensembles.In.
    hnf in H0.
    firstorder.
Qed.

Lemma subset_preserved_same_set_preserved: forall P,
  subset_preserved P ->
  Proper (Same_set _ ==> iff) P.
Proof.
  intros.
  hnf; intros.
  rewrite Same_set_spec in H0.
  split; apply H.
  + unfold Included, Ensembles.In.
    hnf in H0.
    firstorder.
  + unfold Included, Ensembles.In.
    hnf in H0.
    firstorder.
Qed.

End Properties.
