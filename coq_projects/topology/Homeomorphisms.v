Require Export TopologicalSpaces.
Require Export Continuity.

Inductive homeomorphism {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y) : Prop :=
| intro_homeomorphism: forall g:point_set Y -> point_set X,
  continuous f -> continuous g ->
  (forall x:point_set X, g (f x) = x) ->
  (forall y:point_set Y, f (g y) = y) -> homeomorphism f.

Lemma homeomorphism_is_invertible: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  homeomorphism f -> invertible f.
Proof.
intros.
destruct H as [g].
exists g; trivial.
Qed.

Definition open_map {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y) : Prop :=
forall U:Ensemble (point_set X), open U -> open (Im U f).

Lemma homeomorphism_is_open_map: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  homeomorphism f -> open_map f.
Proof.
intros.
destruct H as [g].
red; intros.
assert (Im U f = inverse_image g U).
apply Extensionality_Ensembles; split; red; intros.
destruct H4.
rewrite H5.
constructor.
rewrite H1; trivial.
destruct H4.
exists (g x); trivial.
symmetry; apply H2.
rewrite H4; apply H0; trivial.
Qed.

Lemma invertible_open_map_is_homeomorphism: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  invertible f -> continuous f -> open_map f -> homeomorphism f.
Proof.
intros.
destruct H as [g].
exists g; trivial.
red; intros.
assert (inverse_image g V = Im V f).
apply Extensionality_Ensembles; split; red; intros.
destruct H4.
exists (g x); trivial.
symmetry; apply H2.
destruct H4.
constructor.
rewrite H5.
rewrite H; trivial.
rewrite H4; apply H1; trivial.
Qed.

Inductive homeomorphic (X Y:TopologicalSpace) : Prop :=
| intro_homeomorphic: forall f:point_set X -> point_set Y,
    homeomorphism f -> homeomorphic X Y.

Require Export Relation_Definitions.
From ZornsLemma Require Import Relation_Definitions_Implicit.

Lemma homeomorphic_equiv: equivalence homeomorphic.
Proof.
constructor.
red; intros X.
exists (fun x:point_set X => x).
exists (fun x:point_set X => x); trivial;
  apply continuous_identity.

red; intros X Y Z ? ?.
destruct H as [f [finv]].
destruct H0 as [g [ginv]].
exists (fun x:point_set X => g (f x)).
exists (fun z:point_set Z => finv (ginv z)); (congruence ||
  apply continuous_composition; trivial).

red; intros X Y ?.
destruct H as [f [finv]].
exists finv; exists f; trivial.
Qed.
