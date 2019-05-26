Require Export TopologicalSpaces.

Definition clopen {X:TopologicalSpace} (S:Ensemble (point_set X))
  : Prop :=
  open S /\ closed S.

Definition connected (X:TopologicalSpace) : Prop :=
  forall S:Ensemble (point_set X), clopen S ->
        S = Empty_set \/ S = Full_set.

Require Export Continuity.

Lemma connected_img: forall {X Y:TopologicalSpace}
  (f:point_set X -> point_set Y),
  connected X -> continuous f -> surjective f -> connected Y.
Proof.
intros.
red; intros.
destruct (H (inverse_image f S)).
split.
apply H0.
apply H2.
red.
rewrite <- inverse_image_complement.
apply H0.
apply H2.

left.
apply Extensionality_Ensembles; split; red; intros.
destruct (H1 x).
assert (In Empty_set x0).
rewrite <- H3.
constructor.
rewrite H5.
trivial.
destruct H6.
destruct H4.

right.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct (H1 x).
rewrite <- H5.
assert (In (inverse_image f S) x0).
rewrite H3; constructor.
destruct H6; trivial.
Qed.

Require Export SubspaceTopology.

Lemma connected_union: forall {X:TopologicalSpace}
  {A:Type} (S:IndexedFamily A (point_set X)),
  (forall a:A, connected (SubspaceTopology (S a))) ->
  Inhabited (IndexedIntersection S) ->
  IndexedUnion S = Full_set -> connected X.
Proof.
intros.
pose (inc := fun (a:A) => subspace_inc (S a)).
destruct H0.
destruct H0.
red; intros.
assert (forall a:A, clopen (inverse_image (inc a) S0)).
intro.
split.
apply subspace_inc_continuous.
apply H2.
red.
rewrite <- inverse_image_complement.
apply subspace_inc_continuous.
apply H2.
destruct (classic (In S0 x)).
right.
assert (forall a:A, inverse_image (inc a) S0 = Full_set).
intro.
destruct (H a _ (H3 a)).
assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
  (exist _ x (H0 a))).
rewrite <- H5.
constructor.
simpl.
trivial.
destruct H6.
trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
assert (In (IndexedUnion S) x0).
rewrite H1; constructor.
destruct H7.
assert (In (@Full_set (point_set (SubspaceTopology (S a))))
  (exist _ x0 H7)).
constructor.
rewrite <- H5 in H8.
destruct H8.
simpl in H8.
trivial.

left.
assert (forall a:A, inverse_image (inc a) S0 = Empty_set).
intros.
destruct (H a _ (H3 a)).
trivial.
assert (In (@Full_set (point_set (SubspaceTopology (S a))))
  (exist _ x (H0 a))).
constructor.
rewrite <- H5 in H6.
destruct H6.
simpl in H6.
contradiction H4.

apply Extensionality_Ensembles; split; red; intros.
assert (In (IndexedUnion S) x0).
rewrite H1; constructor.
destruct H7.
assert (In (@Empty_set (point_set (SubspaceTopology (S a))))
  (exist _ x0 H7)).
rewrite <- H5.
constructor.
simpl.
trivial.
destruct H8.
destruct H6.
Qed.
