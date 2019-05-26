Require Export TopologicalSpaces.
From ZornsLemma Require Export InverseImage.
Require Export Continuity.

Section StrongTopology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.
Variable Y:Type.
Variable f:forall a:A, point_set (X a) -> Y.

Definition strong_open (S:Ensemble Y) : Prop :=
  forall a:A, open (inverse_image (f a) S).

Definition StrongTopology : TopologicalSpace.
refine (Build_TopologicalSpace Y strong_open _ _ _).
intros.
red; intro.
assert (inverse_image (f a) (FamilyUnion F) =
  IndexedUnion (fun U:{ U:Ensemble Y | In F U } =>
                 inverse_image (f a) (proj1_sig U))).
apply Extensionality_Ensembles; red; split; red; intros.
destruct H0.
inversion H0.
exists (exist _ S H1).
constructor.
exact H2.

destruct H0.
destruct H0.
destruct a0 as [U].
constructor.
exists U; trivial.

rewrite H0.
apply open_indexed_union.
intros.
destruct a0 as [U].
simpl.
apply H; trivial.

intros.
red; intro.
rewrite inverse_image_intersection.
apply open_intersection2; (apply H || apply H0).

red; intro.
rewrite inverse_image_full.
apply open_full.
Defined.

Lemma strong_topology_makes_continuous_funcs:
  forall a:A, continuous (f a) (Y:=StrongTopology).
Proof.
intros.
red.
intros.
auto.
Qed.

Lemma strong_topology_strongest: forall (T':Ensemble Y->Prop)
  (H1:_) (H2:_) (H3:_),
  (forall a:A, continuous (f a)
          (Y:=Build_TopologicalSpace Y T' H1 H2 H3)) ->
  forall V:Ensemble Y, T' V -> strong_open V.
Proof.
intros.
unfold continuous in H.
simpl in H.
red; intros; apply H; trivial.
Qed.

End StrongTopology.

Arguments StrongTopology {A} {X} {Y}.
