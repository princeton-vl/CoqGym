Require Export TopologicalSpaces.
Require Export Neighborhoods.
From ZornsLemma Require Export InverseImage.
Require Export OpenBases.
Require Export NeighborhoodBases.
Require Export Subbases.

Section continuity.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.

Definition continuous : Prop :=
  forall V:Ensemble (point_set Y), open V ->
  open (inverse_image f V).

Definition continuous_at (x:point_set X) : Prop :=
  forall V:Ensemble (point_set Y),
  neighborhood V (f x) -> neighborhood (inverse_image f V) x.

Lemma continuous_at_open_neighborhoods:
  forall x:point_set X,
  (forall V:Ensemble (point_set Y),
  open_neighborhood V (f x) -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H0 as [V' [? ?]].
pose proof (H V' H0).
destruct H2 as [U' [? ?]].
exists U'; split; trivial.
apply (inverse_image_increasing f) in H1; auto with sets.
Qed.

Lemma pointwise_continuity :
  (forall x:point_set X, continuous_at x) -> continuous.
Proof.
intros.
red; intros.
assert (interior (inverse_image f V) = inverse_image f V).
apply Extensionality_Ensembles; split.
apply interior_deflationary.
red; intros.
destruct H1.
assert (neighborhood V (f x)).
exists V; repeat split; auto with sets.
pose proof (H x V H2).
destruct H3 as [U].
destruct H3.
destruct H3.
assert (Included U (interior (inverse_image f V))).
apply interior_maximal; trivial.
auto.

rewrite <- H1; apply interior_open.
Qed.

Lemma continuous_func_continuous_everywhere:
  continuous -> forall x:point_set X, continuous_at x.
Proof.
intros.
apply continuous_at_open_neighborhoods.
intros.
apply open_neighborhood_is_neighborhood.
destruct H0; split; try constructor; auto.
Qed.

Lemma continuous_at_neighborhood_basis:
  forall (x:point_set X) (NB:Family (point_set Y)),
  neighborhood_basis NB (f x) ->
  (forall V:Ensemble (point_set Y),
  In NB V -> neighborhood (inverse_image f V) x) ->
  continuous_at x.
Proof.
intros.
red; intros.
destruct H.
apply neighborhood_basis_cond in H1.
destruct H1 as [N [? ?]].
pose proof (H0 N H).
destruct H2 as [U [? ?]].
exists U; split; trivial.
assert (Included (inverse_image f N) (inverse_image f V));
  auto with sets.
Qed.

Lemma continuous_open_basis:
  forall (B:Family (point_set Y)), open_basis B ->
  (forall V:Ensemble (point_set Y),
    In B V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply pointwise_continuity.
intro.
pose proof (open_basis_to_open_neighborhood_basis B (f x) H).
apply open_neighborhood_basis_is_neighborhood_basis in H1.
apply (continuous_at_neighborhood_basis _ _ H1).
intros.
destruct H2 as [[? ?]].
apply open_neighborhood_is_neighborhood.
split; try constructor; auto.
Qed.

Lemma continuous_subbasis:
  forall (SB:Family (point_set Y)), subbasis SB ->
  (forall V:Ensemble (point_set Y),
     In SB V -> open (inverse_image f V)) -> continuous.
Proof.
intros.
apply (continuous_open_basis _
  (finite_intersections_of_subbasis_form_open_basis _ _ H)).
intros.
destruct H1.
destruct H1 as [A [? [V' []]]].
rewrite H3.
assert (inverse_image f (IndexedIntersection V') =
  IndexedIntersection (fun a:A => inverse_image f (V' a))).
apply Extensionality_Ensembles; split; red; intros.
destruct H4.
inversion_clear H4.
constructor; intros.
constructor.
apply H5.
destruct H4.
constructor.
constructor; intros.
destruct (H4 a).
exact H5.

rewrite H4.
apply open_finite_indexed_intersection; trivial.
intros.
apply H0.
apply H2.
Qed.

End continuity.

Arguments continuous {X} {Y}.
Arguments continuous_at {X} {Y}.

Lemma continuous_composition_at: forall {X Y Z:TopologicalSpace}
  (f:point_set Y -> point_set Z) (g:point_set X -> point_set Y)
  (x:point_set X),
  continuous_at f (g x) -> continuous_at g x ->
  continuous_at (fun x:point_set X => f (g x)) x.
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_composition: forall {X Y Z:TopologicalSpace}
  (f:point_set Y -> point_set Z) (g:point_set X -> point_set Y),
  continuous f -> continuous g ->
  continuous (fun x:point_set X => f (g x)).
Proof.
intros.
red; intros.
rewrite inverse_image_composition.
auto.
Qed.

Lemma continuous_identity: forall (X:TopologicalSpace),
  continuous (fun x:point_set X => x).
Proof.
intros.
red; intros.
apply eq_ind with (1:=H).
apply Extensionality_Ensembles; split; red; intros.
constructor; trivial.
destruct H0; trivial.
Qed.

Lemma continuous_constant: forall (X Y:TopologicalSpace)
  (y0:point_set Y), continuous (fun x:point_set X => y0).
Proof.
intros.
pose (f := fun _:point_set X => y0).
fold f.
red; intros.
destruct (classic (In V y0)).
replace (inverse_image f V) with (@Full_set (point_set X)).
apply open_full.
apply Extensionality_Ensembles; split; red; intros.
constructor; trivial.
constructor.
replace (inverse_image f V) with (@Empty_set (point_set X)).
apply open_empty.
apply Extensionality_Ensembles; split; auto with sets;
  red; intros.
destruct H1.
contradiction H0.
Qed.

Lemma continuous_at_is_local: forall (X Y:TopologicalSpace)
  (x0:point_set X) (f g:point_set X -> point_set Y)
  (N:Ensemble (point_set X)),
  neighborhood N x0 -> (forall x:point_set X, In N x -> f x = g x) ->
  continuous_at f x0 -> continuous_at g x0.
Proof.
intros.
red; intros.
destruct H as [U1 [[]]].
rewrite <- H0 in H2.
apply H1 in H2.
destruct H2 as [U2 [[]]].
exists (Intersection U1 U2).
repeat split; trivial.
apply open_intersection2; trivial.
destruct H7.
rewrite <- H0.
apply H6 in H8.
destruct H8; trivial.
auto.
auto.
Qed.
