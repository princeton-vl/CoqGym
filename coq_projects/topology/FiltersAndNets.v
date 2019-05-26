Require Export FilterLimits.
Require Export Nets.

Section net_tail_filter.

Variable X:TopologicalSpace.
Variable J:DirectedSet.
Variable x:Net J X.
Hypothesis J_nonempty: inhabited (DS_set J).

Definition net_tail (j:DS_set J) :=
  Im [ i:DS_set J | DS_ord j i ] x.

Definition tail_filter_basis : Family (point_set X) :=
  Im Full_set net_tail.

Definition tail_filter : Filter (point_set X).
refine (Build_Filter_from_basis tail_filter_basis _ _ _).
destruct J_nonempty as [j].
exists (net_tail j).
exists j; trivial.
constructor.
intro.
inversion H as [j].
assert (In Empty_set (x j)).
rewrite H1.
exists j; trivial.
constructor.
apply preord_refl; apply DS_ord_cond.
destruct H3.

intros.
destruct H.
destruct H0.
destruct (DS_join_cond x0 x1) as [k []].
exists (net_tail k); split.
exists k; trivial.
constructor.
red; intros.
constructor.
destruct H5 as [i0].
destruct H5.
rewrite H1.
exists i0; trivial.
constructor.
apply preord_trans with k; trivial.
apply DS_ord_cond.
destruct H5 as [i0].
destruct H5.
rewrite H2.
exists i0; trivial.
constructor.
apply preord_trans with k; trivial.
apply DS_ord_cond.
Defined.

Lemma net_limit_impl_tail_filter_limit: forall x0:point_set X,
  net_limit x x0 -> filter_limit tail_filter x0.
Proof.
intros.
red; intros.
red; intros U ?.
destruct H0.
destruct H0 as [V []].
destruct H0.
pose proof (H V H0 H2).
destruct H3 as [j0].
apply filter_upward_closed with (net_tail j0).
constructor.
exists (net_tail j0).
split.
exists j0; trivial.
constructor.
auto with sets.
intros y ?.
apply H1.
destruct H4 as [j].
rewrite H5.
apply H3.
destruct H4; assumption.
Qed.

Lemma tail_filter_limit_impl_net_limit: forall x0:point_set X,
  filter_limit tail_filter x0 -> net_limit x x0.
Proof.
intros.
intros U ? ?.
assert (In (filter_family tail_filter) U).
apply H.
constructor.
apply open_neighborhood_is_neighborhood.
split; trivial.
destruct H2.
destruct H2 as [T []].
destruct H2 as [j0].
exists j0.
intros.
apply H3.
rewrite H4.
exists j; trivial.
constructor; assumption.
Qed.

Lemma net_cluster_point_impl_tail_filter_cluster_point:
  forall x0:point_set X,
  net_cluster_point x x0 -> filter_cluster_point tail_filter x0.
Proof.
intros.
red; intros.
destruct H0.
destruct H0 as [T []].
destruct H0 as [j0].
apply meets_every_open_neighborhood_impl_closure.
intros.
pose proof (H U H3 H4).
destruct (H5 j0) as [j' []].
exists (x j').
constructor; trivial.
apply H1.
rewrite H2.
exists j'.
constructor; trivial.
reflexivity.
Qed.

Lemma tail_filter_cluster_point_impl_net_cluster_point:
  forall x0:point_set X,
  filter_cluster_point tail_filter x0 -> net_cluster_point x x0.
Proof.
intros.
red; intros.
red; intros.
assert (In (closure (net_tail i)) x0).
apply H.
constructor.
exists (net_tail i).
split.
exists i; trivial.
constructor.
auto with sets.
pose proof (closure_impl_meets_every_open_neighborhood _ _ _ H2
  U H0 H1).
destruct H3.
destruct H3.
destruct H3.
exists x1; split.
destruct H3; trivial.
rewrite <- H5; trivial.
Qed.

End net_tail_filter.

Arguments net_tail {X} {J}.
Arguments tail_filter {X} {J}.

Section filter_to_net.

Variable X:TopologicalSpace.
Variable F:Filter (point_set X).

Record filter_to_net_DS_set : Type := {
  ftn_S : Ensemble (point_set X);
  ftn_x : point_set X;
  ftn_S_in_F : In (filter_family F) ftn_S;
  ftn_x_in_S : In ftn_S ftn_x
}.

Definition filter_to_net_DS : DirectedSet.
refine (Build_DirectedSet filter_to_net_DS_set
  (fun x1 x2:filter_to_net_DS_set =>
     Included (ftn_S x2) (ftn_S x1)) _ _).
constructor.
red; intros.
auto with sets.
red; intros.
auto with sets.
intros.
destruct i.
destruct j.
assert (In (filter_family F) (Intersection ftn_S0 ftn_S1)).
apply filter_intersection; trivial.
assert (Inhabited (Intersection ftn_S0 ftn_S1)).
apply NNPP; red; intro.
assert (Intersection ftn_S0 ftn_S1 = Empty_set).
apply Extensionality_Ensembles; split; red; intros.
contradiction H0.
exists x; trivial.
destruct H1.
rewrite H1 in H.
contradiction (filter_empty _ F).
destruct H0 as [ftn_x'].
exists (Build_filter_to_net_DS_set
  (Intersection ftn_S0 ftn_S1) ftn_x' H H0).
simpl.
split; auto with sets.
Defined.

Definition filter_to_net : Net filter_to_net_DS X :=
  ftn_x.

Lemma filter_limit_impl_filter_to_net_limit: forall x0:point_set X,
  filter_limit F x0 -> net_limit filter_to_net x0.
Proof.
intros.
intros U ? ?.
assert (In (filter_family F) U).
apply H.
constructor.
apply open_neighborhood_is_neighborhood.
split; trivial.
exists (Build_filter_to_net_DS_set U x0 H2 H1).
destruct j.
simpl.
auto.
Qed.

Lemma filter_to_net_limit_impl_filter_limit: forall x0:point_set X,
  net_limit filter_to_net x0 -> filter_limit F x0.
Proof.
intros.
intros U ?.
destruct H0.
destruct H0 as [V []].
apply filter_upward_closed with V; trivial.
destruct H0.
destruct (H V H0 H2) as [[]].
apply filter_upward_closed with ftn_S0.
trivial.
red; intros.
pose proof (H3
  (Build_filter_to_net_DS_set ftn_S0 x ftn_S_in_F0 H4)).
simpl in H5.
apply H5; auto with sets.
Qed.

Lemma filter_cluster_point_impl_filter_to_net_cluster_point:
  forall x0:point_set X,
  filter_cluster_point F x0 -> net_cluster_point filter_to_net x0.
Proof.
intros.
red; intros.
red; intros.
destruct i.
pose proof (H ftn_S0 ftn_S_in_F0).
pose proof (closure_impl_meets_every_open_neighborhood _ _
  _ H2 U H0 H1).
destruct H3.
destruct H3.
exists (Build_filter_to_net_DS_set ftn_S0 x ftn_S_in_F0 H3).
simpl.
split; auto with sets.
Qed.

Lemma filter_to_net_cluster_point_impl_filter_cluster_point:
  forall x0:point_set X,
  net_cluster_point filter_to_net x0 -> filter_cluster_point F x0.
Proof.
intros.
red; intros.
apply meets_every_open_neighborhood_impl_closure; intros.
assert (Inhabited S).
apply NNPP; red; intro.
assert (S = Empty_set).
apply Extensionality_Ensembles; split; red; intros.
contradiction H3.
exists x; trivial.
destruct H4.
rewrite H4 in H0.
contradiction (filter_empty _ F).
destruct H3 as [y].
pose (j0 := Build_filter_to_net_DS_set S y H0 H3).
destruct (H U H1 H2 j0) as [j' []].
exists (filter_to_net j').
constructor; trivial.
destruct j'.
simpl.
simpl in H5.
simpl in H4.
auto.
Qed.

End filter_to_net.
