Require Export TopologicalSpaces.
Require Export OrderTopology.
Require Export Reals.

Definition RTop := OrderTopology Rle.

Require Export MetricSpaces.

Definition R_metric (x y:R) : R := Rabs (y-x).

Lemma R_metric_is_metric: metric R_metric.
Proof.
constructor.
intros.
unfold R_metric.
pose proof (Rabs_pos (y-x)).
auto with *.

intros.
unfold R_metric.
replace (y-x) with (-(x-y)); try ring.
apply Rabs_Ropp.

intros.
unfold R_metric.
replace (z-x) with ((y-x) + (z-y)); try ring.
apply Rabs_triang.

intros.
unfold R_metric.
replace (x-x) with 0; try ring.
exact Rabs_R0.

intros.
assert (y-x=0).
apply NNPP.
contradict H.
apply Rabs_no_R0; assumption.
auto with *.
Qed.

Lemma Rmetric_bound: forall x y z:R, R_metric x z < y - x ->
  z < y.
Proof.
intros.
replace z with (x + (z-x)); try ring.
apply Rle_lt_trans with (x + R_metric x z).
assert (z - x <= R_metric x z).
apply Rle_abs.
auto with real.
replace y with (x + (y-x)); try ring.
auto with real.
Qed.

Lemma Rmetric_bound2: forall x y z:R, R_metric y z < y - x ->
  x < z.
Proof.
intros.
replace z with (y + (z-y)); try ring.
apply Rlt_le_trans with (y - R_metric y z).
apply Rlt_minus in H.
apply Rminus_lt.
replace (x - (y - R_metric y z)) with
  (R_metric y z - (y - x)); try ring.
trivial.
assert (y - z <= R_metric y z).
rewrite (metric_sym _ _ R_metric_is_metric y z).
apply Rle_abs.
apply Rle_minus in H0.
apply Rminus_le.
replace (y - R_metric y z - (y + (z - y))) with
  (y - z - R_metric y z); trivial; ring.
Qed.

Lemma RTop_metrization: metrizes RTop R_metric.
Proof.
refine (let Hsubbasis := Build_TopologicalSpace_from_subbasis_subbasis
  _ (order_topology_subbasis _ Rle) in _).
clearbody Hsubbasis.
red; intros.
constructor.
intros.
destruct H.
assert (open_ball (point_set RTop) R_metric x r = Intersection
  [ y:R | x-r <= y /\ y <> x-r ]
  [ y:R | y <= x+r /\ y <> x+r ]).
apply Extensionality_Ensembles; split; red; intros.
destruct H0.
assert (x - r < x0).
apply Rmetric_bound2 with x.
ring_simplify; trivial.
assert (x + r > x0).
apply Rmetric_bound with x.
ring_simplify; trivial.
repeat split; auto with real.
constructor.
destruct H0.
destruct H0.
destruct H0.
destruct H1.
destruct H1.
apply Rabs_def1.
assert (x0-x <= r).
apply Rminus_le.
apply Rle_minus in H1.
replace (x0 - x - r) with (x0 - (x + r)); trivial; ring.
assert (x0 - x <> r).
intro.
contradiction H3.
rewrite <- H5.
ring.
destruct (total_order_T (x0 - x) r) as [[|]|]; try tauto.
assert (r < r).
apply Rlt_le_trans with (x0 - x); trivial.
contradict H6.
apply Rlt_irrefl.
assert (-r <= x0 - x).
apply Rle_minus in H0.
apply Rminus_le.
replace (-r - (x0 - x)) with (x - r - x0); try ring; trivial.
assert (-r <> x0 - x).
intro.
contradiction H2.
replace r with (- -r); try ring.
rewrite H5; ring.
destruct (total_order_T (-r) (x0 - x)) as [[|]|]; try tauto.
assert (-r < -r).
apply Rle_lt_trans with (x0 - x); trivial.
contradict H6.
apply Rlt_irrefl.

rewrite H0.
constructor.
apply (@open_intersection2 RTop).
apply Hsubbasis; constructor.
apply Hsubbasis; constructor.
assert (x-r < x).
apply Rminus_lt.
ring_simplify.
auto with real.
assert (x+r > x).
apply Rminus_gt.
ring_simplify; trivial.
repeat split; auto with real.

intros.
destruct H.
destruct H.
destruct H0.
pose proof (H _ H0).
assert (exists eps:R, eps > 0 /\ Included (open_ball _ R_metric x eps) S).
clear H0.
induction H2.
exists 1.
split.
red.
auto with real.
intro; constructor.
destruct H0.
destruct H1.
destruct H0.
exists (x0-x).
split.
destruct (total_order_T x0 x) as [[]|].
assert (x < x).
apply Rle_lt_trans with x0; trivial.
contradict H2.
apply Rlt_irrefl.
congruence.
apply Rgt_minus; trivial.
red; intros y ?.
destruct H2.
constructor.
assert (y < x0).
apply Rmetric_bound with x; trivial.
split; auto with real.

destruct H1.
destruct H0.
exists (x - x0).
split.
destruct (total_order_T x0 x) as [[]|].
apply Rgt_minus; trivial.
congruence.
assert (x < x).
apply Rlt_le_trans with x0; trivial.
contradict H2.
apply Rlt_irrefl.
intros y ?.
destruct H2.
constructor.
assert (x0 < y).
apply Rmetric_bound2 with x; trivial.
split; auto with real.
destruct H1.
apply IHfinite_intersections in H1.
apply IHfinite_intersections0 in H3.
destruct H1 as [eps1 []].
destruct H3 as [eps2 []].
exists (Rmin eps1 eps2).
split.
unfold Rmin.
destruct Rle_dec; trivial.
red; intros y ?.
destruct H6.
constructor.
apply H4.
constructor.
apply Rlt_le_trans with (Rmin eps1 eps2); trivial.
unfold Rmin; destruct Rle_dec; auto with real.
apply H5.
constructor.
apply Rlt_le_trans with (Rmin eps1 eps2); trivial.
unfold Rmin; destruct Rle_dec; auto with real.

destruct H3 as [eps []].
exists (open_ball R R_metric x eps).
split.
constructor.
trivial.
assert (Included S (FamilyUnion F)).
intros y ?.
exists S; trivial.
auto with sets.
Qed.

Corollary RTop_metrizable: metrizable RTop.
Proof.
exists R_metric.
exact R_metric_is_metric.
exact RTop_metrization.
Qed.

Lemma RTop_separable: separable RTop.
Proof.
Require Import RationalsInReals.
exists (Im Full_set Q2R).
apply countable_img.
apply countable_type_ensemble.
exact Q_countable.

apply meets_every_nonempty_open_impl_dense.
intros.
destruct H0 as [x].
destruct (RTop_metrization x).
destruct (open_neighborhood_basis_cond U) as [V []].
split; trivial.
destruct H1.
destruct (rationals_dense_in_reals (x-r) (x+r)) as [q].
apply Rminus_gt.
replace (x+r-(x-r)) with (r+r); try ring.
apply Rgt_trans with r; auto with real.
pattern r at 3.
replace r with (r+0); try ring.
auto with real.

exists (Q2R q).
constructor.
exists q; trivial.
constructor.
apply H2.
constructor.
destruct H3.
apply Rabs_def1.
apply Rminus_lt.
apply Rlt_minus in H4.
replace (Q2R q - x - r) with (Q2R q - (x + r)); trivial; ring.
apply Rminus_lt.
apply Rlt_minus in H3.
replace (-r - (Q2R q - x)) with (x - r - Q2R q); trivial; ring.
Qed.

Require Export Compactness.

Lemma bounded_real_net_has_cluster_point: forall (I:DirectedSet)
  (x:Net I RTop) (a b:R), (forall i:DS_set I, a <= x i <= b) ->
  exists x0:point_set RTop, net_cluster_point x x0.
Proof.
(* idea: the liminf is a cluster point *)
intros.
destruct (classic (inhabited (DS_set I))) as [Hinh|Hempty].
assert (forall i:DS_set I, { y:R | is_glb
                             (Im [ j:DS_set I | DS_ord i j ] x) y }).
intro.
apply inf.
exists a.
red; intros.
destruct H0.
destruct (H x0).
rewrite H1.
auto with real.
exists (x i).
exists i; trivial.
constructor.
apply preord_refl.
apply DS_ord_cond.

assert ({ x0:R | is_lub (Im Full_set (fun i:DS_set I => proj1_sig (X i)))
                        x0 }).
apply sup.
exists b.
red; intros.
destruct H0 as [i].
destruct (X i).
simpl in H1.
rewrite H1.
destruct i0.
cut (b >= x0).
auto with real.
apply Rge_trans with (x i).
destruct (H i).
auto with real.
apply H2.
exists i; trivial.
constructor.
apply preord_refl.
apply DS_ord_cond.

destruct Hinh as [i0].
exists (proj1_sig (X i0)).
exists i0; trivial.
constructor.

destruct H0 as [x0].
exists x0.
assert (forall i j:DS_set I, DS_ord i j ->
  proj1_sig (X i) <= proj1_sig (X j)).
intros.
destruct (X i0).
destruct (X j).
simpl.
destruct i1.
destruct i2.
apply H4.
red; intros.
destruct H5.
destruct H5.
apply H1.
exists x3; trivial.
constructor.
apply preord_trans with j; trivial.
apply DS_ord_cond.

red; intros.
destruct (RTop_metrization x0).
destruct (open_neighborhood_basis_cond U).
split; trivial.
destruct H3.
destruct H3.
destruct (lub_approx _ _ r i).
trivial.
destruct H5.
destruct H5.
destruct H6.
red; intros.
destruct (DS_join_cond x1 i0).
destruct H9.
remember (X x2) as y2.
destruct y2.
destruct (glb_approx _ _ r i1).
trivial.
destruct H11.
destruct H11.
destruct H11.
destruct H12.
exists x4.
split.
apply preord_trans with x2; trivial.
apply DS_ord_cond.
apply H4.
constructor.
assert (y <= proj1_sig (X x2)).
rewrite H7.
apply H0; trivial.
rewrite <- Heqy2 in H15.
simpl in H15.
assert (proj1_sig (X x2) <= x0).
apply i.
exists x2; trivial.
constructor.
rewrite <- Heqy2 in H16.
simpl in H16.
rewrite <- H13.
apply Rabs_def1.

cut (y0 < x0 + r).
intro.
apply Rlt_minus in H17.
apply Rminus_lt.
replace (y0 - x0 - r) with (y0-(x0+r)); trivial; ring.
apply Rlt_le_trans with (x3 + r).
trivial.
auto with real.

cut (y0 > x0 - r).
intro.
apply Rlt_minus in H17.
apply Rminus_lt.
replace (-r - (y0-x0)) with (x0-r-y0); trivial; ring.
apply Rge_gt_trans with y.
apply Rge_trans with x3; auto with real.
trivial.

exists a.
red; intros.
red; intros.
contradiction Hempty.
exists; exact i.
Qed.

Lemma R_closed_interval_compact: forall a b:R, a <= b ->
  compact (SubspaceTopology ([x:point_set RTop | a <= x <= b])).
Proof.
intros a b Hbound.
apply net_cluster_point_impl_compact.
intros.
pose (y := fun i:DS_set I => proj1_sig (x i)).
destruct (bounded_real_net_has_cluster_point _ y a b).
intros.
unfold y.
destruct (x i).
destruct i0.
simpl.
trivial.

assert (closed [x:point_set RTop | a <= x <= b]).
assert ([x:point_set RTop | a <= x <= b] = Intersection
                [ x:point_set RTop | a <= x ]
                [ x:point_set RTop | x <= b ]).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct H1.
constructor; constructor; trivial.
destruct H1.
destruct H1.
destruct H2.
constructor.
auto.
rewrite H1.
apply closed_intersection2.
apply upper_closed_interval_closed.
constructor; red; intros; auto with real.
apply Rle_trans with y0; trivial.
intros.
destruct (total_order_T x1 y0) as [[|]|]; auto with real.
apply lower_closed_interval_closed.
constructor; red; intros; auto with real.
apply Rle_trans with y0; trivial.
intros.
destruct (total_order_T x1 y0) as [[|]|]; auto with real.

assert (Ensembles.In [x:point_set RTop | a <= x <= b] x0).
rewrite <- (closure_fixes_closed _ H1).
apply net_cluster_point_in_closure with y.
destruct H as [i0].
exists i0.
intros.
constructor.
unfold y.
destruct (x j).
simpl.
destruct i.
trivial.
trivial.

exists (exist _ x0 H2).
red; intros.
destruct (subspace_topology_topology _ _ _ H3) as [V].
destruct H5.
red; intros.
assert (Ensembles.In V x0).
rewrite H6 in H4.
destruct H4.
simpl in H4.
trivial.

destruct (H0 V H5 H7 i) as [j []].
exists j.
split; trivial.
rewrite H6.
constructor.
simpl.
exact H9.
Qed.

Lemma R_compact_subset_bounded: forall A:Ensemble (point_set RTop),
  compact (SubspaceTopology A) -> bound A.
Proof.
intros.
destruct (H (Im Full_set (fun y:R => inverse_image (subspace_inc _)
                   [ x:point_set RTop | y - 1 < x < y + 1 ]))).
intros.
destruct H0.
rewrite H1.
apply subspace_inc_continuous.
replace [x0:point_set RTop | x-1 < x0 < x+1] with
  (Intersection [x0:point_set RTop | x-1 <= x0 /\ x0 <> x-1]
                [x0:point_set RTop | x0 <= x+1 /\ x0 <> x+1]).
pose proof (Build_TopologicalSpace_from_subbasis_subbasis
  _ (order_topology_subbasis _ Rle)).
apply open_intersection2.
apply H2.
constructor.
apply H2.
constructor.
apply Extensionality_Ensembles; split; red; intros.
destruct H2.
destruct H2.
destruct H2.
destruct H3.
destruct H3.
constructor.
split.
destruct (total_order_T (x-1) x0) as [[|]|]; auto with real.
contradiction H4; symmetry; trivial.
assert (x0 < x0).
apply Rlt_le_trans with (x-1); auto with real.
contradict H6; apply Rlt_irrefl.
destruct (total_order_T x0 (x+1)) as [[|]|]; auto with real.
contradiction H5.
assert (x0 < x0).
apply Rle_lt_trans with (x+1); auto with real.
contradict H6; apply Rlt_irrefl.
destruct H2.
destruct H2.
constructor; constructor; split; auto with real.

apply Extensionality_Ensembles; split; red; intros.
constructor.
eexists.
exists (proj1_sig x).
constructor.
reflexivity.
constructor.
constructor.
destruct x.
simpl.
split; apply Rminus_lt; auto with real.
replace (x-1-x) with (-1); try ring.
apply Ropp_lt_gt_0_contravar.
exact Rlt_0_1.

destruct H0.
destruct H1.
assert (exists a:R, forall S:Ensemble (point_set (SubspaceTopology A)),
  forall b:point_set (SubspaceTopology A),
  Ensembles.In x S -> Ensembles.In S b -> proj1_sig b < a).
clear H2.
induction H0.
exists 0.
intros.
destruct H0.
destruct IHFinite.
cut (Included A0 (Add A0 x)); auto with sets.
assert (Ensembles.In (Add A0 x) x).
right.
constructor.
apply H1 in H4.
destruct H4.
exists (Rmax x0 (x+1)).
intros.
destruct H6.
apply Rlt_le_trans with x0.
apply H3 with x1; trivial.
unfold Rmax.
destruct Rle_dec; auto with real.
destruct H6.
rewrite H5 in H7.
destruct H7.
destruct H6.
apply Rlt_le_trans with (x+1).
apply H6.
unfold Rmax; destruct Rle_dec; auto with real.

destruct H3 as [a].
exists a.
red; intros.
assert (Ensembles.In (FamilyUnion x)
  (exist (fun x:R => Ensembles.In A x) x0 H4)).
rewrite H2; constructor.
inversion H5.
pose proof (H3 _ _ H6 H7).
simpl in H9.
auto with real.
Qed.

Lemma Ropp_continuous: continuous Ropp (X:=RTop) (Y:=RTop).
Proof.
apply pointwise_continuity.
intro.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists eps.
split; trivial.
intros.
unfold R_metric.
replace (-x' - -x) with (x-x'); try ring.
rewrite Rabs_minus_sym; trivial.
Qed.

Require Export Connectedness.

Lemma R_connected: connected RTop.
Proof.
cut (forall S:Ensemble (point_set RTop),
  clopen S -> Ensembles.In S 0 -> S = Full_set).
intro.
red; intros.
destruct (classic (Ensembles.In S 0)).
right.
apply H; trivial.
left.
assert (Complement S = Full_set).
apply H; trivial.
destruct H0; split; trivial.
red; rewrite Complement_Complement; trivial.
apply Extensionality_Ensembles; split; red; intros.
assert (Ensembles.In (Complement S) x).
rewrite H2; constructor.
contradiction H4.
destruct H3.

cut (forall S:Ensemble (point_set RTop),
  clopen S -> Ensembles.In S 0 -> forall x:R, x > 0 ->
                                  Ensembles.In S x).
intro.
assert (forall S:Ensemble (point_set RTop),
  clopen S -> Ensembles.In S 0 -> forall x:R, x < 0 ->
                                  Ensembles.In S x).
intros.
pose (T := inverse_image Ropp S).

assert (Ensembles.In T (-x)).
apply H.
destruct H0; split.
apply Ropp_continuous; trivial.
red.
subst T.
rewrite <- inverse_image_complement.
apply Ropp_continuous; trivial.
constructor.
replace (-0) with 0; trivial; ring.
cut (0 < -x); auto with real.
destruct H3.
rewrite Ropp_involutive in H3; trivial.

intros.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct (total_order_T x 0) as [[|]|].
apply H0; trivial.
congruence.
apply H; trivial.

intros.
apply NNPP; intro.
pose (T := [ y:R | forall z:R, 0 <= z <= y -> Ensembles.In S z ]).
assert (Ensembles.In T 0).
constructor.
intros.
assert (z = 0).
destruct H3; auto with real.
rewrite H4; trivial.

destruct (sup T).
exists x.
red; intros.
cut (~ x0>x).
apply Rnot_lt_le; auto with real.
intro.
destruct H4.
apply H2.
apply H4.
split; auto with real.
exists 0.
exact H3.

assert (0 <= x0).
apply i.
exact H3.

destruct (RTop_metrization x0).
assert (Ensembles.In S x0).
rewrite <- (closure_fixes_closed S); try apply H.
apply meets_every_open_neighborhood_impl_closure.
intros.
destruct (open_neighborhood_basis_cond U).
split; trivial.
destruct H7.
destruct H7.
destruct (lub_approx _ _ r i).
trivial.
destruct H9.
exists (Rmax x1 0).
constructor.
unfold Rmax.
destruct Rle_dec.
trivial.
apply H9.
auto with real.

apply H8.
constructor.
unfold Rmax.
destruct Rle_dec.
unfold R_metric.
rewrite Rabs_minus_sym.
replace (x0-0) with x0; try ring.
apply Rabs_def1.
apply Rminus_lt.
destruct H10.
apply Rlt_le_trans with x1; trivial.
apply Rlt_le_trans with 0; auto with real.

apply Rabs_def1.
apply Rle_lt_trans with 0; auto with real.
destruct H10.
apply Rle_minus; trivial.
destruct H10.
apply Rminus_lt.
apply Rlt_minus in H10.
replace (-r - (x1-x0)) with (x0-r-x1); trivial; ring.

destruct (open_neighborhood_basis_cond S).
split; trivial.
apply H.
destruct H6.
destruct H6.

destruct (lub_approx _ _ r i).
trivial.
destruct H8.

assert (Ensembles.In T (x0+r/2)).
constructor.
intros.
destruct H10.
destruct (total_order_T z x1) as [[|]|].
apply H8.
split; auto with real.
apply H8.
split; auto with real.
apply H7.
constructor.
apply Rabs_def1.
apply Rle_lt_trans with (r/2).
apply Rminus_le.
apply Rle_minus in H11.
replace (z-x0-r/2) with (z-(x0+r/2)); trivial; ring.
apply Rminus_gt.
replace (r-r/2) with (r/2); try field.
apply Rmult_gt_0_compat; auto with real.
auto with *.
apply Rlt_trans with (x1 - x0).
destruct H9.
apply Rlt_minus in H9.
apply Rminus_lt.
replace (-r - (x1-x0)) with (x0-r-x1); trivial; ring.
cut (x1<z); trivial.
intro.
unfold Rminus.
auto with real.

assert (x0 + r/2 <= x0).
apply i.
exact H10.

absurd (x0 + r/2 > x0).
apply Rge_not_gt; auto with real.
apply Rminus_gt.
ring_simplify.
apply Rmult_gt_0_compat; auto with real.
apply Rinv_0_lt_compat.
auto with real.
Qed.

Require Export Completeness.

Lemma R_cauchy_sequence_bounded: forall x:nat->R,
  cauchy R_metric x -> bound (Im Full_set x).
Proof.
intros.
destruct (H 1) as [N].
red; auto with real.
assert (exists y:R, forall n:nat, (n<N)%nat -> x n <= y).
clear H0; induction N.
exists 0.
intros.
contradict H0.
auto with arith.
destruct IHN as [y].
exists (Rmax y (x N)).
intros.
apply lt_n_Sm_le in H1.
destruct (le_lt_or_eq _ _ H1).
apply Rle_trans with y.
apply H0; trivial.
apply Rmax_l.
rewrite H2.
apply Rmax_r.

destruct H1 as [y].
exists (Rmax y (x N + 1)).
red; intros.
destruct H2 as [n].
rewrite H3; clear y0 H3.
destruct (le_or_lt N n).
apply Rle_trans with (x N + 1).
assert (R_metric (x n) (x N) < 1).
apply H0; auto with arith.
apply Rabs_def2 in H4.
destruct H4.
Require Import Fourier.
fourier.
apply Rmax_r.
apply Rle_trans with y; auto.
apply Rmax_l.
Qed.

Lemma R_cauchy_sequence_lower_bound: forall x:nat->R,
  cauchy R_metric x -> lower_bound (Im Full_set x).
Proof.
intros.
assert (cauchy R_metric (fun n:nat => - x n)).
red; intros.
destruct (H eps H0) as [N].
exists N.
intros.
replace (R_metric (- x m) (- x n)) with (R_metric (x m) (x n)).
apply H1; trivial.
unfold R_metric.
replace (x n - x m) with (- (- x n - - x m)) by ring.
apply Rabs_Ropp.
destruct (R_cauchy_sequence_bounded _ H0) as [m].
exists (-m).
red; intros.
cut (-x0 <= m).
intros; fourier.
apply H1.
destruct H2 as [n].
exists n; trivial.
f_equal; trivial.
Qed.

Lemma R_metric_complete: complete R_metric R_metric_is_metric.
Proof.
red; intros.
destruct (R_cauchy_sequence_bounded _ H) as [b].
destruct (R_cauchy_sequence_lower_bound _ H) as [a].
destruct (bounded_real_net_has_cluster_point nat_DS x a b) as [x0].
intros; split; [ cut (x i >= a); auto with real; apply H1 | apply H0 ];
  exists i; trivial; constructor.
exists x0.
apply cauchy_sequence_with_cluster_point_converges; trivial.
apply metric_space_net_cluster_point with R_metric;
  try apply MetricTopology_metrizable.
intros.
apply metric_space_net_cluster_point_converse with RTop; trivial.
apply RTop_metrization.
Qed.
