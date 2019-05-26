Require Export MetricSpaces.

Section UniformTopology.

Variable X Y:Type.
Variable d:Y->Y->R.
Variable y0:X->Y. (* base function limiting the extents of the
                  range of a function X->Y *)
Hypothesis d_metric: metric d.
Hypothesis X_inhabited: inhabited X.

Definition uniform_space := { f:X->Y | bound (Im Full_set
                                      (fun x:X => d (y0 x) (f x))) }.

Definition uniform_metric (f g:uniform_space) : R.
refine (match f, g with exist f0 Hf, exist g0 Hg =>
  proj1_sig (sup (Im Full_set (fun x:X => d (f0 x) (g0 x))) _ _) end).
destruct Hf as [mf].
destruct Hg as [mg].
exists (mf + mg).
red; intros.
destruct H1.
rewrite H2.
apply Rle_trans with (d (y0 x) (f0 x) + d (y0 x) (g0 x)).
rewrite (metric_sym _ d d_metric (y0 x) (f0 x)); trivial;
  apply triangle_inequality; trivial.
assert (d (y0 x) (f0 x) <= mf) by (apply H; exists x; trivial).
assert (d (y0 x) (g0 x) <= mg) by (apply H0; exists x; trivial).
auto with real.

destruct X_inhabited as [x0].
exists (d (f0 x0) (g0 x0)); exists x0; trivial; constructor.
Defined.

Lemma uniform_metric_is_metric: metric uniform_metric.
Proof.
constructor; intros.
unfold uniform_metric.
destruct x as [f0 Hf]; destruct y as [g0 Hg]; destruct sup.
simpl.
destruct X_inhabited as [x0].
apply Rge_trans with (d (f0 x0) (g0 x0)).
cut (d (f0 x0) (g0 x0) <= x); auto with real.
apply i.
exists x0; trivial.
constructor.
apply d_metric.
unfold uniform_metric.
destruct x as [f0 Hf]; destruct y as [g0 Hg].
destruct sup.
destruct sup.
simpl.
assert (Im Full_set (fun x:X => d (f0 x) (g0 x)) =
        Im Full_set (fun x:X => d (g0 x) (f0 x))).
apply Extensionality_Ensembles; split; red; intros.
destruct H.
exists x1.
constructor.
rewrite metric_sym; trivial.
destruct H.
exists x1.
constructor.
rewrite metric_sym; trivial.
apply Rle_antisym.
apply i.
rewrite H.
apply i0.
apply i0.
rewrite <- H.
apply i.

destruct x as [f0 Hf]; destruct y as [g0 Hg]; destruct z as [h0 Hh].
simpl.
repeat destruct sup; simpl.
apply i.
red; intros.
destruct H.
rewrite H0.
apply Rle_trans with (d (f0 x2) (g0 x2) + d (g0 x2) (h0 x2)).
apply d_metric.
assert (d (f0 x2) (g0 x2) <= x0) by
  (apply i0; exists x2; trivial).
assert (d (g0 x2) (h0 x2) <= x1) by
  (apply i1; exists x2; trivial).
auto with real.

destruct x as [f0 Hf].
simpl.
destruct sup; simpl.
apply Rle_antisym.
apply i.
red; intros.
destruct H.
rewrite metric_zero in H0; trivial.
right; trivial.
apply i.
destruct X_inhabited as [x0].
exists x0.
constructor.
symmetry; apply d_metric.

destruct x as [f0 Hf]; destruct y as [g0 Hg].
From ZornsLemma Require Import Proj1SigInjective.
apply subset_eq_compatT.
Require Import FunctionalExtensionality.
extensionality x.
apply d_metric.
simpl in H.
destruct sup in H.
simpl in H.
rewrite H in i; clear H.
apply Rle_antisym.
apply i; exists x; trivial.
constructor.
cut (d (f0 x) (g0 x) >= 0); auto with real.
apply d_metric.
Qed.

Definition UniformTopology : TopologicalSpace :=
  MetricTopology uniform_metric uniform_metric_is_metric.

Require Export Completeness.

Lemma uniform_metric_complete: complete d d_metric ->
  complete uniform_metric uniform_metric_is_metric.
Proof.
intros.
assert (forall y:Net nat_DS (MetricTopology d d_metric), cauchy d y ->
  { y0:Y | net_limit y y0 }) as cauchy_limit.
intros.
Require Import Description.
apply constructive_definite_description.
apply -> unique_existence; split.
apply H; trivial.
apply (Hausdorff_impl_net_limit_unique y).
apply T3_sep_impl_Hausdorff.
apply normal_sep_impl_T3_sep.
apply metrizable_impl_normal_sep.
exists d; trivial; apply MetricTopology_metrizable.

red; intros f ?.
unshelve refine (let H1 := _ in let H2 := _ in ex_intro _
  (exist _ (fun x:X => proj1_sig (cauchy_limit
                  (fun n:nat => proj1_sig (f n) x) (H1 x))) H2) _); [ | clearbody H1 | clearbody H1 H2 ].
intros.
red; intros.
destruct (H0 eps H1) as [N].
exists N; intros.
apply Rle_lt_trans with (uniform_metric (f m) (f n)).
unfold uniform_metric.
destruct (f m) as [f0 Hf]; destruct (f n) as [g0 Hg]; destruct sup.
simpl.
apply i.
exists x; trivial; constructor.
apply H2; trivial.

assert (1 > 0) by (red; auto with real).
destruct (H0 1 H2) as [N].
pose (fN := f N).
assert (f N = fN) by reflexivity.
destruct fN as [fN [M]].
assert (forall (n:nat) (x:X), (n >= N)%nat -> d (proj1_sig (f n) x)
                                               (proj1_sig (f N) x) < 1).
intros.
apply Rle_lt_trans with (uniform_metric (f n) (f N)).
unfold uniform_metric; destruct (f n) as [f0 Hf];
  destruct (f N) as [g0 Hg]; destruct sup; simpl.
apply i0.
exists x; trivial.
constructor.
apply H3; trivial.
constructor.
assert (forall x:X,
  d (fN x) (proj1_sig (cauchy_limit _ (H1 x))) <= 1).
intros.
apply lt_plus_epsilon_le.
intros.
destruct cauchy_limit; simpl.
pose proof (metric_space_net_limit_converse _ _
  (MetricTopology_metrizable _ d d_metric) nat_DS
  (fun n:nat => proj1_sig (f n) x) x0 n).
destruct (H7 eps H6) as [i0].
Require Import Max.
pose (N' := max N i0).
apply Rle_lt_trans with (d (fN x) (proj1_sig (f N') x) +
                         d x0 (proj1_sig (f N') x)).
rewrite metric_sym with (x:=x0) (y:=proj1_sig (f N') x); trivial.
apply d_metric.
replace (fN x) with (proj1_sig (f N) x).
assert (d (proj1_sig (f N) x) (proj1_sig (f N') x) < 1).
rewrite metric_sym; trivial.
apply H5.
apply le_max_l.
assert (d x0 (proj1_sig (f N') x) < eps).
apply H8.
apply le_max_r.
auto with real.
rewrite H4; reflexivity.
exists (M+1).
red; intros.
destruct H7.
rewrite H8; clear H8.
apply Rle_trans with (d (y0 x) (fN x) + d (fN x)
                                   (proj1_sig (cauchy_limit _ (H1 x)))).
apply d_metric.
assert (d (y0 x) (fN x) <= M).
apply i.
exists x; trivial.
auto with real.

apply metric_space_net_limit with uniform_metric.
apply MetricTopology_metrizable.
intros.
Require Import Fourier.
assert (eps/2 > 0) by fourier.
destruct (H0 (eps/2) H4) as [N].
exists N; intros.
apply Rle_lt_trans with (eps/2); try fourier.
unfold uniform_metric; remember (f j) as fj; destruct fj as [fj].
destruct sup; simpl.
apply i.
red; intros.
destruct H7.
rewrite H8; clear y H8.
apply lt_plus_epsilon_le; intros.
destruct (cauchy_limit (fun n:nat => proj1_sig (f n) x0) (H1 x0));
  simpl.
pose proof (metric_space_net_limit_converse _ _
  (MetricTopology_metrizable _ d d_metric) nat_DS
  (fun n:nat => proj1_sig (f n) x0) x1 n).
destruct (H9 eps0 H8) as [N'].
pose (N'' := max N N').
apply Rle_lt_trans with (d x1 (proj1_sig (f N'') x0) +
                        d (proj1_sig (f N'') x0) (proj1_sig (f j) x0)).
repeat rewrite <- Heqfj; simpl.
apply d_metric.
assert (d x1 (proj1_sig (f N'') x0) < eps0).
apply H10.
apply le_max_r.
assert (d (proj1_sig (f N'') x0) (proj1_sig (f j) x0) < eps/2).
apply Rle_lt_trans with (uniform_metric (f N'') (f j)).
unfold uniform_metric; destruct (f N'') as [f1];
  destruct (f j) as [f2]; destruct sup; simpl.
apply i0; exists x0; trivial.
apply H5; trivial.
apply le_max_l.
rewrite (Rplus_comm (eps/2) eps0).
auto with real.
Qed.

End UniformTopology.

Arguments uniform_space {X} {Y}.
Arguments uniform_metric {X} {Y}.
Arguments UniformTopology {X} {Y}.

Section UniformTopology_and_continuity.

Variable X:TopologicalSpace.
Variable Y:Type.
Variable d:Y->Y->R.
Variable y0:point_set X -> Y.
Hypothesis d_metric: metric d.
Hypothesis X_inh: inhabited (point_set X).

Lemma continuous_functions_at_point_closed_in_uniform_metric:
  forall x0:point_set X,
  closed (fun f:uniform_space d y0 => continuous_at (proj1_sig f) x0
                                      (Y:=MetricTopology d d_metric))
    (X:=UniformTopology d y0 d_metric X_inh).
Proof.
intros.
match goal with |- @closed ?X ?F => cut (Included (@closure X F) F) end.
intros.
match type of H with | Included ?A ?B => assert (A=B) end.
apply Extensionality_Ensembles; split; trivial;
  apply closure_inflationary.
rewrite <- H0; apply closure_closed.
red; intros f0 ?.
red.
apply first_countable_sequence_closure in H.
destruct H as [f []].
pose proof (MetricTopology_metrizable _ d d_metric
  (proj1_sig f0 x0)).
apply open_neighborhood_basis_is_neighborhood_basis in H1.
apply continuous_at_neighborhood_basis with (1:=H1).
intros.
destruct H2.
assert (r/3>0) by fourier.
destruct (metric_space_net_limit_converse _ _
  (MetricTopology_metrizable _ _
     (uniform_metric_is_metric _ _ d y0 d_metric X_inh))
  nat_DS f f0 H0 (r/3) H3) as [N].
assert (neighborhood
  (inverse_image (proj1_sig (f N))
     (open_ball _ d (proj1_sig (f N) x0) (r/3))) x0).
apply H.
pose proof (MetricTopology_metrizable _ d d_metric
  (proj1_sig (f N) x0)).
apply open_neighborhood_basis_is_neighborhood_basis in H5.
apply H5.
constructor; trivial.
match goal with H5:neighborhood ?U x0 |- neighborhood ?V x0 =>
  cut (Included U V) end.
intros.
destruct H5 as [U []].
exists U; auto with sets.
red; intros.
destruct H6.
destruct H6.
constructor.
constructor.
apply Rle_lt_trans with
  (d (proj1_sig f0 x0) (proj1_sig (f N) x0) +
   d (proj1_sig (f N) x0) (proj1_sig f0 x)).
apply d_metric.
apply Rle_lt_trans with
  (d (proj1_sig f0 x0) (proj1_sig (f N) x0) +
   d (proj1_sig (f N) x0) (proj1_sig (f N) x) +
   d (proj1_sig (f N) x) (proj1_sig f0 x)).
assert (d (proj1_sig (f N) x0) (proj1_sig f0 x) <=
        d (proj1_sig (f N) x0) (proj1_sig (f N) x) +
        d (proj1_sig (f N) x) (proj1_sig f0 x)) by apply d_metric.
fourier.
assert (forall x':point_set X,
  d (proj1_sig f0 x') (proj1_sig (f N) x') < r/3).
intros.
apply Rle_lt_trans with (uniform_metric d y0 d_metric X_inh f0 (f N)).
unfold uniform_metric; destruct f0 as [f0]; destruct (f N) as [fN];
  destruct sup; simpl.
apply i.
exists x'; trivial.
constructor.
apply H4; simpl; auto with arith.
rewrite (metric_sym _ d d_metric (proj1_sig (f N) x) (proj1_sig f0 x)).
pose proof (H7 x0); pose proof (H7 x).
fourier.

apply metrizable_impl_first_countable.
exists (uniform_metric d y0 d_metric X_inh).
exact (uniform_metric_is_metric _ _ d y0 d_metric X_inh).
apply MetricTopology_metrizable.
Qed.

Lemma continuous_functions_closed_in_uniform_metric:
  closed (fun f:uniform_space d y0 => continuous (proj1_sig f)
                                      (Y:=MetricTopology d d_metric))
    (X:=UniformTopology d y0 d_metric X_inh).
Proof.
replace (fun f:uniform_space d y0 => continuous (proj1_sig f)
                                     (Y:=MetricTopology d d_metric)) with
  (IndexedIntersection (fun (x0:point_set X) (f:uniform_space d y0) =>
         continuous_at (proj1_sig f) x0 (Y:=MetricTopology d d_metric))).
apply (@closed_indexed_intersection (UniformTopology d y0 d_metric X_inh)).
apply continuous_functions_at_point_closed_in_uniform_metric.

apply Extensionality_Ensembles; split; intros f ?.
destruct H.
apply pointwise_continuity; trivial.
constructor; intros x.
unfold In in H |-*.
apply continuous_func_continuous_everywhere; trivial.
Qed.

End UniformTopology_and_continuity.
