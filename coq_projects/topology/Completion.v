Require Export Completeness.
Require Import UniformTopology.
Require Import RTopology.

Lemma completion_exists: forall (X:Type) (d:X->X->R) (d_metric:metric d),
  exists Y:Type, exists i:X->Y, exists d':Y->Y->R,
  exists d'_metric:metric d',
  injective i /\ dense (Im Full_set i) (X:=MetricTopology d' d'_metric) /\
  (forall x1 x2:X, d' (i x1) (i x2) = d x1 x2) /\
  complete d' d'_metric.
Proof.
intros.
(* first of all, it suffices to construct a (Y, d') without the
   density condition; then the restriction of d' to the closure of X
   is again complete, and X is dense in it *)
cut (exists Y:Type, exists i:X->Y, exists d':Y->Y->R,
  exists d'_metric:metric d', injective i /\
  (forall x1 x2:X, d' (i x1) (i x2) = d x1 x2) /\
  complete d' d'_metric).
intros.
destruct H as [Y [i [d' [d'_metric [? []]]]]].
pose (F := closure (Im Full_set i) (X:=MetricTopology d' d'_metric)).
exists {y:Y | In F y}.
assert (forall x:X, In F (i x)).
intros.
apply closure_inflationary.
exists x; trivial.
constructor.
exists (fun x:X => exist _ (i x) (H2 x)).
exists (fun y1 y2 => d' (proj1_sig y1) (proj1_sig y2)).
assert (d'_metric0 : metric (fun (y1 y2:{y:Y | In F y}) =>
                       d' (proj1_sig y1) (proj1_sig y2))).
constructor; try destruct x; try destruct y; try destruct z; simpl;
  try apply d'_metric.
intros.
From ZornsLemma Require Import Proj1SigInjective.
apply subset_eq_compatT.
apply d'_metric; trivial.
exists d'_metric0.
repeat split.
red; intros.
injection H3; intros.
apply H; trivial.
red.
apply Extensionality_Ensembles; split; red; intros.
constructor.
simpl in x.
destruct x.
clear H3.
generalize i0.
apply first_countable_sequence_closure in i0.
destruct i0.
destruct H3.
assert (forall n:nat, { x:X | x0 n = i x }).
intros.
Require Import Description.
apply constructive_definite_description.
apply -> unique_existence.
split.
destruct (H3 n).
exists x1; trivial.
red; intros.
apply H.
rewrite H5 in H6; trivial.
assert (forall n:nat, In F (i (proj1_sig (X0 n)))).
intros; apply H2.
intros.
apply (@net_limit_in_closure nat_DS
  (MetricTopology _ d'_metric0)
  _ (fun n:nat => exist _ (i (proj1_sig (X0 n))) (H5 n))).
red; intros.
exists i1.
split.
simpl; auto with arith.
exists (proj1_sig (X0 i1)).
constructor.
apply subset_eq_compatT.
reflexivity.
pose proof (metric_space_net_limit_converse (MetricTopology d' d'_metric) d'
  (MetricTopology_metrizable _ d' d'_metric) nat_DS x0 x H4).
apply metric_space_net_limit with (1:=MetricTopology_metrizable _ _ d'_metric0).
(*
destruct (metric_space_net_limit (MetricTopology d' d'_metric)
  d' (MetricTopology_metrizable _ d' d'_metric) nat_DS x0 x).
pose proof (H6 H4); clear H6 H7.
apply <- (metric_space_net_limit (MetricTopology _ d'_metric0)
  _ (MetricTopology_metrizable _ _ d'_metric0) nat_DS). *)
intros.
destruct (H6 eps H7).
exists x1.
intros.
simpl.
destruct (X0 j).
simpl.
rewrite <- e.
apply H8; trivial.
apply metrizable_impl_first_countable.
exists d'; trivial.
apply MetricTopology_metrizable.

intros.
simpl.
apply H0.
apply (closed_subset_of_complete_is_complete Y d' d'_metric F);
  trivial.
apply closure_closed.

destruct (classic (inhabited X)).
destruct H as [x0].

(* we now construct Y as the uniform space of functions X->R,
   with base point "distance from x0"; the embedding of X into this
   space is to send x to "distance from x" *)
assert (forall x y z:X, R_metric (d x z) (d y z) <= d x y).
unfold R_metric.
assert (forall a b:R, -b <= a -> a <= b -> Rabs a <= b).
intros.
unfold Rabs.
Require Import Fourier.
destruct Rcase_abs; fourier.
intros.
apply H.
assert (d x z <= d x y + d y z) by apply d_metric.
fourier.
rewrite (metric_sym _ _ d_metric x y).
assert (d y z <= d y x + d x z) by apply d_metric.
fourier.

exists (uniform_space R_metric (d x0)).
unshelve refine (let H0:=_ in ex_intro _ (fun x:X => exist _ (d x) (H0 x)) _).
intros.
exists (d x0 x).
red; intros.
destruct H0.
rewrite H1; trivial.
exists (uniform_metric R_metric (d x0) R_metric_is_metric
  (inhabits x0)).
exists (uniform_metric_is_metric _ _ _ _ _ _).
repeat split.
red; intros.
injection H1; intros.
apply d_metric.
rewrite H2; apply d_metric.

intros.
unfold uniform_metric; destruct sup; simpl.
apply Rle_antisym.
apply i.
red; intros.
destruct H1.
rewrite H2; apply H.
apply i.
exists x1.
constructor.
rewrite metric_zero; trivial.
unfold R_metric.
rewrite (metric_sym _ _ d_metric x2 x1).
rewrite Rminus_0_r.
symmetry; apply Rabs_right; apply d_metric.

apply uniform_metric_complete.
exact R_metric_complete.

exists False.
exists (fun x:X => H (inhabits x)).
exists (False_rect _).
assert (metric (False_rect (False->R))).
constructor; intros; destruct x.
exists H0.
repeat split.
red; intros.
contradiction (H (inhabits x1)).
intros.
contradiction (H (inhabits x1)).
red; intros.
contradiction (x O).
Qed.
