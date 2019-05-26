Require Export RTopology.
Require Export ProductTopology.

Lemma Rplus_continuous: continuous_2arg Rplus (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
apply pointwise_continuity_2arg.
intros.
red.
pose proof (RTop_metrization (x+y)).
apply continuous_at_neighborhood_basis with
  (metric_topology_neighborhood_basis R_metric (x+y)).
apply open_neighborhood_basis_is_neighborhood_basis.
apply RTop_metrization.

intros.
destruct H0.
exists ([ p:point_set RTop * point_set RTop | let (x',y'):=p in
  In (open_ball _ R_metric x (r/2)) x' /\
  In (open_ball _ R_metric y (r/2)) y' ]).
repeat split.
apply ProductTopology2_basis_is_basis.
constructor.
pose proof (RTop_metrization x).
destruct H1.
apply (open_neighborhood_basis_elements
  (open_ball _ R_metric x (r/2))).
constructor.
Require Import Fourier.
fourier.
destruct (RTop_metrization y).
apply (open_neighborhood_basis_elements
  (open_ball _ R_metric y (r/2))).
constructor.
fourier.
rewrite metric_zero.
fourier.
apply R_metric_is_metric.
rewrite metric_zero.
fourier.
apply R_metric_is_metric.
destruct x0 as [x' y'].
destruct H1 as [[[] []]].
unfold R_metric.
replace (x'+y' - (x+y)) with ((x'-x) + (y'-y)) by ring.
apply Rle_lt_trans with (Rabs (x'-x) + Rabs(y'-y)).
apply Rabs_triang.
replace r with (r/2+r/2) by field; apply Rplus_lt_compat; trivial.
Qed.

Corollary sum_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x + g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere.
apply Rplus_continuous.
Qed.

(* Ropp_continuous was already proved in RTopology *)

Lemma Rminus_continuous: continuous_2arg Rminus
  (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
unfold Rminus.
apply pointwise_continuity_2arg; intros.
red.
pose proof (sum_continuous _
  (fun p:point_set (ProductTopology2 RTop RTop) => fst p)
  (fun p:point_set (ProductTopology2 RTop RTop) => -snd p) (x,y)).
simpl in H.
match goal with |- continuous_at ?f ?q =>
  replace f with (fun p:R*R => fst p + - snd p) end.
apply sum_continuous.
apply continuous_func_continuous_everywhere.
apply product2_fst_continuous.
apply (continuous_composition_at (Y:=RTop)).
apply continuous_func_continuous_everywhere.
apply Ropp_continuous.
apply continuous_func_continuous_everywhere.
apply product2_snd_continuous.

Require Import FunctionalExtensionality.
extensionality p.
destruct p as [x' y'].
trivial.
Qed.

Corollary diff_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x - g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere.
exact Rminus_continuous.
Qed.

Lemma const_multiple_func_continuous: forall c:R,
  continuous (fun x:R => c*x) (X:=RTop) (Y:=RTop).
Proof.
intros.
apply pointwise_continuity; intros.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
destruct (classic (c=0)).
exists 1.
split.
red; auto with real.
intros.
rewrite H.
unfold R_metric.
replace (0*x'-0*x) with 0 by ring.
rewrite Rabs_R0.
trivial.

intros.
exists (eps / Rabs c).
split.
apply Rmult_gt_0_compat; trivial.
apply Rinv_0_lt_compat.
apply Rabs_pos_lt; trivial.
intros.
unfold R_metric.
replace (c*x' - c*x) with (c*(x'-x)) by ring.
rewrite Rabs_mult.
replace eps with (Rabs c * (eps / Rabs c)); try field.
apply Rmult_lt_compat_l.
apply Rabs_pos_lt; trivial.
trivial.
apply Rabs_no_R0; trivial.
Qed.

Corollary const_multiple_continuous: forall (X:TopologicalSpace)
  (f:point_set X -> point_set RTop) (c:R) (x:point_set X),
  continuous_at f x -> continuous_at (fun x:point_set X => c * f x) x
                       (Y:=RTop).
Proof.
intros.
apply continuous_composition_at; trivial.
apply continuous_func_continuous_everywhere.
apply const_multiple_func_continuous with (c:=c).
Qed.

Lemma Rmult_continuous_at_origin: continuous_at_2arg Rmult 0 0
                                  (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
red.
pose proof (RTop_metrization 0).
apply continuous_at_neighborhood_basis with
  (metric_topology_neighborhood_basis R_metric 0).
apply open_neighborhood_basis_is_neighborhood_basis.
replace (0*0) with 0 by auto with real.
apply H.

intros.
destruct H0.
exists (characteristic_function_to_ensemble
  (fun p:point_set RTop * point_set RTop => let (x',y'):=p in
  In (open_ball _ R_metric 0 r) x' /\
  In (open_ball _ R_metric 0 1) y' )).
repeat split.
apply ProductTopology2_basis_is_basis.
constructor.
destruct H.
apply (open_neighborhood_basis_elements (open_ball _ R_metric 0 r)).
constructor; trivial.
destruct H.
apply (open_neighborhood_basis_elements (open_ball _ R_metric 0 1)).
constructor; red; auto with real.
rewrite metric_zero; trivial.
apply R_metric_is_metric.
rewrite metric_zero; auto with real.
apply R_metric_is_metric.

destruct H1.
destruct x as [x y].
destruct H1 as [[] []].
unfold R_metric in H1, H2.
unfold R_metric.
replace (x*y-0) with (x*y) by auto with real.
replace (x-0) with x in H1 by auto with real.
replace (y-0) with y in H2 by auto with real.
rewrite Rabs_mult.
replace r with (r*1) by auto with real.
apply Rmult_le_0_lt_compat; trivial.
apply Rabs_pos.
apply Rabs_pos.
Qed.

Lemma Rmult_continuous: continuous_2arg Rmult (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
apply pointwise_continuity_2arg.
intros x0 y0.
red.
match goal with |- continuous_at ?f ?q => replace f with
  (fun p:point_set RTop*point_set RTop =>
   (fst p - x0) * (snd p - y0) + y0 * fst p + x0 * snd p - x0 * y0) end.
apply diff_continuous.
apply sum_continuous.
apply sum_continuous.
apply continuous_composition_at_2arg with RTop RTop.
simpl.
replace (x0-x0) with 0 by ring.
replace (y0-y0) with 0 by ring.
apply Rmult_continuous_at_origin.
apply diff_continuous.
apply continuous_func_continuous_everywhere; apply product2_fst_continuous.
apply continuous_func_continuous_everywhere; apply continuous_constant.
apply diff_continuous.
apply continuous_func_continuous_everywhere; apply product2_snd_continuous.
apply continuous_func_continuous_everywhere; apply continuous_constant.
apply const_multiple_continuous.
apply continuous_func_continuous_everywhere; apply product2_fst_continuous.
apply const_multiple_continuous.
apply continuous_func_continuous_everywhere; apply product2_snd_continuous.
apply continuous_func_continuous_everywhere; apply continuous_constant.

extensionality p.
destruct p as [x y].
simpl.
ring.
Qed.

Corollary product_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x:point_set X),
  continuous_at f x -> continuous_at g x ->
  continuous_at (fun x:point_set X => f x * g x) x (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply continuous_func_continuous_everywhere.
exact Rmult_continuous.
Qed.

Lemma Rinv_continuous_at_1: continuous_at Rinv 1 (X:=RTop) (Y:=RTop).
Proof.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists (Rmin (1/2) (eps/2)).
split; intros.
apply Rmin_Rgt_r; split; fourier.
assert (x' > 1/2).
assert (Rabs (x'-1) < 1/2).
apply Rlt_le_trans with (1 := H0).
apply Rmin_l.
destruct (Rabs_def2 _ _ H1).
fourier.
assert (/ x' < 2).
rewrite <- Rinv_involutive.
apply Rinv_lt_contravar.
apply Rmult_lt_0_compat; fourier.
unfold Rdiv in H1.
replace (1 * / 2) with (/ 2) in H1 by auto with real.
exact H1.
intro.
fourier.

unfold R_metric.
replace (/ x' - / 1) with ((1 - x') * / x'); try field.
rewrite Rabs_mult.
rewrite (Rabs_right (/ x')).
rewrite Rabs_minus_sym.
assert (Rabs (x' - 1) < eps/2).
apply Rlt_le_trans with (1:=H0).
apply Rmin_r.
replace eps with ((eps/2) * 2) by field.
apply Rmult_gt_0_lt_compat; trivial.
apply Rinv_0_lt_compat.
fourier.
fourier.
left.
apply Rinv_0_lt_compat.
fourier.
intro.
fourier.
Qed.

Lemma Rinv_continuous: forall x0:R, x0<>0 -> continuous_at Rinv x0
                                             (X:=RTop) (Y:=RTop).
Proof.
intros.
apply continuous_at_is_local with
  (f:=fun x:R => /x0 * Rinv (/x0 * x))
  (N:=Complement (Singleton 0)).
apply open_neighborhood_is_neighborhood.
split.
apply Hausdorff_impl_T1_sep.
apply T3_sep_impl_Hausdorff.
apply normal_sep_impl_T3_sep.
apply metrizable_impl_normal_sep.
exists R_metric.
apply R_metric_is_metric.
apply RTop_metrization.

intro.
destruct H0.
contradiction H.
reflexivity.

intros.
assert (x<>0).
intro.
contradiction H0.
rewrite H1; constructor.
simpl.
field; split; trivial.

apply const_multiple_continuous.
apply (continuous_composition_at (Y:=RTop)).
replace (/x0 * x0) with 1.
apply Rinv_continuous_at_1.
field; trivial.
apply continuous_func_continuous_everywhere.
apply const_multiple_func_continuous with (c:=/ x0).
Qed.

Lemma Rdiv_continuous: forall x y:R, y <> 0 ->
  continuous_at_2arg Rdiv x y (X:=RTop) (Y:=RTop) (Z:=RTop).
Proof.
intros.
red.
match goal with |- continuous_at ?f ?q => replace f with
  (fun p:point_set RTop * point_set RTop => fst p * / snd p) end.
apply product_continuous.
apply continuous_func_continuous_everywhere; apply product2_fst_continuous.
apply continuous_composition_at.
simpl.
apply Rinv_continuous; trivial.
apply continuous_func_continuous_everywhere; apply product2_snd_continuous.

extensionality p.
destruct p as [x' y'].
trivial.
Qed.

Corollary quotient_continuous: forall (X:TopologicalSpace)
  (f g:point_set X -> point_set RTop) (x0:point_set X),
  continuous_at f x0 -> continuous_at g x0 -> g x0 <> 0 ->
  continuous_at (fun x:point_set X => f x / g x) x0 (Y:=RTop).
Proof.
intros.
apply continuous_composition_at_2arg; trivial.
apply Rdiv_continuous; trivial.
Qed.

Lemma Rabs_continuous: continuous Rabs (X:=RTop) (Y:=RTop).
Proof.
apply pointwise_continuity; intros.
apply metric_space_fun_continuity with R_metric R_metric;
  try apply RTop_metrization.
intros.
exists eps; split; trivial.
intros.
apply Rle_lt_trans with (2 := H0).
apply Rabs_triang_inv2.
Qed.

(* a miscellaneous example which is used in the proof of the
   Tietze extension theorem *)
Require Export Homeomorphisms.

Lemma open_interval_homeomorphic_to_real_line:
  let U:=characteristic_function_to_ensemble
      (fun x:point_set RTop => -1 < x < 1) in
  homeomorphic RTop (SubspaceTopology U).
Proof.
intros.
assert (forall x:R, -1 < x / (1 + Rabs x) < 1).
intros.
assert (0 < 1 + Rabs x).
apply Rlt_le_trans with 1; auto with real.
pattern 1 at 1; replace 1 with (1+0) by auto with real.
apply Rplus_le_compat_l.
apply Rabs_pos.
apply and_comm; apply Rabs_def2.
unfold Rdiv; rewrite Rabs_mult.
rewrite Rabs_Rinv.
rewrite (Rabs_right (1 + Rabs x)); try (left; trivial).
pattern 1 at 2; replace 1 with ((1 + Rabs x) * / (1 + Rabs x)).
apply Rmult_lt_compat_r.
apply Rinv_0_lt_compat; trivial.
pattern (Rabs x) at 1; replace (Rabs x) with (0 + Rabs x); auto with real.
field.
apply Rgt_not_eq; trivial.
apply Rgt_not_eq; trivial.

assert (forall x:point_set RTop, In U (x / (1 + Rabs x))).
intros; constructor; apply H.
Require Import ContinuousFactorization.
exists (continuous_factorization _ _ H0).
exists (fun x:point_set (SubspaceTopology U) =>
  (subspace_inc U x) / (1 - Rabs (subspace_inc U x))).
apply factorization_is_continuous.
apply pointwise_continuity; intros.
apply quotient_continuous.
apply continuous_func_continuous_everywhere; apply continuous_identity.
apply sum_continuous.
apply continuous_func_continuous_everywhere; apply continuous_constant.
apply continuous_func_continuous_everywhere; apply Rabs_continuous.
apply Rgt_not_eq.
apply Rlt_le_trans with 1; auto with real.
pattern 1 at 1; replace 1 with (1+0) by auto with real.
apply Rplus_le_compat_l.
apply Rabs_pos.

apply pointwise_continuity; intros.
apply quotient_continuous.
apply continuous_func_continuous_everywhere; apply subspace_inc_continuous.
apply diff_continuous.
apply continuous_func_continuous_everywhere; apply continuous_constant.
apply continuous_composition_at.
apply continuous_func_continuous_everywhere; apply Rabs_continuous.
apply continuous_func_continuous_everywhere; apply subspace_inc_continuous.
apply Rgt_not_eq.
apply Rgt_minus.
red.
destruct x as [x [[]]]; simpl.
apply Rabs_def1; trivial.

simpl.
intros.
unfold Rabs at 1 3; destruct Rcase_abs.
rewrite Rabs_left.
field.
split; intro; fourier.
assert (/ (1 + -x) > 0).
apply Rinv_0_lt_compat.
fourier.
replace 0 with (x*0) by auto with real.
apply Rmult_lt_gt_compat_neg_l; trivial.

rewrite Rabs_right.
field.
split; intro; fourier.
assert (/ (1+x) > 0).
apply Rinv_0_lt_compat.
fourier.
apply Rle_ge.
apply Rge_le in r.
red in H1.
unfold Rdiv.
replace 0 with (0 * / (1+x)); auto with real.

intros.
destruct y as [x].
simpl.
From ZornsLemma Require Import Proj1SigInjective.
apply subset_eq_compatT.
destruct i.
destruct H1.
assert (Rabs x < 1).
apply Rabs_def1; trivial.

unfold Rabs at 1 3; destruct Rcase_abs.
rewrite Rabs_left.
field.
split; intro; fourier.
replace (1 - -x) with (1+x) by ring.
assert (/ (1+x) > 0).
apply Rinv_0_lt_compat.
fourier.
unfold Rdiv.
replace 0 with (x*0) by auto with real.
apply Rmult_lt_gt_compat_neg_l; trivial.

rewrite Rabs_right.
field.
split; intro; fourier.
assert (/ (1-x) > 0).
apply Rinv_0_lt_compat.
apply Rgt_minus; trivial.
unfold Rdiv.
red in H4.
apply Rge_le in r.
apply Rle_ge.
replace 0 with (0 * / (1-x)); auto with real.
Qed.
