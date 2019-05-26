Require Export TopologicalSpaces.
Require Export Nets.
Require Export FilterLimits.
Require Export Continuity.

Set Asymmetric Patterns.

Definition compact (X:TopologicalSpace) :=
  forall C:Family (point_set X),
    (forall U:Ensemble (point_set X), In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C':Family (point_set X),
      Finite _ C' /\ Included C' C /\
      FamilyUnion C' = Full_set.

Lemma compactness_on_indexed_covers:
  forall (X:TopologicalSpace) (A:Type) (C:IndexedFamily A (point_set X)),
    compact X ->
    (forall a:A, open (C a)) -> IndexedUnion C = Full_set ->
  exists A':Ensemble A, Finite _ A' /\
    IndexedUnion (fun a':{a':A | In A' a'} => C (proj1_sig a')) = Full_set.
Proof.
intros.
pose (cover := ImageFamily C).
destruct (H cover) as [subcover].
intros.
destruct H2.
rewrite H3; apply H0.
unfold cover; rewrite <- indexed_to_family_union; trivial.
destruct H2 as [? []].
destruct (finite_choice _ _
  (fun (U:{U:Ensemble (point_set X) | In subcover U}) (a:A) =>
      proj1_sig U = C a)) as [choice_fun].
apply Finite_ens_type; trivial.
destruct x as [U].
simpl.
apply H3 in i.
destruct i.
exists x; trivial.

exists (Im Full_set choice_fun).
split.
apply FiniteT_img.
apply Finite_ens_type; trivial.
intros; apply classic.
apply Extensionality_Ensembles; split; red; intros.
constructor.
rewrite <- H4 in H6.
destruct H6.
assert (In (Im Full_set choice_fun) (choice_fun (exist _ S H6))).
exists (exist _ S H6).
constructor.
trivial.
exists (exist _ (choice_fun (exist _ S H6)) H8).
simpl.
rewrite <- H5.
simpl.
trivial.
Qed.

Lemma compact_finite_nonempty_closed_intersection:
  forall X:TopologicalSpace, compact X ->
  forall F:Family (point_set X),
    (forall G:Ensemble (point_set X), In F G -> closed G) ->
    (forall F':Family (point_set X), Finite _ F' -> Included F' F ->
     Inhabited (FamilyIntersection F')) ->
    Inhabited (FamilyIntersection F).
Proof.
intros.
apply NNPP; red; intro.
pose (C := [ U:Ensemble (point_set X) | In F (Complement U) ]).
unshelve refine (let H3:=(H C _ _) in _).
intros.
destruct H3.
apply H0 in H3.
apply closed_complement_open; trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
apply NNPP; red; intro.
contradiction H2.
exists x.
constructor.
intros.
apply NNPP; red; intro.
contradiction H4.
exists (Complement S).
constructor.
rewrite Complement_Complement; trivial.
exact H6.

destruct H3 as [C' [? [? ?]]].
pose (F' := [G : Ensemble (point_set X) | In C' (Complement G)]).
unshelve refine (let H6 := (H1 F' _ _) in _).
assert (F' = Im C' Complement).
apply Extensionality_Ensembles; split; red; intros.
destruct H6.
exists (Complement x); trivial.
symmetry; apply Complement_Complement.
destruct H6.
constructor.
rewrite H7; rewrite Complement_Complement; trivial.
rewrite H6; apply finite_image.
assumption.

red; intros.
destruct H6.
apply H4 in H6.
destruct H6.
rewrite Complement_Complement in H6; trivial.

destruct H6 as [x0].
destruct H6.
assert (In (FamilyUnion C') x).
rewrite H5; constructor.
destruct H7.
assert (In (Complement S) x).
apply H6.
constructor.
rewrite Complement_Complement; trivial.
contradiction H9.
Qed.

Lemma finite_nonempty_closed_intersection_impl_compact:
  forall X:TopologicalSpace,
  (forall F:Family (point_set X),
    (forall G:Ensemble (point_set X), In F G -> closed G) ->
    (forall F':Family (point_set X), Finite _ F' -> Included F' F ->
     Inhabited (FamilyIntersection F')) ->
    Inhabited (FamilyIntersection F)) ->
  compact X.
Proof.
intros.
red; intros.
apply NNPP; red; intro.
pose (F := [ G:Ensemble (point_set X) | In C (Complement G) ]).
unshelve refine (let H3 := (H F _ _) in _).
intros.
destruct H3.
apply H0; trivial.
intros.
apply NNPP; red; intro.
contradiction H2.
exists [ U:Ensemble (point_set X) | In F' (Complement U) ].
repeat split.
assert ([U:Ensemble (point_set X) | In F' (Complement U)] =
  Im F' Complement).
apply Extensionality_Ensembles; split; red; intros.
destruct H6.
exists (Complement x); trivial.
symmetry; apply Complement_Complement.
constructor.
destruct H6.
rewrite H7; rewrite Complement_Complement; trivial.
rewrite H6; apply finite_image; trivial.

red; intros.
destruct H6.
apply H4 in H6.
destruct H6.
rewrite Complement_Complement in H6; trivial.

apply Extensionality_Ensembles; split; red; intros.
constructor.
apply NNPP; red; intro.
contradiction H5.
exists x.
constructor.
intros.
apply NNPP; red; intro.
contradiction H7.
exists (Complement S).
constructor.
rewrite Complement_Complement; trivial.
exact H9.

destruct H3.
assert (In (FamilyUnion C) x).
rewrite H1; constructor.
destruct H4.
assert (In (Complement S) x).
destruct H3.
apply H3.
constructor.
rewrite Complement_Complement; trivial.
contradiction H6.
Qed.

Lemma compact_impl_filter_cluster_point:
  forall X:TopologicalSpace, compact X ->
    forall F:Filter (point_set X), exists x0:point_set X,
    filter_cluster_point F x0.
Proof.
intros.
pose proof (compact_finite_nonempty_closed_intersection
  _ H [ G:Ensemble (point_set X) | In (filter_family F) G /\
                                   closed G ]) as [x0].
intros.
destruct H0 as [[]]; trivial.
intros.
assert (closed (FamilyIntersection F')).
apply closed_family_intersection.
intros.
apply H1 in H2.
destruct H2 as [[]]; trivial.
assert (In (filter_family F) (FamilyIntersection F')).
clear H2.
induction H0.
rewrite empty_family_intersection.
apply filter_full.
replace (FamilyIntersection (Add A x)) with
  (Intersection (FamilyIntersection A) x).
apply filter_intersection.
apply IHFinite.
auto with sets.
assert (In (Add A x) x) by (right; constructor).
apply H1 in H3.
destruct H3 as [[]]; trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
constructor.
intros.
destruct H5.
destruct H3.
apply H3; trivial.
destruct H5; trivial.
destruct H3.
constructor.
constructor; intros.
apply H3.
auto with sets.
apply H3.
auto with sets.
apply NNPP; intro.
contradiction (filter_empty _ F).
replace (@Empty_set (point_set X)) with (FamilyIntersection F'); trivial.
apply Extensionality_Ensembles; split; red; intros.
contradiction H4.
exists x; trivial.
destruct H5.

exists x0.
red; intros.
destruct H0.
apply H0.
constructor.
split.
apply filter_upward_closed with S; trivial.
apply closure_inflationary.
apply closure_closed.
Qed.

Lemma filter_cluster_point_impl_compact:
  forall X:TopologicalSpace,
    (forall F:Filter (point_set X), exists x0:point_set X,
      filter_cluster_point F x0) -> compact X.
Proof.
intros.
apply finite_nonempty_closed_intersection_impl_compact.
intros.
unshelve refine (let H2:=_ in let filt := Build_Filter_from_subbasis F H2 in _).
intros.
rewrite indexed_to_family_intersection.
apply H1.
apply FiniteT_img; trivial.
intros; apply classic.
red; intros.
destruct H4.
rewrite H5; apply H3.
assert (filter_subbasis filt F) by apply filter_from_subbasis_subbasis.
destruct (H filt) as [x0].
exists x0.
constructor; intros.
assert (closed S) by (apply H0; trivial).
assert (In (filter_family filt) S).
apply (filter_subbasis_elements _ _ H3); trivial.
pose proof (H4 _ H7).
rewrite closure_fixes_closed in H8; trivial.
Qed.

Lemma ultrafilter_limit_impl_compact:
  forall X:TopologicalSpace,
    (forall U:Filter (point_set X), ultrafilter U ->
      exists x0:point_set X, filter_limit U x0) -> compact X.
Proof.
intros.
apply filter_cluster_point_impl_compact.
intros.
destruct (ultrafilter_extension F) as [U].
destruct H0.
destruct (H _ H1) as [x0].
exists x0.
red; intros.
apply filter_limit_is_cluster_point in H2.
apply H0 in H3.
apply H2; trivial.
Qed.

Lemma compact_impl_net_cluster_point:
  forall X:TopologicalSpace, compact X ->
    forall (I:DirectedSet) (x:Net I X), inhabited (DS_set I) ->
    exists x0:point_set X, net_cluster_point x x0.
Proof.
Require Import FiltersAndNets.
intros.
destruct (compact_impl_filter_cluster_point
  _ H (tail_filter x H0)) as [x0].
exists x0.
apply tail_filter_cluster_point_impl_net_cluster_point with H0.
apply H1.
Qed.

Lemma net_cluster_point_impl_compact: forall X:TopologicalSpace,
  (forall (I:DirectedSet) (x:Net I X), inhabited (DS_set I) ->
    exists x0:point_set X, net_cluster_point x x0) ->
  compact X.
Proof.
intros.
apply filter_cluster_point_impl_compact.
intros.
destruct (H _ (filter_to_net _ F)) as [x0].
cut (inhabited (point_set X)).
intro.
destruct H0 as [x].
exists.
simpl.
apply Build_filter_to_net_DS_set with Full_set x.
apply filter_full.
constructor.
apply NNPP; intro.
contradiction (filter_empty _ F).
replace (@Empty_set (point_set X)) with (@Full_set (point_set X)).
apply filter_full.
apply Extensionality_Ensembles; split; red; intros.
contradiction H0.
exists; exact x.
destruct H1.

exists x0.
apply filter_to_net_cluster_point_impl_filter_cluster_point.
trivial.
Qed.

Require Export SeparatednessAxioms.
Require Export SubspaceTopology.

Lemma compact_closed: forall (X:TopologicalSpace)
  (S:Ensemble (point_set X)), Hausdorff X ->
  compact (SubspaceTopology S) -> closed S.
Proof.
intros.
destruct (classic (Inhabited S)).
assert (closure S = S).
apply Extensionality_Ensembles; split.
red; intros.
destruct (net_limits_determine_topology _ _ H2) as [I0 [y []]].
pose (yS (i:DS_set I0) := exist (fun x:point_set X => In S x) (y i) (H3 i)).
assert (inhabited (point_set (SubspaceTopology S))).
destruct H1.
exists.
exists x0; trivial.
assert (inhabited (DS_set I0)) as HinhI0.
red in H4.
destruct (H4 Full_set) as [i0]; auto with topology.
constructor.
pose proof (compact_impl_net_cluster_point
  (SubspaceTopology S) H0 _ yS HinhI0).
destruct H6 as [[x0]].
apply net_cluster_point_impl_subnet_converges in H6.
destruct H6 as [J [y' []]].
destruct H6.
assert (net_limit (fun j:DS_set J => y (h j)) x0).
apply continuous_func_preserves_net_limits with
  (f:=subspace_inc S) (Y:=X) in H7.
simpl in H7.
assumption.
apply continuous_func_continuous_everywhere.
apply subspace_inc_continuous.
assert (net_limit (fun j:DS_set J => y (h j)) x).
apply subnet_limit with I0 y; trivial.
constructor; trivial.
assert (x = x0).
exact (Hausdorff_impl_net_limit_unique _ H _ _ H10 H9).
rewrite H11; trivial.
destruct (H4 Full_set).
apply open_full.
constructor.
exists; exact x1.
destruct H1.

apply closure_inflationary.
rewrite <- H2; apply closure_closed.

red.
assert (Complement S = Full_set).
apply Extensionality_Ensembles; split; red; intros.
constructor.
red; intro.
contradiction H1; exists x; trivial.
rewrite H2; apply open_full.
Qed.

Lemma closed_compact: forall (X:TopologicalSpace) (S:Ensemble (point_set X)),
  compact X -> closed S -> compact (SubspaceTopology S).
Proof.
intros.
apply net_cluster_point_impl_compact.
intros.
destruct (compact_impl_net_cluster_point _ H
  _ (fun i:DS_set I => subspace_inc _ (x i))) as [x0].
trivial.
assert (In S x0).
rewrite <- (closure_fixes_closed S); trivial.
apply net_cluster_point_in_closure with
  (2:=H2).
destruct H1 as [i0].
exists i0.
intros.
destruct (x j).
simpl.
trivial.
exists (exist _ x0 H3).
red; intros.
red; intros.
destruct (subspace_topology_topology _ _ _ H4) as [V []].
rewrite H7 in H5.
destruct H5.
simpl in H5.
destruct (H2 V H6 H5 i) as [j []]; trivial.
exists j; split; trivial.
rewrite H7.
constructor.
trivial.
Qed.

Lemma compact_image: forall {X Y:TopologicalSpace}
  (f:point_set X->point_set Y),
  compact X -> continuous f -> surjective f -> compact Y.
Proof.
intros.
red; intros.
pose (B := fun U:{U:Ensemble (point_set Y) | In C U} =>
           inverse_image f (proj1_sig U)).
destruct (compactness_on_indexed_covers _ _ B H) as [subcover].
destruct a as [U].
unfold B; simpl.
apply H0.
apply H2; trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
assert (In (FamilyUnion C) (f x)).
rewrite H3; constructor.
inversion_clear H5 as [V].
exists (exist _ V H6).
unfold B; simpl.
constructor; trivial.
destruct H4.

exists (Im subcover (@proj1_sig _ (fun U:Ensemble (point_set Y) => In C U))).
repeat split.
apply finite_image; trivial.
red; intros V ?.
destruct H6 as [[U]].
simpl in H7.
congruence.
apply Extensionality_Ensembles; split; red; intros y ?.
constructor.
destruct (H1 y) as [x].
assert (In (IndexedUnion
  (fun a':{a' | In subcover a'} => B (proj1_sig a'))) x).
rewrite H5; constructor.
destruct H8 as [[[U]]].
exists U.
simpl in H8.
exists (exist _ U i); trivial.
unfold B in H8; simpl in H8.
destruct H8.
congruence.
Qed.

Lemma compact_Hausdorff_impl_normal_sep: forall X:TopologicalSpace,
  compact X -> Hausdorff X -> normal_sep X.
Proof.
intros.
assert (T3_sep X).
Require Import ClassicalChoice.
destruct (choice (fun (xy:{xy:point_set X * point_set X |
                  let (x,y):=xy in x <> y})
  (UV:Ensemble (point_set X) * Ensemble (point_set X)) =>
  match xy with | exist (x,y) i =>
    let (U,V):=UV in
  open U /\ open V /\ In U x /\ In V y /\ Intersection U V = Empty_set
  end)) as
[choice_fun].
destruct x as [[x y] i].
destruct (H0 _ _ i) as [U [V]].
exists (U, V); trivial.

pose (choice_fun_U := fun (x y:point_set X)
  (Hineq:x<>y) => fst (choice_fun (exist _ (x,y) Hineq))).
pose (choice_fun_V := fun (x y:point_set X)
  (Hineq:x<>y) => snd (choice_fun (exist _ (x,y) Hineq))).
assert (forall (x y:point_set X) (Hineq:x<>y),
  open (choice_fun_U x y Hineq) /\
  open (choice_fun_V x y Hineq) /\
  In (choice_fun_U x y Hineq) x /\
  In (choice_fun_V x y Hineq) y /\
  Intersection (choice_fun_U x y Hineq) (choice_fun_V x y Hineq) = Empty_set).
intros.
unfold choice_fun_U; unfold choice_fun_V.
pose proof (H1 (exist _ (x,y) Hineq)).
destruct (choice_fun (exist _ (x,y) Hineq)).
exact H2.
clearbody choice_fun_U choice_fun_V; clear choice_fun H1.

split.
apply Hausdorff_impl_T1_sep; trivial.
intros.
pose proof (closed_compact _ _ H H1).
assert (forall y:point_set X, In F y -> x <> y).
intros.
congruence.
pose (cover := fun (y:point_set (SubspaceTopology F)) =>
  let (y,i):=y in inverse_image (subspace_inc F)
                     (choice_fun_V x y (H5 y i))).
destruct (compactness_on_indexed_covers _ _ cover H4) as [subcover].
destruct a as [y i].
apply subspace_inc_continuous.
apply H2.
apply Extensionality_Ensembles; split; red; intros y ?.
constructor.
exists y.
destruct y as [y i].
simpl.
constructor.
simpl.
apply H2.
destruct H6.

exists (IndexedIntersection
  (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
    let (y,_):=y in let (y,i):=y in choice_fun_U x y (H5 y i))).
exists (IndexedUnion
  (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
    let (y,_):=y in let (y,i):=y in choice_fun_V x y (H5 y i))).
repeat split.
apply open_finite_indexed_intersection.
apply Finite_ens_type; trivial.
destruct a as [[y]].
apply H2.
apply open_indexed_union.
destruct a as [[y]].
apply H2.
destruct a as [[y]].
apply H2.
red; intros y ?.
assert (In (IndexedUnion
  (fun y:{y:point_set (SubspaceTopology F) | In subcover y} =>
    cover (proj1_sig y))) (exist _ y H8)).
rewrite H7; constructor.
remember (exist (In F) y H8) as ysig.
destruct H9 as [[y']].
rewrite Heqysig in H9; clear x0 Heqysig.
simpl in H9.
destruct y' as [y'].
simpl in H9.
destruct H9.
simpl in H9.
exists (exist _ (exist _ y' i0) i).
trivial.

apply Extensionality_Ensembles; split; auto with sets; red; intros y ?.
destruct H8.
destruct H8.
destruct H9.
pose proof (H8 a).
destruct a as [[y]].
replace (@Empty_set (point_set X)) with
  (Intersection (choice_fun_U x y (H5 y i))
                (choice_fun_V x y (H5 y i))).
constructor; trivial.
apply H2.

destruct (choice (fun (xF:{p:point_set X * Ensemble (point_set X) |
                        let (x,F):=p in closed F /\ ~ In F x})
  (UV:Ensemble (point_set X) * Ensemble (point_set X)) =>
  let (p,i):=xF in let (x,F):=p in
  let (U,V):=UV in
  open U /\ open V /\ In U x /\ Included F V /\
  Intersection U V = Empty_set)) as [choice_fun].
destruct x as [[x F] []].
destruct H1.
destruct (H4 x F H2 H3) as [U [V]].
exists (U,V); trivial.

pose (choice_fun_U := fun (x:point_set X) (F:Ensemble (point_set X))
  (HC:closed F) (Hni:~ In F x) =>
  fst (choice_fun (exist _ (x,F) (conj HC Hni)))).
pose (choice_fun_V := fun (x:point_set X) (F:Ensemble (point_set X))
  (HC:closed F) (Hni:~ In F x) =>
  snd (choice_fun (exist _ (x,F) (conj HC Hni)))).
assert (forall (x:point_set X) (F:Ensemble (point_set X))
  (HC:closed F) (Hni:~ In F x),
  open (choice_fun_U x F HC Hni) /\
  open (choice_fun_V x F HC Hni) /\
  In (choice_fun_U x F HC Hni) x /\
  Included F (choice_fun_V x F HC Hni) /\
  Intersection (choice_fun_U x F HC Hni) (choice_fun_V x F HC Hni) =
     Empty_set).
intros.
pose proof (H2 (exist _ (x,F) (conj HC Hni))).
unfold choice_fun_U; unfold choice_fun_V;
  destruct (choice_fun (exist _ (x,F) (conj HC Hni))); trivial.
clearbody choice_fun_U choice_fun_V; clear choice_fun H2.
split.
apply H1.
intros.
pose proof (closed_compact _ _ H H2).
assert (forall x:point_set X, In F x -> ~ In G x).
intros.
intro.
absurd (In Empty_set x).
red; destruct 1.
rewrite <- H5; split; trivial.

pose (cover := fun x:point_set (SubspaceTopology F) =>
  let (x,i):=x in inverse_image (subspace_inc F)
                   (choice_fun_U x G H4 (H7 x i))).
destruct (compactness_on_indexed_covers _ _ cover H6) as [subcover].
destruct a as [x i].
apply subspace_inc_continuous.
apply H3.
apply Extensionality_Ensembles; split; red; intros.
constructor.
exists x.
destruct x.
simpl cover.
constructor.
simpl.
apply H3.
destruct H8.

exists (IndexedUnion
  (fun x:{x:point_set (SubspaceTopology F) | In subcover x} =>
     let (x,i):=proj1_sig x in choice_fun_U x G H4 (H7 x i))).
exists (IndexedIntersection
  (fun x:{x:point_set (SubspaceTopology F) | In subcover x} =>
     let (x,i):=proj1_sig x in choice_fun_V x G H4 (H7 x i))).
repeat split.
apply open_indexed_union.
destruct a as [[x]].
simpl.
apply H3.
apply open_finite_indexed_intersection.
apply Finite_ens_type; trivial.
destruct a as [[x]].
simpl.
apply H3.
intros x ?.
assert (In (@Full_set (point_set (SubspaceTopology F))) (exist _ x H10))
  by constructor.
rewrite <- H9 in H11.
remember (exist _ x H10) as xsig.
destruct H11.
destruct a as [x'].
destruct x' as [x'].
rewrite Heqxsig in H11; clear x0 Heqxsig.
simpl in H11.
destruct H11.
simpl in H11.
exists (exist _ (exist _ x' i0) i).
simpl.
trivial.
destruct a as [x'].
simpl.
destruct x' as [x'].
assert (Included G (choice_fun_V x' G H4 (H7 x' i0))) by apply H3.
auto.

apply Extensionality_Ensembles; split; auto with sets; red; intros.
destruct H10.
destruct H10.
destruct H11.
pose proof (H11 a).
destruct a as [[x']].
simpl in H12.
simpl in H10.
replace (@Empty_set (point_set X)) with (Intersection
  (choice_fun_U x' G H4 (H7 x' i))
  (choice_fun_V x' G H4 (H7 x' i))).
constructor; trivial.
apply H3.
Qed.
