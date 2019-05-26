Require Export TopologicalSpaces.
Require Export WeakTopology.
From ZornsLemma Require Import DependentTypeChoice.

Section product_topology.

Variable A:Type.
Variable X:forall a:A, TopologicalSpace.

Definition product_space_point_set : Type :=
  forall a:A, point_set (X a).
Definition product_space_proj (a:A) : product_space_point_set ->
                                      point_set (X a) :=
  fun (x:product_space_point_set) => x a.

Definition ProductTopology : TopologicalSpace :=
  WeakTopology product_space_proj.

Lemma product_space_proj_continuous: forall a:A,
  continuous (product_space_proj a) (X:=ProductTopology).
Proof.
apply weak_topology_makes_continuous_funcs.
Qed.

Lemma product_net_limit: forall (I:DirectedSet)
  (x:Net I ProductTopology) (x0:point_set ProductTopology),
  inhabited (DS_set I) ->
  (forall a:A, net_limit (fun i:DS_set I => x i a) (x0 a)) ->
  net_limit x x0.
Proof.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology;
  trivial.
Qed.

Require Export FilterLimits.

Lemma product_filter_limit:
  forall (F:Filter (point_set ProductTopology))
    (x0:point_set ProductTopology),
  (forall a:A, filter_limit (filter_direct_image
                     (product_space_proj a) F) (x0 a)) ->
  filter_limit F x0.
Proof.
intros.
assert (subbasis
  (weak_topology_subbasis product_space_proj)
  (X:=ProductTopology)).
apply Build_TopologicalSpace_from_subbasis_subbasis.
red; intros.
red; intros U ?.
destruct H1.
destruct H1 as [U' []].
cut (In (filter_family F) U').
intro.
apply filter_upward_closed with U'; trivial.
destruct H1.
destruct (subbasis_cover _ _ H0 _ _ H3 H1) as
  [B [? [V [? []]]]].
cut (In (filter_family F) (IndexedIntersection V)).
intro.
apply filter_upward_closed with (1:=H8); trivial.
apply filter_finite_indexed_intersection; trivial.

intro b.
pose proof (H5 b).
inversion H8.
apply H.
constructor.
apply open_neighborhood_is_neighborhood.
constructor; trivial.
destruct H6.
pose proof (H6 b).
rewrite <- H9 in H11.
destruct H11.
exact H11.
Qed.

Require Export Compactness.

Theorem TychonoffProductTheorem:
  (forall a:A, compact (X a)) -> compact ProductTopology.
Proof.
intro.
apply ultrafilter_limit_impl_compact; intros.
destruct (choice_on_dependent_type (fun (a:A) (x:point_set (X a)) =>
  filter_limit (filter_direct_image (product_space_proj a) U) x))
  as [choice_fun].
intro.
destruct (compact_impl_filter_cluster_point _ (H a)
  (filter_direct_image (product_space_proj a) U)) as [xa].
exists xa.
apply ultrafilter_cluster_point_is_limit; trivial.
red; intros.
destruct (H0 (inverse_image (product_space_proj a) S));
  [left | right]; constructor; try rewrite inverse_image_complement; trivial.
exists choice_fun.
apply product_filter_limit; trivial.
Qed.

End product_topology.

Arguments ProductTopology {A}.
Arguments product_space_proj {A} {X}.

Lemma product_map_continuous: forall {A:Type}
  (X:TopologicalSpace) (Y:A->TopologicalSpace)
  (f:forall a:A, point_set X -> point_set (Y a)) (x:point_set X),
  (forall a:A, continuous_at (f a) x) ->
  continuous_at (fun x:point_set X => (fun a:A => f a x)) x
    (Y:=ProductTopology Y).
Proof.
intros.
apply func_preserving_net_limits_is_continuous.
intros.
apply product_net_limit.
destruct (H0 Full_set) as [i].
apply open_full.
constructor.
exists; exact i.
intros.
apply continuous_func_preserves_net_limits; trivial.
Qed.

Section product_topology2.

(* we provide a version of the product topology on X and Y
   whose underlying set is point_set X * point_set Y, for
   more convenience as compared with the general definition *)
Variable X Y:TopologicalSpace.

Inductive twoT := | twoT_1 | twoT_2.
Let prod2_fun (i:twoT) := match i with
  | twoT_1 => X | twoT_2 => Y end.
Let prod2 := ProductTopology prod2_fun.

Let prod2_conv1 (p:point_set prod2) : point_set X * point_set Y :=
  (p twoT_1, p twoT_2).
Let prod2_conv2 (p : point_set X * point_set Y) : point_set prod2 :=
  let (x,y):=p in fun i:twoT => match i with
    | twoT_1 => x | twoT_2 => y
  end.

Lemma prod2_comp1: forall p:point_set prod2,
  prod2_conv2 (prod2_conv1 p) = p.
Proof.
intros.
Require Import FunctionalExtensionality.
extensionality i.
destruct i; trivial.
Qed.

Lemma prod2_comp2: forall p:point_set X * point_set Y,
  prod2_conv1 (prod2_conv2 p) = p.
Proof.
intros.
destruct p as [x y].
trivial.
Qed.

Let prod2_proj := fun i:twoT =>
  match i return (point_set X * point_set Y ->
                  point_set (prod2_fun i)) with
  | twoT_1 => @fst (point_set X) (point_set Y)
  | twoT_2 => @snd (point_set X) (point_set Y)
  end.

Definition ProductTopology2 : TopologicalSpace :=
  WeakTopology prod2_proj.

Lemma prod2_conv1_cont: continuous prod2_conv1 (Y:=ProductTopology2).
Proof.
apply pointwise_continuity.
intros p.
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
destruct (H Full_set).
apply open_full.
constructor.
exact (inhabits x0).
destruct a.
simpl.
apply net_limit_in_weak_topology_impl_net_limit_in_projections
  with (a:=twoT_1) in H.
exact H.
simpl.
apply net_limit_in_weak_topology_impl_net_limit_in_projections
  with (a:=twoT_2) in H.
exact H.
Qed.

Lemma prod2_conv2_cont: continuous prod2_conv2 (X:=ProductTopology2).
Proof.
apply pointwise_continuity.
destruct x as [x y].
apply func_preserving_net_limits_is_continuous.
intros.
apply net_limit_in_projections_impl_net_limit_in_weak_topology.
destruct (H Full_set).
apply open_full.
constructor.
exact (inhabits x1).
destruct a.
unfold product_space_proj.
simpl.
replace (fun i:DS_set I => prod2_conv2 (x0 i) twoT_1) with
  (fun i:DS_set I => fst (x0 i)).
apply net_limit_in_weak_topology_impl_net_limit_in_projections
  with (a:=twoT_1) in H.
simpl in H.
trivial.
extensionality i.
destruct (x0 i) as [xi yi].
trivial.
unfold product_space_proj.
simpl.
replace (fun i:DS_set I => prod2_conv2 (x0 i) twoT_2) with
  (fun i:DS_set I => snd (x0 i)).
apply net_limit_in_weak_topology_impl_net_limit_in_projections
  with (a:=twoT_2) in H.
simpl in H.
trivial.
extensionality i.
destruct (x0 i) as [xi yi].
trivial.
Qed.

Lemma product2_fst_continuous:
  continuous (@fst (point_set X) (point_set Y))
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_1).
Qed.

Lemma product2_snd_continuous:
  continuous (@snd (point_set X) (point_set Y))
    (X:=ProductTopology2).
Proof.
exact (weak_topology_makes_continuous_funcs
  _ _ _ prod2_proj twoT_2).
Qed.

Lemma product2_map_continuous: forall (W:TopologicalSpace)
  (f:point_set W -> point_set X) (g:point_set W -> point_set Y)
  (w:point_set W),
  continuous_at f w -> continuous_at g w ->
  continuous_at (fun w:point_set W => (f w, g w)) w
  (Y:=ProductTopology2).
Proof.
intros.
replace (fun w:point_set W => (f w, g w)) with
  (fun w:point_set W => prod2_conv1
              (fun i:twoT => match i with
                | twoT_1 => f w
                | twoT_2 => g w end)).
apply (@continuous_composition_at W prod2 ProductTopology2
  prod2_conv1
  (fun w:point_set W =>
     fun i:twoT => match i with
         | twoT_1 => f w | twoT_2 => g w end)).
apply continuous_func_continuous_everywhere.
apply prod2_conv1_cont.
apply product_map_continuous.
destruct a; trivial.
extensionality w0.
trivial.
Qed.

Inductive ProductTopology2_basis :
  Family (point_set ProductTopology2) :=
| intro_product2_basis_elt:
  forall (U:Ensemble (point_set X))
         (V:Ensemble (point_set Y)),
  open U -> open V ->
  In ProductTopology2_basis
  [ p:point_set ProductTopology2 |
    let (x,y):=p in (In U x /\ In V y) ].

Lemma ProductTopology2_basis_is_basis:
  open_basis ProductTopology2_basis.
Proof.
From ZornsLemma Require Import FiniteIntersections.
assert (open_basis (finite_intersections (weak_topology_subbasis prod2_proj))
  (X:=ProductTopology2)) by apply
  Build_TopologicalSpace_from_open_basis_basis.
apply eq_ind with (1:=H).
apply Extensionality_Ensembles; split; red; intros U ?.
induction H0.
replace (@Full_set (point_set X * point_set Y)) with
  [ p:point_set ProductTopology2 |
    let (x,y):=p in (In Full_set x /\ In Full_set y) ].
constructor; try apply open_full.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct x.
constructor; split; constructor.
destruct H0.
destruct a.
replace (inverse_image (prod2_proj twoT_1) V) with
  [ p:point_set ProductTopology2 |
    let (x,y):=p in (In V x /\ In Full_set y) ].
constructor; trivial.
apply open_full.
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct x.
destruct H1.
constructor.
trivial.
destruct H1.
destruct x.
constructor.
split; trivial.
constructor.
replace (inverse_image (prod2_proj twoT_2) V) with
  [ p:point_set ProductTopology2 |
    let (x,y):=p in (In Full_set x /\ In V y) ].
constructor; trivial.
apply open_full.
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
destruct x.
destruct H1.
constructor.
trivial.
destruct H1.
destruct x.
constructor.
split.
constructor.
trivial.

destruct IHfinite_intersections as [U1 V1].
destruct IHfinite_intersections0 as [U2 V2].
replace (@Intersection (point_set X * point_set Y)
  [p:point_set ProductTopology2 | let (x,y):=p in In U1 x /\ In V1 y]
  [p:point_set ProductTopology2 | let (x,y):=p in In U2 x /\ In V2 y])
with
  [p:point_set ProductTopology2 | let (x,y):=p in
   (In (Intersection U1 U2) x /\ In (Intersection V1 V2) y)].
constructor; apply open_intersection2; trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H6.
destruct x.
destruct H6.
destruct H6.
destruct H7.
constructor.
constructor.
split; trivial.
constructor.
split; trivial.
destruct H6.
destruct H6.
destruct H7.
destruct x.
destruct H6.
destruct H7.
constructor.
split; constructor; trivial.

destruct H0.
replace [p:point_set ProductTopology2 | let (x,y):=p in
         In U x /\ In V y] with
  (Intersection (inverse_image (prod2_proj twoT_1) U)
                (inverse_image (prod2_proj twoT_2) V)).
constructor 3.
constructor.
constructor; trivial.
constructor.
constructor; trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H2.
destruct H2.
destruct H3.
constructor.
destruct x.
split; trivial.
destruct H2.
destruct x.
destruct H2.
constructor; constructor; trivial.
Qed.

End product_topology2.

Section two_arg_convenience_results.

Variable X Y Z:TopologicalSpace.
Variable f:point_set X -> point_set Y -> point_set Z.

Definition continuous_2arg :=
  continuous (fun p:point_set X * point_set Y =>
              let (x,y):=p in f x y)
  (X:=ProductTopology2 X Y).
Definition continuous_at_2arg (x:point_set X) (y:point_set Y) :=
  continuous_at (fun p:point_set X * point_set Y =>
                 let (x,y):=p in f x y)  (x, y)
  (X:=ProductTopology2 X Y).

Lemma continuous_2arg_func_continuous_everywhere:
  continuous_2arg -> forall (x:point_set X) (y:point_set Y),
                       continuous_at_2arg x y.
Proof.
intros.
apply continuous_func_continuous_everywhere; trivial.
Qed.

Lemma pointwise_continuity_2arg:
  (forall (x:point_set X) (y:point_set Y),
   continuous_at_2arg x y) -> continuous_2arg.
Proof.
intros.
apply pointwise_continuity.
intros.
destruct x as [x y].
apply H.
Qed.

End two_arg_convenience_results.

Arguments continuous_2arg {X} {Y} {Z}.
Arguments continuous_at_2arg {X} {Y} {Z}.

Lemma continuous_composition_at_2arg:
  forall (W X Y Z:TopologicalSpace)
    (f:point_set X -> point_set Y -> point_set Z)
    (g:point_set W -> point_set X) (h:point_set W -> point_set Y)
    (w:point_set W),
  continuous_at_2arg f (g w) (h w) ->
  continuous_at g w -> continuous_at h w ->
  continuous_at (fun w:point_set W => f (g w) (h w)) w.
Proof.
intros.
apply (continuous_composition_at
  (fun p:point_set (ProductTopology2 X Y) =>
      let (x,y):=p in f x y)
  (fun w:point_set W => (g w, h w))).
exact H.
apply product2_map_continuous; trivial.
Qed.
