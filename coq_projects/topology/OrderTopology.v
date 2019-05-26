Require Export Subbases.
From ZornsLemma Require Export Relation_Definitions_Implicit.
Require Export SeparatednessAxioms.

Section OrderTopology.

Variable X:Type.
Variable R:relation X.
Hypothesis R_ord: order R.

Inductive order_topology_subbasis : Family X :=
  | intro_lower_interval: forall x:X,
    In order_topology_subbasis [ y:X | R y x /\ y <> x ]
  | intro_upper_interval: forall x:X,
    In order_topology_subbasis [ y:X | R x y /\ y <> x].

Definition OrderTopology : TopologicalSpace :=
  Build_TopologicalSpace_from_subbasis X order_topology_subbasis.

Section if_total_order.

Hypothesis R_total: forall x y:X, R x y \/ R y x.

Lemma lower_closed_interval_closed: forall x:X,
  closed [ y:X | R y x ] (X:=OrderTopology).
Proof.
intro.
red.
match goal with |- open ?U => cut (U = interior U) end.
intro.
rewrite H; apply interior_open.
apply Extensionality_Ensembles; split.
2:apply interior_deflationary.
intros y ?.
red in H.
red in H.
assert (R x y).
destruct (R_total x y); trivial.
contradiction H.
constructor; trivial.
exists ([z:X | R x z /\ z <> x]).
constructor; split.
apply (Build_TopologicalSpace_from_subbasis_subbasis
  _ order_topology_subbasis).
constructor.
red; intros z ?.
destruct H1.
destruct H1.
intro.
destruct H3.
contradiction H2.
apply (ord_antisym R_ord); trivial.
constructor.
split; trivial.
intro.
contradiction H.
constructor.
destruct H1; apply (ord_refl R_ord).
Qed.

Lemma upper_closed_interval_closed: forall x:X,
  closed [y:X | R x y] (X:=OrderTopology).
Proof.
intro.
red.
match goal with |- open ?U => cut (U = interior U) end.
intro.
rewrite H; apply interior_open.
apply Extensionality_Ensembles; split.
2:apply interior_deflationary.
intros y ?.
red in H.
red in H.
assert (R y x).
destruct (R_total x y); trivial.
contradiction H.
constructor; trivial.
exists ([z:X | R z x /\ z <> x]).
constructor; split.
apply (Build_TopologicalSpace_from_subbasis_subbasis
  _ order_topology_subbasis).
constructor.
red; intros z ?.
destruct H1.
destruct H1.
intro.
destruct H3.
contradiction H2.
apply (ord_antisym R_ord); trivial.
constructor.
split; trivial.
intro.
contradiction H.
constructor.
destruct H1; apply (ord_refl R_ord).
Qed.

Lemma order_topology_Hausdorff: Hausdorff OrderTopology.
Proof.
red.
match goal with |- forall x y:point_set OrderTopology, ?P =>
  cut (forall x y:point_set OrderTopology, R x y -> P)
  end.
intros.
destruct (R_total x y).
exact (H x y H1 H0).
assert (y <> x).
auto.
destruct (H y x H1 H2) as [V [U [? [? [? []]]]]].
exists U; exists V; repeat split; trivial.
transitivity (Intersection V U); trivial.
apply Extensionality_Ensembles; split; red; intros.
destruct H8; constructor; trivial.
destruct H8; constructor; trivial.

intros.
pose proof (Build_TopologicalSpace_from_subbasis_subbasis
  _ order_topology_subbasis).
destruct (classic (exists z:X, R x z /\ R z y /\ z <> x /\ z <> y)).
destruct H2 as [z [? [? []]]].
exists ([w:X | R w z /\ w <> z]);
exists ([w:X | R z w /\ w <> z]).
repeat split; trivial.
apply H1.
constructor.
apply H1.
constructor.
auto.
auto.
apply Extensionality_Ensembles; split; red; intros.
destruct H6.
destruct H6.
destruct H7.
destruct H6.
destruct H7.
contradiction H8.
apply (ord_antisym R_ord); trivial.
destruct H6.

exists ([w:X | R w y /\ w <> y]);
exists ([w:X | R x w /\ w <> x]).
repeat split.
apply H1.
constructor.
apply H1.
constructor.
trivial.
trivial.
trivial.
auto.
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
destruct H3.
destruct H4.
destruct H3.
destruct H4.
contradiction H2.
exists x0; repeat split; trivial.
destruct H3.
Qed.

End if_total_order.

End OrderTopology.

Arguments OrderTopology {X}.
