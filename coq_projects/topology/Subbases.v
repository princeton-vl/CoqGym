Require Export TopologicalSpaces.
Require Export OpenBases.
From ZornsLemma Require Export FiniteTypes.
From ZornsLemma Require Export EnsemblesSpec.

Section Subbasis.

Variable X:TopologicalSpace.
Variable SB:Family (point_set X).

Record subbasis : Prop := {
  subbasis_elements: forall U:Ensemble (point_set X),
    In SB U -> open U;
  subbasis_cover: forall (U:Ensemble (point_set X)) (x:point_set X),
    In U x -> open U ->
    exists A:Type, FiniteT A /\
    exists V:A->Ensemble (point_set X),
      (forall a:A, In SB (V a)) /\
      In (IndexedIntersection V) x /\
      Included (IndexedIntersection V) U
}.

Lemma open_basis_is_subbasis: open_basis SB -> subbasis.
Proof.
intros.
destruct H.
constructor.
exact open_basis_elements.
intros.
destruct (open_basis_cover x U); trivial.
destruct H1 as [? [? ?]].
exists True.
split.
apply True_finite.
exists (True_rect x0).
repeat split; intros.
destruct a.
simpl.
assumption.
destruct a.
simpl.
assumption.
red; intros.
destruct H4.
apply H2.
exact (H4 I).
Qed.

Lemma finite_intersections_of_subbasis_form_open_basis:
  subbasis ->
  open_basis [ U:Ensemble (point_set X) |
              exists A:Type, FiniteT A /\
              exists V:A->Ensemble (point_set X),
              (forall a:A, In SB (V a)) /\
              U = IndexedIntersection V ].
Proof.
constructor.
intros.
destruct H0.
destruct H0 as [A [? [V' [? ?]]]].
rewrite H2.
apply open_finite_indexed_intersection; trivial.
intros.
apply H; trivial.

intros.
pose proof (subbasis_cover H U x).
destruct H2 as [A [? [V [? [? ?]]]]]; trivial.
exists (IndexedIntersection V).
repeat split; trivial.
exists A; split; trivial.
exists V; trivial.
split; trivial.
destruct H4.
exact H4.
Qed.

End Subbasis.

Arguments subbasis {X}.

Section build_from_subbasis.

Variable X:Type.
Variable S:Family X.

From ZornsLemma Require Import FiniteIntersections.

Definition Build_TopologicalSpace_from_subbasis : TopologicalSpace.
refine (Build_TopologicalSpace_from_open_basis
  (finite_intersections S) _ _).
red; intros.
exists (Intersection U V); repeat split; trivial.
apply intro_intersection; trivial.
destruct H1; assumption.
destruct H1; assumption.
destruct H2; assumption.
destruct H2; assumption.

red; intro.
exists Full_set.
split; constructor.
Defined.

Lemma Build_TopologicalSpace_from_subbasis_subbasis:
  @subbasis Build_TopologicalSpace_from_subbasis S.
Proof.
assert (@open_basis Build_TopologicalSpace_from_subbasis
  (finite_intersections S)).
apply Build_TopologicalSpace_from_open_basis_basis.
constructor.
intros.
simpl in U.
apply open_basis_elements with (finite_intersections S); trivial.
constructor; trivial.

intros.
destruct (@open_basis_cover _ _ H x U) as [V]; trivial.
destruct H2 as [? [? ?]].
simpl.

pose proof (finite_intersection_is_finite_indexed_intersection
  _ _ H2).
destruct H5 as [A [? [W [? ?]]]].
exists A; split; trivial.
exists W; repeat split; trivial.

rewrite H7 in H4; destruct H4; apply H4.
rewrite H7 in H3; assumption.
Qed.

End build_from_subbasis.
