Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Families.
Require Export FiniteTypes.
Require Export IndexedFamilies.

Inductive finite_intersections {X:Type} (S:Family X) : Family X :=
  | intro_full: In (finite_intersections S) Full_set
  | intro_S: forall U:Ensemble X, In S U -> In (finite_intersections S) U
  | intro_intersection: forall U V:Ensemble X,
    In (finite_intersections S) U -> In (finite_intersections S) V ->
    In (finite_intersections S) (Intersection U V).

Lemma finite_intersection_is_finite_indexed_intersection:
  forall {X:Type} (S:Family X) (U:Ensemble X),
  In (finite_intersections S) U -> exists J:Type, FiniteT J /\
  exists V:J->Ensemble X,
  (forall j:J, In S (V j)) /\ U = IndexedIntersection V.
Proof.
intros.
induction H.
exists False.
split.
constructor.
exists (False_rect _).
split.
destruct j.
symmetry; apply empty_indexed_intersection.

exists True.
split.
exact True_finite.
exists (True_rect U).
split.
destruct j.
simpl.
trivial.
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct a; simpl.
trivial.
destruct H0.
exact (H0 I).
destruct IHfinite_intersections as [J0 [? [W []]]].
destruct IHfinite_intersections0 as [J1 [? [W' []]]].
exists ((J0+J1)%type).
split.
apply finite_sum; trivial.
exists (fun s:J0+J1 => match s with
  | inl j => W j
  | inr j => W' j
end).
split.
destruct j; auto.
apply Extensionality_Ensembles; split; red; intros.
destruct H7.
rewrite H3 in H7; destruct H7.
rewrite H6 in H8; destruct H8.
constructor.
destruct a as [j|j]; auto.
destruct H7.
constructor.
rewrite H3; constructor.
intro j.
exact (H7 (inl _ j)).
rewrite H6; constructor.
intro j.
exact (H7 (inr _ j)).
Qed.

Lemma finite_indexed_intersection_is_finite_intersection:
  forall {X:Type} (S:Family X) (J:Type) (V:J->Ensemble X),
  FiniteT J -> (forall j:J, In S (V j)) ->
  In (finite_intersections S) (IndexedIntersection V).
Proof.
intros.
induction H.
rewrite empty_indexed_intersection.
constructor.

assert (IndexedIntersection V = Intersection
  (IndexedIntersection (fun j:T => V (Some j)))
  (V None)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
constructor.
constructor.
trivial.
trivial.
destruct H1.
constructor.
destruct H1.
destruct a as [j|]; trivial.
rewrite H1.
constructor 3; auto.
constructor 2; trivial.

destruct H1 as [g].
assert (IndexedIntersection V =
  IndexedIntersection (fun x:X0 => V (f x))).
apply Extensionality_Ensembles; split; red; intros.
destruct H3.
constructor.
trivial.
destruct H3.
constructor.
intro.
rewrite <- (H2 a).
trivial.
rewrite H3; auto.
Qed.
