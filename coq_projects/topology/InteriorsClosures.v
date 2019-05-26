Require Export TopologicalSpaces.
From ZornsLemma Require Export EnsemblesSpec.

Section interior_closure.

Variable X:TopologicalSpace.
Variable S:Ensemble (point_set X).

Definition interior := FamilyUnion
  [ U:Ensemble (point_set X) | open U /\ Included U S ].
Definition closure := FamilyIntersection
  [ F:Ensemble (point_set X) | closed F /\ Included S F ].

Lemma interior_open : open interior.
Proof.
apply open_family_union.
intros.
destruct H as [[]]; trivial.
Qed.

Lemma interior_deflationary : Included interior S.
Proof.
red; intros.
destruct H.
destruct H as [[]]; auto with sets.
Qed.

Lemma interior_fixes_open: open S -> interior = S.
Proof.
intros.
apply Extensionality_Ensembles; split.
apply interior_deflationary.
red; intros.
exists S; trivial.
constructor; auto with sets.
Qed.

Lemma interior_maximal: forall U:Ensemble (point_set X),
  open U -> Included U S -> Included U interior.
Proof.
intros.
red; intros.
exists U; trivial.
constructor; split; trivial.
Qed.

Lemma closure_closed : closed closure.
Proof.
apply closed_family_intersection.
intros.
destruct H as [[]]; trivial.
Qed.

Lemma closure_inflationary : Included S closure.
Proof.
red; intros.
constructor; intros.
destruct H0 as [[]].
auto with sets.
Qed.

Lemma closure_fixes_closed : closed S -> closure = S.
Proof.
intro.
apply Extensionality_Ensembles; split.
red; intros.
destruct H0.
apply H0; split; auto with sets.
apply closure_inflationary.
Qed.

Lemma closure_minimal: forall F:Ensemble (point_set X),
  closed F -> Included S F -> Included closure F.
Proof.
intros; red; intros.
destruct H1.
apply H1.
constructor; split; trivial.
Qed.

End interior_closure.

Arguments interior {X}.
Arguments closure {X}.
Arguments interior_open {X}.
Arguments interior_deflationary {X}.
Arguments interior_fixes_open {X}.
Arguments interior_maximal {X}.
Arguments closure_closed {X}.
Arguments closure_inflationary {X}.
Arguments closure_fixes_closed {X}.
Arguments closure_minimal {X}.

Section interior_closure_relations.

Variable X:TopologicalSpace.

Lemma interior_increasing: forall S T:Ensemble (point_set X),
  Included S T -> Included (interior S) (interior T).
Proof.
intros.
apply interior_maximal.
apply interior_open.
assert (Included (interior S) S).
apply interior_deflationary.
auto with sets.
Qed.

Lemma interior_intersection: forall S T:Ensemble (point_set X),
  interior (Intersection S T) =
  Intersection (interior S) (interior T).
Proof.
intros.
apply Extensionality_Ensembles; split.
assert (Included (interior (Intersection S T)) (interior S)).
apply interior_increasing.
auto with sets.
assert (Included (interior (Intersection S T)) (interior T)).
apply interior_increasing.
auto with sets.
auto with sets.

apply interior_maximal.
apply open_intersection2; apply interior_open.
pose proof (interior_deflationary S).
pose proof (interior_deflationary T).
red; intros x H1; constructor; (apply H || apply H0);
destruct H1; trivial.
Qed.

Lemma interior_union: forall S T:Ensemble (point_set X),
  Included (Union (interior S) (interior T))
           (interior (Union S T)).
Proof.
intros.
apply interior_maximal.
apply open_union2; apply interior_open.
pose proof (interior_deflationary S).
pose proof (interior_deflationary T).
auto with sets.
Qed.

Lemma complement_inclusion: forall {Y:Type} (S T:Ensemble Y),
  Included S T -> Included (Complement T) (Complement S).
Proof.
intros.
red; intros.
red; intro.
contradiction H0.
auto with sets.
Qed.

Lemma interior_complement: forall S:Ensemble (point_set X),
  interior (Complement S) = Complement (closure S).
Proof.
intros.
apply Extensionality_Ensembles; split.
rewrite <- Complement_Complement with (A:=interior (Complement S)).
apply complement_inclusion.
apply closure_minimal.
red.
rewrite Complement_Complement.
apply interior_open.
pattern S at 1;
rewrite <- Complement_Complement with (A:=S).
apply complement_inclusion.
apply interior_deflationary.

apply interior_maximal.
apply closure_closed.
apply complement_inclusion.
apply closure_inflationary.
Qed.

Lemma closure_increasing: forall S T:Ensemble (point_set X),
  Included S T -> Included (closure S) (closure T).
Proof.
intros.
apply closure_minimal.
apply closure_closed.
pose proof (closure_inflationary T).
auto with sets.
Qed.

Lemma closure_complement: forall S:Ensemble (point_set X),
  closure (Complement S) = Complement (interior S).
Proof.
intros.
pose proof (interior_complement (Complement S)).
rewrite Complement_Complement in H.
rewrite H.
rewrite Complement_Complement; reflexivity.
Qed.

Lemma closure_union: forall S T:Ensemble (point_set X),
  closure (Union S T) = Union (closure S) (closure T).
Proof.
intros.
apply Extensionality_Ensembles; split.
apply closure_minimal.
apply closed_union2; apply closure_closed.
pose proof (closure_inflationary S).
pose proof (closure_inflationary T).
auto with sets.

assert (Included (closure S) (closure (Union S T))).
apply closure_increasing; auto with sets.
assert (Included (closure T) (closure (Union S T))).
apply closure_increasing; auto with sets.
auto with sets.
Qed.

Lemma closure_intersection: forall S T:Ensemble (point_set X),
  Included (closure (Intersection S T))
           (Intersection (closure S) (closure T)).
Proof.
intros.
assert (Included (closure (Intersection S T)) (closure S)).
apply closure_increasing; auto with sets.
assert (Included (closure (Intersection S T)) (closure T)).
apply closure_increasing; auto with sets.
auto with sets.
Qed.

Lemma meets_every_open_neighborhood_impl_closure:
  forall (S:Ensemble (point_set X)) (x:point_set X),
  (forall U:Ensemble (point_set X), open U -> In U x ->
                                Inhabited (Intersection S U)) ->
  In (closure S) x.
Proof.
intros.
apply NNPP; intro.
pose proof (H (Complement (closure S))).
destruct H1.
apply closure_closed.
exact H0.
destruct H1.
contradiction H2.
apply closure_inflationary.
assumption.
Qed.

Lemma closure_impl_meets_every_open_neighborhood:
  forall (S:Ensemble (point_set X)) (x:point_set X),
  In (closure S) x ->
  forall U:Ensemble (point_set X), open U -> In U x ->
    Inhabited (Intersection S U).
Proof.
intros.
apply NNPP; intro.
assert (Included (closure S) (Complement U)).
apply closure_minimal.
unfold closed.
rewrite Complement_Complement; assumption.
red; intros.
intro.
contradiction H2.
exists x0; constructor; trivial.

contradict H1.
apply H3.
assumption.
Qed.

Definition dense (S:Ensemble (point_set X)) : Prop :=
  closure S = Full_set.

Lemma dense_meets_every_nonempty_open:
  forall S:Ensemble (point_set X), dense S ->
    forall U:Ensemble (point_set X), open U -> Inhabited U ->
    Inhabited (Intersection S U).
Proof.
intros.
destruct H1.
apply closure_impl_meets_every_open_neighborhood with x; trivial.
rewrite H; constructor.
Qed.

Lemma meets_every_nonempty_open_impl_dense:
  forall S:Ensemble (point_set X),
  (forall U:Ensemble (point_set X), open U -> Inhabited U ->
   Inhabited (Intersection S U)) ->
  dense S.
Proof.
intros.
apply Extensionality_Ensembles; split; red; intros.
constructor.
apply meets_every_open_neighborhood_impl_closure.
intros.
apply H; trivial.
exists x; trivial.
Qed.

End interior_closure_relations.

Arguments interior_increasing {X}.
Arguments interior_intersection {X}.
Arguments interior_union {X}.
Arguments interior_complement {X}.
Arguments closure_increasing {X}.
Arguments closure_complement {X}.
Arguments closure_union {X}.
Arguments closure_intersection {X}.
Arguments dense {X}.

Section Build_from_closure.

Variable X:Type.
Variable cl : Ensemble X -> Ensemble X.
Hypothesis cl_inflationary: forall S:Ensemble X,
  Included S (cl S).
Hypothesis cl_respects_union: forall S1 S2:Ensemble X,
  cl (Union S1 S2) = Union (cl S1) (cl S2).
Hypothesis cl_empty: cl Empty_set = Empty_set.
Hypothesis cl_idempotent: forall S:Ensemble X,
  cl (cl S) = cl S.

Lemma cl_increasing: forall S1 S2:Ensemble X,
  Included S1 S2 -> Included (cl S1) (cl S2).
Proof.
intros.
replace S2 with (Union S1 S2).
rewrite cl_respects_union.
auto with sets.
apply Extensionality_Ensembles; split; auto with sets.
Qed.

Definition Build_TopologicalSpace_from_closure_operator : TopologicalSpace.
refine (Build_TopologicalSpace_from_closed_sets
  (fun F => cl F = F) _ _ _).
apply cl_empty.
intros.
rewrite cl_respects_union; congruence.
intros.
apply Extensionality_Ensembles; split; try apply cl_inflationary.
red; intros.
constructor; intros.
rewrite <- (H S H1).
apply cl_increasing with (FamilyIntersection F); trivial.
red; intros.
destruct H2.
apply H2; trivial.
Defined.

Lemma Build_TopologicalSpace_from_closure_operator_closure:
  forall S:Ensemble (point_set Build_TopologicalSpace_from_closure_operator),
    closure S = cl S.
Proof.
intros.
apply Extensionality_Ensembles; split.
apply closure_minimal.
apply <- Build_TopologicalSpace_from_closed_sets_closed.
apply cl_idempotent.
trivial.
replace (closure S) with (cl (closure S)).
apply cl_increasing.
apply (closure_inflationary S).
pose proof (closure_closed S).
apply -> Build_TopologicalSpace_from_closed_sets_closed in H.
exact H.
Qed.

End Build_from_closure.

Arguments Build_TopologicalSpace_from_closure_operator {X}.
