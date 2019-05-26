Require Export Ensembles.
From ZornsLemma Require Import EnsemblesImplicit.
From ZornsLemma Require Export Families.
From ZornsLemma Require Export IndexedFamilies.
From ZornsLemma Require Export FiniteTypes.
From ZornsLemma Require Import EnsemblesSpec.

Record TopologicalSpace : Type := {
  point_set : Type;
  open : Ensemble point_set -> Prop;
  open_family_union : forall F : Family point_set,
    (forall S : Ensemble point_set, In F S -> open S) ->
    open (FamilyUnion F);
  open_intersection2: forall U V:Ensemble point_set,
    open U -> open V -> open (Intersection U V);
  open_full : open Full_set
}.

Arguments open {t}.
Arguments open_family_union {t}.
Arguments open_intersection2 {t}.

Lemma open_empty: forall X:TopologicalSpace,
  open (@Empty_set (point_set X)).
Proof.
intros.
rewrite <- empty_family_union.
apply open_family_union.
intros.
destruct H.
Qed.

Lemma open_union2: forall {X:TopologicalSpace}
  (U V:Ensemble (point_set X)), open U -> open V -> open (Union U V).
Proof.
intros.
assert (Union U V = FamilyUnion (Couple U V)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
exists U; auto with sets.
exists V; auto with sets.
destruct H1.
destruct H1.
left; trivial.
right; trivial.

rewrite H1; apply open_family_union.
intros.
destruct H2; trivial.
Qed.

Lemma open_indexed_union: forall {X:TopologicalSpace} {A:Type}
  (F:IndexedFamily A (point_set X)),
  (forall a:A, open (F a)) -> open (IndexedUnion F).
Proof.
intros.
rewrite indexed_to_family_union.
apply open_family_union.
intros.
destruct H0.
rewrite H1; apply H.
Qed.

Lemma open_finite_indexed_intersection:
  forall {X:TopologicalSpace} {A:Type}
    (F:IndexedFamily A (point_set X)),
    FiniteT A -> (forall a:A, open (F a)) ->
    open (IndexedIntersection F).
Proof.
intros.
induction H.
rewrite empty_indexed_intersection.
apply open_full.

assert (IndexedIntersection F = Intersection
  (IndexedIntersection (fun x:T => F (Some x)))
  (F None)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
constructor.
constructor.
intros; apply H1.
apply H1.
destruct H1.
destruct H1.
constructor.
destruct a.
apply H1.
apply H2.
rewrite H1.
apply open_intersection2.
apply IHFiniteT.
intros; apply H0.
apply H0.

destruct H1.
assert (IndexedIntersection F =
  IndexedIntersection (fun x:X0 => F (f x))).
apply Extensionality_Ensembles; split; red; intros.
constructor.
destruct H3.
intro; apply H3.
constructor.
destruct H3.
intro; rewrite <- H2 with a.
apply H3.
rewrite H3.
apply IHFiniteT.
intro; apply H0.
Qed.

Definition closed {X:TopologicalSpace} (F:Ensemble (point_set X)) :=
  open (Ensembles.Complement F).

Lemma closed_complement_open: forall {X:TopologicalSpace}
  (U:Ensemble (point_set X)), closed (Ensembles.Complement U) ->
  open U.
Proof.
intros.
red in H.
rewrite Complement_Complement in H.
assumption.
Qed.

Lemma closed_union2: forall {X:TopologicalSpace}
  (F G:Ensemble (point_set X)),
  closed F -> closed G -> closed (Union F G).
Proof.
intros.
red in H, H0.
red.
assert (Ensembles.Complement (Union F G) =
  Intersection (Ensembles.Complement F)
               (Ensembles.Complement G)).
unfold Ensembles.Complement.
apply Extensionality_Ensembles; split; red; intros.
constructor.
auto with sets.
auto with sets.
destruct H1.
red; red; intro.
destruct H3.
apply (H1 H3).
apply (H2 H3).

rewrite H1.
apply open_intersection2; assumption.
Qed.

Lemma closed_intersection2: forall {X:TopologicalSpace}
  (F G:Ensemble (point_set X)),
  closed F -> closed G -> closed (Intersection F G).
Proof.
intros.
red in H, H0.
red.
assert (Ensembles.Complement (Intersection F G) =
  Union (Ensembles.Complement F)
        (Ensembles.Complement G)).
apply Extensionality_Ensembles; split; red; intros.
apply NNPP.
red; intro.
unfold Ensembles.Complement in H1.
unfold In in H1.
contradict H1.
constructor.
apply NNPP.
red; intro.
auto with sets.
apply NNPP.
red; intro.
auto with sets.

red; red; intro.
destruct H2.
destruct H1; auto with sets.

rewrite H1; apply open_union2; trivial.
Qed.

Lemma closed_family_intersection: forall {X:TopologicalSpace}
  (F:Family (point_set X)),
  (forall S:Ensemble (point_set X), In F S -> closed S) ->
  closed (FamilyIntersection F).
Proof.
intros.
unfold closed in H.
red.
assert (Ensembles.Complement (FamilyIntersection F) =
  FamilyUnion [ S:Ensemble (point_set X) |
                  In F (Ensembles.Complement S) ]).
apply Extensionality_Ensembles; split; red; intros.
apply NNPP.
red; intro.
red in H0; red in H0.
contradict H0.
constructor.
intros.
apply NNPP.
red; intro.
contradict H1.
exists (Ensembles.Complement S).
constructor.
rewrite Complement_Complement; assumption.
assumption.
destruct H0.
red; red; intro.
destruct H2.
destruct H0.
pose proof (H2 _ H0).
contradiction H3.

rewrite H0; apply open_family_union.
intros.
destruct H1.
pose proof (H _ H1).
rewrite Complement_Complement in H2; assumption.
Qed.

Lemma closed_indexed_intersection: forall {X:TopologicalSpace}
  {A:Type} (F:IndexedFamily A (point_set X)),
  (forall a:A, closed (F a)) -> closed (IndexedIntersection F).
Proof.
intros.
rewrite indexed_to_family_intersection.
apply closed_family_intersection.
intros.
destruct H0.
rewrite H1; trivial.
Qed.

Lemma closed_finite_indexed_union: forall {X:TopologicalSpace}
  {A:Type} (F:IndexedFamily A (point_set X)),
  FiniteT A -> (forall a:A, closed (F a)) ->
  closed (IndexedUnion F).
Proof.
intros.
red.
assert (Ensembles.Complement (IndexedUnion F) =
  IndexedIntersection (fun a:A => Ensembles.Complement (F a))).
apply Extensionality_Ensembles; split; red; intros.
constructor.
intros.
red; red; intro.
contradiction H1.
exists a.
assumption.
destruct H1.
red; red; intro.
destruct H2.
contradiction (H1 a).

rewrite H1; apply open_finite_indexed_intersection; trivial.
Qed.

Hint Unfold closed : topology.
Hint Resolve (@open_family_union) (@open_intersection2) open_full
  open_empty (@open_union2) (@open_indexed_union)
  (@open_finite_indexed_intersection) (@closed_complement_open)
  (@closed_union2) (@closed_intersection2) (@closed_family_intersection)
  (@closed_indexed_intersection) (@closed_finite_indexed_union)
  : topology.

Section Build_from_closed_sets.

Variable X:Type.
Variable closedP : Ensemble X -> Prop.
Hypothesis closedP_empty: closedP Empty_set.
Hypothesis closedP_union2: forall F G:Ensemble X,
  closedP F -> closedP G -> closedP (Union F G).
Hypothesis closedP_family_intersection: forall F:Family X,
  (forall G:Ensemble X, In F G -> closedP G) ->
  closedP (FamilyIntersection F).

Definition Build_TopologicalSpace_from_closed_sets : TopologicalSpace.
refine (Build_TopologicalSpace X
  (fun U:Ensemble X => closedP (Ensembles.Complement U)) _ _ _).
intros.
replace (Ensembles.Complement (FamilyUnion F)) with
  (FamilyIntersection [ G:Ensemble X | In F (Ensembles.Complement G) ]).
apply closedP_family_intersection.
destruct 1.
rewrite <- Complement_Complement.
apply H; trivial.
apply Extensionality_Ensembles; split; red; intros.
intro.
destruct H1.
destruct H0.
absurd (In (Ensembles.Complement S) x).
intro.
contradiction H3.
apply H0.
constructor.
rewrite Complement_Complement; trivial.
constructor.
destruct 1.
apply NNPP; intro.
contradiction H0.
exists (Ensembles.Complement S); trivial.

intros.
replace (Ensembles.Complement (Intersection U V)) with
  (Union (Ensembles.Complement U) (Ensembles.Complement V)).
apply closedP_union2; trivial.
apply Extensionality_Ensembles; split; red; intros.
intro.
destruct H2.
destruct H1; contradiction H1.
apply NNPP; intro.
contradiction H1.
constructor; apply NNPP; intro; contradiction H2;
  [ left | right ]; trivial.

apply eq_ind with (1 := closedP_empty).
apply Extensionality_Ensembles; split; auto with sets;
  red; intros.
contradiction H.
constructor.
Defined.

Lemma Build_TopologicalSpace_from_closed_sets_closed:
  forall (F:Ensemble (point_set Build_TopologicalSpace_from_closed_sets)),
  closed F <-> closedP F.
Proof.
intros.
unfold closed.
simpl.
rewrite Complement_Complement.
split; trivial.
Qed.

End Build_from_closed_sets.

Arguments Build_TopologicalSpace_from_closed_sets {X}.
