Require Export TopologicalSpaces.
From ZornsLemma Require Export CountableTypes.
Require Export NeighborhoodBases.
From ZornsLemma Require Import EnsemblesSpec.

Global Set Asymmetric Patterns.

Definition first_countable (X:TopologicalSpace) : Prop :=
  forall x:point_set X, exists NBx:Family (point_set X),
    neighborhood_basis NBx x /\ Countable NBx.

Lemma first_countable_open_neighborhood_bases:
  forall X:TopologicalSpace, first_countable X ->
    forall x:point_set X, exists NBx:Family (point_set X),
      open_neighborhood_basis NBx x /\ Countable NBx.
Proof.
intros.
destruct (H x) as [NBx [? ?]].
exists (@Im (Ensemble (point_set X)) (Ensemble (point_set X)) NBx (@interior X)).
split.
constructor.
intros.
destruct H2 as [U].
split.
rewrite H3; apply interior_open.
rewrite H3; apply neighborhood_interior.
apply H0; trivial.
intros.
destruct H0.
destruct (neighborhood_basis_cond U) as [N].
apply open_neighborhood_is_neighborhood; trivial.
destruct H0.
exists (interior N).
split.
exists N; trivial.
pose proof (interior_deflationary N).
auto with sets.

apply countable_img; trivial.
Qed.

Require Export Nets.

Lemma first_countable_sequence_closure:
  forall (X:TopologicalSpace) (S:Ensemble (point_set X)) (x:point_set X),
  first_countable X -> In (closure S) x ->
  exists y:Net nat_DS X, (forall n:nat, In S (y n)) /\
                         net_limit y x.
Proof.
intros.
destruct (first_countable_open_neighborhood_bases _ H x) as [NB []].
destruct H2 as [g].
pose (U (n:nat) := IndexedIntersection
  (fun x: {x:{x:Ensemble (point_set X) | In NB x} | (g x < n)%nat} =>
     proj1_sig (proj1_sig x))).
assert (forall n:nat, open (U n)).
intros.
apply open_finite_indexed_intersection.
apply inj_finite with _ (fun x:{x:{x:Ensemble (point_set X) | In NB x}
                           | (g x < n)%nat} =>
  exist (fun m:nat => (m<n)%nat) (g (proj1_sig x)) (proj2_sig x)).
From ZornsLemma Require Import InfiniteTypes.
apply finite_nat_initial_segment.
red.
intros [[x0 P] p] [[y0 Q] q] ?.
simpl in H3.
From ZornsLemma Require Import Proj1SigInjective.
apply subset_eq_compatT.
apply subset_eq_compatT.
injection H3; intros.
apply H2 in H4.
injection H4; trivial.
intros; apply classic.
intros.
destruct a as [[x0]].
simpl.
Opaque In. apply H1; trivial. Transparent In.

Require Import ClassicalChoice.
destruct (choice (fun (n:nat) (x:point_set X) => In (U n) x /\
                                                 In S x)) as [y].
intros n.
destruct (closure_impl_meets_every_open_neighborhood _ _ _ H0 (U n))
  as [y]; trivial.
constructor; trivial.
destruct a as [[x0]].
simpl.
apply H1; trivial.
exists y; destruct H4; split; trivial.
exists y.
split.
apply H4.

red; intros V ? ?.
destruct H1.
destruct (open_neighborhood_basis_cond V) as [W []].
split; trivial.
pose (a := (exist _ W H1 : {x:Ensemble (point_set X)|In NB x})).
exists (Datatypes.S (g a)).
intros.
simpl in j.
simpl in H8.
apply H7.
assert (Included (U j) W).
red; intros.
destruct H9.
exact (H9 (exist _ a H8)).
apply H9.
apply H4.
Qed.

Inductive separable (X:TopologicalSpace) : Prop :=
  | intro_dense_ctbl: forall S:Ensemble (point_set X),
    Countable S -> dense S -> separable X.

Definition Lindelof (X:TopologicalSpace) : Prop :=
  forall cover:Family (point_set X),
    (forall U:Ensemble (point_set X),
       In cover U -> open U) ->
    FamilyUnion cover = Full_set ->
  exists subcover:Family (point_set X), Included subcover cover /\
     Countable subcover /\ FamilyUnion subcover = Full_set.

Inductive second_countable (X:TopologicalSpace) : Prop :=
  | intro_ctbl_basis: forall B:Family (point_set X),
    open_basis B -> Countable B -> second_countable X.

Lemma second_countable_impl_first_countable:
  forall X:TopologicalSpace, second_countable X -> first_countable X.
Proof.
intros.
destruct H.
red; intros.
exists [ U:Ensemble (point_set X) | In B U /\ In U x ]; split.
apply open_neighborhood_basis_is_neighborhood_basis.
apply open_basis_to_open_neighborhood_basis; trivial.
apply countable_downward_closed with B; trivial.
red; intros.
destruct H1 as [[? ?]]; trivial.
Qed.

Lemma second_countable_impl_separable:
  forall X:TopologicalSpace, second_countable X -> separable X.
Proof.
intros.
destruct H.
Require Import ClassicalChoice.
destruct (choice (fun (U:{U:Ensemble (point_set X) | In B U /\ Inhabited U})
  (x:point_set X) => In (proj1_sig U) x)) as [choice_fun].
intros.
destruct x as [U [? ?]].
simpl.
destruct i0.
exists x; trivial.

exists (Im Full_set choice_fun).
apply countable_img.
red.
match goal with |- CountableT ?S =>
  pose (g := fun (x:S) =>
    match x return {U:Ensemble (point_set X) | In B U} with
    | exist (exist U (conj i _)) _ => exist _ U i
    end)
end.
apply inj_countable with g.
assumption.
red; intros.
unfold g in H2.
destruct x1 as [[U [? ?]]].
destruct x2 as [[V [? ?]]].
From ZornsLemma Require Import Proj1SigInjective.
apply subset_eq_compatT.
apply subset_eq_compatT.
injection H2; trivial.

apply meets_every_nonempty_open_impl_dense.
intros.
destruct H3.
destruct H.
destruct (open_basis_cover x U) as [V [? [? ?]]]; trivial.
assert (In B V /\ Inhabited V).
split; trivial.
exists x; trivial.
exists (choice_fun (exist _ V H6)).

constructor.
(* apply H4. *)
pose proof (H1 (exist _ V H6)).
simpl in H7.
(* assumption. *)
exists (exist (fun U0:Ensemble (point_set X) => In B U0 /\ Inhabited U0) V H6).
constructor.
reflexivity.
apply H4.
pose proof (H1 (exist _ V H6)).
simpl in H7.
assumption.
Qed.

Lemma second_countable_impl_Lindelof:
  forall X:TopologicalSpace, second_countable X -> Lindelof X.
Proof.
intros.
destruct H.
red; intros.

pose (basis_elts_contained_in_cover_elt :=
  [ U:Ensemble (point_set X) | In B U /\ Inhabited U /\
    exists V:Ensemble (point_set X), In cover V /\ Included U V ]).
destruct (choice (fun (U:{U | In basis_elts_contained_in_cover_elt U})
  (V:Ensemble (point_set X)) => In cover V /\ Included (proj1_sig U) V))
  as [choice_fun].
intros.
destruct x.
simpl.
destruct i as [[? [? ?]]].
exact H5.
exists (Im Full_set choice_fun).
repeat split.
red; intros.
destruct H4.
destruct (H3 x).
rewrite H5; assumption.
apply countable_img.
apply countable_type_ensemble.
apply countable_downward_closed with B; trivial.
red; intros.
destruct H4 as [[]].
assumption.

apply Extensionality_Ensembles; red; split; red; intros.
constructor.
clear H4.
assert (In (FamilyUnion cover) x).
rewrite H2; constructor.
destruct H4.

destruct H.
destruct (open_basis_cover x S) as [V]; trivial.
apply H1; trivial.

destruct H as [? [? ?]].

assert (In basis_elts_contained_in_cover_elt V).
constructor.
repeat split; trivial.
exists x; trivial.
exists S; split; trivial.

exists (choice_fun (exist _ V H8)).
exists (exist _ V H8).
constructor.
reflexivity.

pose proof (H3 (exist _ V H8)).
destruct H9.
simpl in H10.
apply H10; trivial.
Qed.
