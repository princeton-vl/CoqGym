Require Export TopologicalSpaces.
Require Import ClassicalChoice.
From ZornsLemma Require Import EnsemblesSpec.

Section OpenBasis.

Variable X : TopologicalSpace.
Variable B : Family (point_set X).

Record open_basis : Prop :=
  { open_basis_elements :
     forall V:Ensemble (point_set X), In B V -> open V;
    open_basis_cover :
     forall (x:point_set X) (U:Ensemble (point_set X)),
        open U -> In U x -> exists V:Ensemble (point_set X),
        In B V /\ Included V U /\ In V x
  }.

Hypothesis Hbasis: open_basis.

Lemma coverable_by_open_basis_impl_open:
  forall U:Ensemble (point_set X),
    (forall x:point_set X, In U x -> exists V:Ensemble (point_set X),
     In B V /\ Included V U /\ In V x) -> open U.
Proof.
intros.
assert (U = FamilyUnion [ V:Ensemble (point_set X) |
                          In B V /\ Included V U ]).
apply Extensionality_Ensembles; split; red; intros.
destruct (H x H0) as [V].
destruct H1 as [? [? ?]].
exists V; auto.
constructor; auto.
destruct H0.
destruct H0.
destruct H0.
auto with sets.

rewrite H0.
apply open_family_union.
intros.
destruct H1.
destruct H1.
apply open_basis_elements; trivial.
Qed.

End OpenBasis.

Arguments open_basis {X}.
Arguments coverable_by_open_basis_impl_open {X}.
Arguments open_basis_elements {X}.
Arguments open_basis_cover {X}.

Section BuildFromOpenBasis.

Variable X : Type.
Variable B : Family X.

Definition open_basis_cond :=
  forall U V:Ensemble X, In B U -> In B V ->
    forall x:X, In (Intersection U V) x ->
      exists W:Ensemble X, In B W /\ In W x /\
                           Included W (Intersection U V).
Definition open_basis_cover_cond :=
  forall x:X, exists U:Ensemble X, In B U /\ In U x.

Hypothesis Hbasis : open_basis_cond.
Hypothesis Hbasis_cover: open_basis_cover_cond.

Inductive B_open : Ensemble X -> Prop :=
  | B_open_intro: forall F:Family X, Included F B ->
    B_open (FamilyUnion F).

Definition Build_TopologicalSpace_from_open_basis : TopologicalSpace.
refine (Build_TopologicalSpace X B_open _ _ _).
intros.
pose proof (choice (fun (x:{S:Ensemble X | In F S}) (F:Family X) =>
  Included F B /\ proj1_sig x = FamilyUnion F)).
unshelve refine (let H1:=(H0 _) in _); [ | clearbody H1 ].
intros.
destruct x.
pose proof (H x i).
destruct H1.
exists F0.
split; simpl; trivial.
clear H0.
destruct H1.
assert (FamilyUnion F = FamilyUnion (IndexedUnion x)).
apply Extensionality_Ensembles; split; red; intros.
destruct H1.
pose proof (H0 (exist _ _ H1)).
destruct H3.
simpl in H4.
rewrite H4 in H2.
destruct H2.
constructor 1 with S0.
exists (exist _ _ H1).
assumption.
assumption.

destruct H1.
destruct H1.
pose proof (H0 a).
destruct H3.
destruct a.
simpl in H4.
exists x2.
assumption.
rewrite H4.
exists x1.
assumption.
assumption.

rewrite H1.
constructor.
red; intros.
destruct H2.
pose proof (H0 a).
destruct H3.
auto with sets.

intros.
assert (Intersection U V = FamilyUnion
  [ S:Ensemble X | In B S /\ Included S (Intersection U V) ]).
apply Extensionality_Ensembles; split; red; intros.
destruct H.
destruct H0.
destruct H1.
destruct H1.
destruct H2.
pose proof (H _ H1).
pose proof (H0 _ H2).
pose proof (Hbasis _ _ H5 H6).
assert (In (Intersection S S0) x). constructor; trivial.
apply H7 in H8.
clear H7.
destruct H8.
destruct H7 as [? [? ?]].
exists x0; trivial.
constructor.
split; trivial.
red; intros.
constructor.
exists S; trivial.
pose proof (H9 x1 H10).
destruct H11; trivial.
exists S0; trivial.
pose proof (H9 x1 H10).
destruct H11; trivial.
destruct H1.
destruct H1.
destruct H1.
auto.

rewrite H1.
constructor.
red; intros.
destruct H2.
destruct H2.
auto.

assert (Full_set = FamilyUnion B).
apply Extensionality_Ensembles; split; red; intros.
pose proof (Hbasis_cover x).
destruct H0.
destruct H0.
exists x0; trivial.
constructor.

rewrite H; constructor.
auto with sets.
Defined.

Lemma Build_TopologicalSpace_from_open_basis_point_set:
  point_set Build_TopologicalSpace_from_open_basis = X.
Proof.
reflexivity.
Qed.

Lemma Build_TopologicalSpace_from_open_basis_basis:
  @open_basis Build_TopologicalSpace_from_open_basis B.
Proof.
constructor.
intros.
simpl.
assert (V = FamilyUnion (Singleton V)).
apply Extensionality_Ensembles; split; red; intros.
exists V; auto with sets.
destruct H0.
destruct H0; trivial.
rewrite H0; constructor.
red; intros.
destruct H1; trivial.
simpl.
intros.
destruct H.
destruct H0.
exists S; repeat split; auto with sets.
red; intros.
exists S; trivial.
Qed.

End BuildFromOpenBasis.

Arguments open_basis_cond {X}.
Arguments open_basis_cover_cond {X}.
Arguments Build_TopologicalSpace_from_open_basis {X}.
Arguments Build_TopologicalSpace_from_open_basis_point_set {X}.
Arguments Build_TopologicalSpace_from_open_basis_basis {X}.
