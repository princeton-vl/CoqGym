Require Export TopologicalSpaces.
Require Export Neighborhoods.
Require Export OpenBases.
From ZornsLemma Require Export IndexedFamilies.
From ZornsLemma Require Export EnsemblesSpec.

Record neighborhood_basis {X:TopologicalSpace}
  (NB:Family (point_set X)) (x:point_set X) : Prop := {
  neighborhood_basis_elements: forall N:Ensemble (point_set X),
    In NB N -> neighborhood N x;
  neighborhood_basis_cond: forall N:Ensemble (point_set X),
    neighborhood N x -> exists N':Ensemble (point_set X),
    In NB N' /\ Included N' N
}.

Record open_neighborhood_basis {X:TopologicalSpace}
  (NB:Family (point_set X)) (x:point_set X) : Prop := {
  open_neighborhood_basis_elements: forall U:Ensemble (point_set X),
    In NB U -> open_neighborhood U x;
  open_neighborhood_basis_cond: forall U:Ensemble (point_set X),
    open_neighborhood U x -> exists V:Ensemble (point_set X),
    In NB V /\ Included V U
}.

Lemma open_neighborhood_basis_is_neighborhood_basis:
  forall {X:TopologicalSpace} (NB:Family (point_set X)) (x:point_set X),
  open_neighborhood_basis NB x -> neighborhood_basis NB x.
Proof.
intros.
destruct H.
constructor; intros.
apply open_neighborhood_is_neighborhood; auto.
destruct H as [U [? ?]].
destruct (open_neighborhood_basis_cond0 U H) as [V [? ?]].
exists V; split; auto with sets.
Qed.

Lemma open_basis_to_open_neighborhood_basis:
  forall {X:TopologicalSpace} (B:Family (point_set X)) (x:point_set X),
    open_basis B -> open_neighborhood_basis
                    [ U:Ensemble (point_set X) | In B U /\ In U x ]
                    x.
Proof.
intros.
destruct H.
constructor.
intros; split; trivial.
destruct H as [[? ?]].
apply open_basis_elements.
assumption.
destruct H as [[? ?]]; assumption.
intros.
destruct H.
destruct (open_basis_cover x U H H0).
destruct H1 as [? [? ?]].
exists x0.
repeat split; trivial.
Qed.

Lemma open_neighborhood_bases_to_open_basis:
  forall {X:TopologicalSpace} (NB : point_set X -> Family (point_set X)),
    (forall x:point_set X, open_neighborhood_basis (NB x) x) ->
    open_basis (IndexedUnion NB).
Proof.
intros.
constructor; intros.
destruct H0.
destruct (H a).
destruct (open_neighborhood_basis_elements0 x H0); trivial.

destruct (H x).
assert (open_neighborhood U x).
split; trivial.
destruct (open_neighborhood_basis_cond0 U H2) as [V [? ?]].
exists V; repeat split; trivial.
exists x; trivial.
pose proof (open_neighborhood_basis_elements0 V H3).
destruct H5; trivial.
Qed.

Section build_from_open_neighborhood_bases.

Variable X:Type.
Variable NB : X -> Family X.

Hypothesis neighborhood_basis_cond :
  forall (U V:Ensemble X) (x:X), In (NB x) U -> In (NB x) V ->
    exists W:Ensemble X, In (NB x) W /\ Included W (Intersection U V).
Hypothesis neighborhood_basis_cond2 :
  forall (U:Ensemble X) (x:X), In (NB x) U -> In U x.
Hypothesis neighborhood_basis_inhabited_cond :
  forall x:X, Inhabited (NB x).
Hypothesis neighborhood_basis_system_cond :
  forall (x y:X) (U:Ensemble X), In (NB x) U -> In U y ->
  exists V:Ensemble X, In (NB y) V /\ Included V U.

Definition Build_TopologicalSpace_from_open_neighborhood_bases :
  TopologicalSpace.
refine (Build_TopologicalSpace_from_open_basis (IndexedUnion NB)
  _ _).
red; intros.
destruct H as [y U'].
destruct H0 as [z V'].
destruct H1.
destruct (neighborhood_basis_system_cond y x U' H H1) as
  [U'' [? ?]].
destruct (neighborhood_basis_system_cond z x V' H0 H2) as
  [V'' [? ?]].
destruct (neighborhood_basis_cond U'' V'' x H3 H5) as
  [W [? ?]].
exists W.
repeat split.
exists x; trivial.
apply neighborhood_basis_cond2; trivial.
apply H4.
pose proof (H8 _ H9).
destruct H10; assumption.
apply H6.
pose proof (H8 _ H9).
destruct H10; assumption.

red; intros.
destruct (neighborhood_basis_inhabited_cond x) as [U].
exists U; split; auto.
exists x; trivial.
Defined.

Lemma Build_TopologicalSpace_from_open_neighborhood_bases_basis:
  forall x:X,
    open_neighborhood_basis (NB x) x
      (X:=Build_TopologicalSpace_from_open_neighborhood_bases).
Proof.
assert (open_basis (IndexedUnion NB)
  (X:=Build_TopologicalSpace_from_open_neighborhood_bases))
  by apply Build_TopologicalSpace_from_open_basis_basis.
destruct H.
intros.
constructor.
intros.
constructor.
apply open_basis_elements.
exists x; trivial.
apply neighborhood_basis_cond2; trivial.

intros.
destruct H.
destruct (open_basis_cover x U H H0) as [V [? []]].
destruct H1 as [y V].
destruct (neighborhood_basis_system_cond y x V H1 H3) as [W []].
exists W; auto with sets.
Qed.

End build_from_open_neighborhood_bases.
