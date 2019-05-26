Require Export TopologicalSpaces.
Require Import WeakTopology.

Section Subspace.

Variable X:TopologicalSpace.
Variable A:Ensemble (point_set X).

Definition SubspaceTopology : TopologicalSpace :=
  WeakTopology1 (proj1_sig (P:=fun x:point_set X => In A x)).

Definition subspace_inc : point_set SubspaceTopology ->
  point_set X :=
  proj1_sig (P:=fun x:point_set X => In A x).

Lemma subspace_topology_topology: forall U:Ensemble {x:point_set X | In A x},
  @open SubspaceTopology U -> exists V:Ensemble (point_set X),
  open V /\ U = inverse_image subspace_inc V.
Proof.
apply weak_topology1_topology.
Qed.

Lemma subspace_inc_continuous:
  continuous subspace_inc.
Proof.
apply weak_topology1_makes_continuous_func.
Qed.

End Subspace.

Arguments SubspaceTopology {X}.
Arguments subspace_inc {X}.
