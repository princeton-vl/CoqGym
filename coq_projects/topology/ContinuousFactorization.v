Require Export TopologicalSpaces.
Require Export Continuity.
Require Export SubspaceTopology.

Section continuous_factorization.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.
Variable S:Ensemble (point_set Y).
Hypothesis f_cont: continuous f.
Hypothesis f_img: forall x:point_set X, In S (f x).

Definition continuous_factorization :
  point_set X -> point_set (SubspaceTopology S) :=
  fun x:point_set X => exist _ (f x) (f_img x).

Lemma factorization_is_continuous:
  continuous continuous_factorization.
Proof.
red; intros.
destruct (subspace_topology_topology _ _ V H) as [V' []].
rewrite H1.
rewrite <- inverse_image_composition.
simpl.
assert (inverse_image (fun x:point_set X => f x) V' =
        inverse_image f V').
apply Extensionality_Ensembles; split; red; intros.
destruct H2; constructor; trivial.
destruct H2; constructor; trivial.
rewrite H2.
apply f_cont; trivial.
Qed.

End continuous_factorization.

Arguments continuous_factorization {X} {Y}.

Section continuous_surj_factorization.

Variable X Y:TopologicalSpace.
Variable f:point_set X -> point_set Y.
Hypothesis f_cont: continuous f.

Definition continuous_surj_factorization :
  point_set X -> point_set (SubspaceTopology (Im Full_set f)).
apply continuous_factorization with f.
intros.
exists x.
constructor.
trivial.
Defined.

Lemma continuous_surj_factorization_is_surjective:
  surjective continuous_surj_factorization.
Proof.
red; intros.
destruct y.
destruct i.
exists x.
unfold continuous_surj_factorization.
unfold continuous_factorization.
pose proof (e).
symmetry in H.
destruct H.
f_equal.
f_equal.
apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Lemma continuous_surj_factorization_is_continuous:
  continuous continuous_surj_factorization.
Proof.
apply factorization_is_continuous.
exact f_cont.
Qed.

End continuous_surj_factorization.

Arguments continuous_surj_factorization {X} {Y}.
