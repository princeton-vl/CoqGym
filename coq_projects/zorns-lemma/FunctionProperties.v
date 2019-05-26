Definition injective {X Y:Type} (f:X->Y) :=
  forall x1 x2:X, f x1 = f x2 -> x1 = x2.
Definition surjective {X Y:Type} (f:X->Y) :=
  forall y:Y, exists x:X, f x = y.
Definition bijective {X Y:Type} (f:X->Y) :=
  injective f /\ surjective f.

Inductive invertible {X Y:Type} (f:X->Y) : Prop :=
  | intro_invertible: forall g:Y->X,
  (forall x:X, g (f x) = x) -> (forall y:Y, f (g y) = y) ->
  invertible f.

Require Import Description.
Require Import FunctionalExtensionality.

Lemma unique_inverse: forall {X Y:Type} (f:X->Y), invertible f ->
  exists! g:Y->X, (forall x:X, g (f x) = x) /\
             (forall y:Y, f (g y) = y).
Proof.
intros.
destruct H.
exists g.
red; split.
tauto.
intros.
destruct H1.
extensionality y.
transitivity (g (f (x' y))).
rewrite H2.
reflexivity.
rewrite H.
reflexivity.
Qed.

Definition function_inverse {X Y:Type} (f:X->Y)
  (i:invertible f) : { g:Y->X | (forall x:X, g (f x) = x) /\
                                (forall y:Y, f (g y) = y) }
  :=
     (constructive_definite_description _
      (unique_inverse f i)).

Lemma bijective_impl_invertible: forall {X Y:Type} (f:X->Y),
  bijective f -> invertible f.
Proof.
intros.
destruct H.
assert (forall y:Y, {x:X | f x = y}).
intro.
apply constructive_definite_description.
pose proof (H0 y).
destruct H1.
exists x.
red; split.
assumption.
intros.
apply H.
transitivity y.
auto with *.
auto with *.
pose (g := fun y:Y => proj1_sig (X0 y)).
pose proof (fun y:Y => proj2_sig (X0 y)).
simpl in H1.
exists g.
intro.
apply H.
unfold g; rewrite H1.
reflexivity.
intro.
unfold g; apply H1.
Qed.

Lemma invertible_impl_bijective: forall {X Y:Type} (f:X->Y),
  invertible f -> bijective f.
Proof.
intros.
destruct H.
split.
red; intros.
congruence.
red; intro.
exists (g y).
apply H0.
Qed.
