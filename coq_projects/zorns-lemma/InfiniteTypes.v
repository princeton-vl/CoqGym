Require Export FiniteTypes.
Require Import EnsemblesImplicit.
Require Import ClassicalChoice.
Require Import Arith.
Require Import FunctionalExtensionality.
Require Import EnsemblesSpec.

Lemma finite_nat_initial_segment: forall n:nat,
  FiniteT { m:nat | m < n }.
Proof.
intros.
apply Finite_ens_type.
rewrite <- characteristic_function_to_ensemble_is_identity.
induction n.
assert ([x:nat | S x <= 0] = Empty_set).
apply Extensionality_Ensembles; split; auto with sets.
red; intros.
destruct H.
contradict H.
auto with arith.
rewrite H; constructor.

assert ([x:nat | S x <= S n] = Add [x:nat | x < n] n).
apply Extensionality_Ensembles; split.
red; intros.
destruct H.
assert (x <= n); auto with arith.
apply le_lt_or_eq in H0.
case H0.
left; constructor; trivial.
right; auto with sets.
red; intros.
case H.
intros.
destruct H0; constructor.
auto with arith.
intros.
destruct H0.
constructor.
auto with arith.
rewrite H; constructor; trivial.
red; intro.
destruct H0.
contradict H0.
auto with arith.
Qed.

Lemma infinite_nat_inj: forall X:Type, ~ FiniteT X ->
  exists f:nat->X, injective f.
Proof.
intros.
assert (inhabited (forall S:Ensemble X, Finite _ S ->
  { x:X | ~ In S x})).
pose proof (choice (fun (x:{S:Ensemble X | Finite _ S}) (y:X) =>
  ~ In (proj1_sig x) y)).
simpl in H0.
match type of H0 with | ?A -> ?B => assert B end.
apply H0.
intros.
apply NNPP.
red; intro.
pose proof (not_ex_not_all _ _ H1); clear H1.
destruct x.
assert (x = Full_set).
apply Extensionality_Ensembles; red; split; auto with sets.
intro x0; constructor.
symmetry in H1; destruct H1.
contradiction H.
clear H2.
apply bij_finite with (f:=@proj1_sig _ (fun x:X => In Full_set x)).
apply Finite_ens_type; assumption.
exists (fun x:X => exist _ x (Full_intro _ x)).
destruct x; simpl.
generalize (Full_intro X x).
intro i0; destruct (proof_irrelevance _ i i0); trivial.
trivial.
clear H0.
destruct H1.
exists.
intros.
exists (x (exist _ S H1)).
exact (H0 (exist _ S H1)).
destruct H0.

assert (forall (n:nat) (g:forall m:nat, m<n -> X),
  { x:X | forall (m:nat) (Hlt:m<n), g m Hlt <> x }).
intros.
assert (Finite _ (fun x:X => exists m:nat, exists Hlt:m<n,
           g m Hlt = x)).
pose (h := fun x:{m:nat | m<n} =>
  g (proj1_sig x) (proj2_sig x)).

match goal with |- Finite X ?S => assert (S =
  Im Full_set h) end.
apply Extensionality_Ensembles; red; split; red; intros.
destruct H0.
destruct H0.
exists (exist (fun m:nat => m < n) x0 x1).
constructor.
unfold h; simpl.
symmetry; assumption.
destruct H0.
destruct x.
unfold h in H1; simpl in H1.
exists x; exists l; symmetry; assumption.

rewrite H0; apply FiniteT_img.
apply finite_nat_initial_segment.
intros; apply classic.

destruct (X0 _ H0).
unfold In in n0.
exists x.
intros; red; intro.
contradiction n0; exists m; exists Hlt; exact H1.

pose (f := Fix lt_wf (fun n:nat => X)
  (fun (n:nat) (g:forall m:nat, m<n->X) => proj1_sig (X1 n g))).
simpl in f.
assert (forall n m:nat, m<n -> f m <> f n).
pose proof (Fix_eq lt_wf (fun n:nat => X)
  (fun (n:nat) (g:forall m:nat, m<n->X) => proj1_sig (X1 n g))).
fold f in H0.
simpl in H0.
match type of H0 with | ?A -> ?B => assert (B) end.
apply H0.
intros.
assert (f0 = g).
Require Import FunctionalExtensionality.
extensionality y; extensionality p; apply H1.
destruct H2; trivial.
intros.
pose proof (H1 n).
destruct X1 in H3.
simpl in H3.
destruct H3.
auto.

exists f.
red; intros m n ?.
destruct (lt_eq_lt_dec m n) as [[Hlt|Heq]|Hlt]; trivial.
contradiction (H0 n m).
contradiction (H0 m n).
symmetry; assumption.
Qed.

Lemma nat_infinite: ~ FiniteT nat.
Proof.
red; intro.
assert (surjective S).
apply finite_inj_surj; trivial.
red; intros.
injection H0; trivial.

destruct (H0 0).
discriminate H1.
Qed.
