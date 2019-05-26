Require Export FunctionProperties.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import CSB.
Require Import EnsemblesSpec.

Inductive Cardinal : Type :=
  | cardinality: Type -> Cardinal.

Fixpoint n_element_set (n:nat) : Set :=
  match n with
  | O => False
  | S m => option (n_element_set m)
  end.
Definition nat_to_cardinal (n:nat) :=
  cardinality (n_element_set n).

Definition aleph0 := cardinality nat.

Inductive eq_cardinal : Cardinal -> Cardinal -> Prop :=
  | bij_eq_cardinal: forall {X Y:Type} (f:X->Y),
    bijective f -> eq_cardinal (cardinality X) (cardinality Y).
Inductive le_cardinal : Cardinal -> Cardinal -> Prop :=
  | inj_le_cardinal: forall {X Y:Type} (f:X->Y),
    injective f -> le_cardinal (cardinality X) (cardinality Y).

Definition lt_cardinal (kappa lambda:Cardinal) : Prop :=
  le_cardinal kappa lambda /\ ~ eq_cardinal kappa lambda.
Definition ge_cardinal (kappa lambda:Cardinal) : Prop :=
  le_cardinal lambda kappa.
Definition gt_cardinal (kappa lambda:Cardinal) : Prop :=
  lt_cardinal lambda kappa.

Lemma eq_cardinal_equiv: equivalence eq_cardinal.
Proof.
constructor.
red; intro.
destruct x.
exists (fun x:T => x).
red; split.
red; intros.
assumption.
red; intro.
exists y.
reflexivity.

red; intros.
destruct H.
inversion H0.
destruct H1.
destruct H3.
exists (fun x:X => f0 (f x)).
red; split.
red; intros.
apply H.
apply H2.
assumption.
red; intro.
destruct H.
destruct H2.
pose proof (H3 y).
destruct H4.
pose proof (H1 x).
destruct H5.
exists x0.
rewrite H5.
assumption.

red; intros.
destruct H.
apply bijective_impl_invertible in H.
destruct (function_inverse f H) as [finv].
destruct a.
exists finv.
apply invertible_impl_bijective.
exists f.
assumption.
assumption.
Qed.

Lemma eq_cardinal_impl_le_cardinal: forall kappa lambda: Cardinal,
  eq_cardinal kappa lambda -> le_cardinal kappa lambda.
Proof.
intros.
destruct H.
exists f.
destruct H.
assumption.
Qed.

Lemma le_cardinal_preorder: preorder le_cardinal.
Proof.
constructor.
red; intro.
apply eq_cardinal_impl_le_cardinal.
apply (equiv_refl eq_cardinal_equiv).
red; intros.
destruct H.
inversion H0.
exists (fun x:X => f0 (f x)).
red; intros.
apply H.
apply H2.
assumption.
Qed.

Lemma le_cardinal_antisym: forall kappa lambda:Cardinal,
  le_cardinal kappa lambda -> le_cardinal lambda kappa ->
  eq_cardinal kappa lambda.
Proof.
intros.
destruct H.
inversion H0.
destruct H1.
destruct H2.
pose proof (CSB Y0 X0 f f0 H H3).
destruct H1.
exists x.
assumption.
Qed.

Lemma cantor_diag: forall (X:Type) (f:X->(X->bool)),
  ~ surjective f.
Proof.
intros.
red; intro.
pose (g := fun x:X => negb (f x x)).
pose proof (H g).
destruct H0.
assert (f x x = g x).
rewrite H0.
reflexivity.
unfold g in H1.
destruct (f x x).
discriminate H1.
discriminate H1.
Qed.

Lemma P_neq_not_P: forall (P:Prop), P <> ~P.
Proof.
unfold not; intros.
assert (~P).
unfold not; intro.
assert (P->False).
rewrite <- H.
assumption.
tauto.
assert P.
rewrite H.
assumption.
tauto.
Qed.

Lemma cantor_diag2: forall (X:Type) (f:X->(X->Prop)),
  ~ surjective f.
Proof.
unfold not; intros.
pose (g := fun x:X => ~ f x x).
pose proof (H g).
destruct H0.
assert (f x x = g x).
rewrite H0.
reflexivity.
unfold g in H1.
contradiction P_neq_not_P with (f x x).
Qed.

Lemma cardinals_unbounded: forall kappa:Cardinal, exists lambda:Cardinal,
  gt_cardinal lambda kappa.
Proof.
destruct kappa.
exists (cardinality (T->Prop)).
red; red; split.
exists (@eq T).
red; intros.
rewrite H.
reflexivity.

unfold not; intro.
inversion H.
destruct H0.
destruct H2.
contradiction (cantor_diag2 _ f).
Qed.

(* The results below require Axiom of Choice *)
Require Import ClassicalChoice.

Lemma surj_le_cardinal: forall {X Y:Type} (f:X->Y),
  surjective f -> le_cardinal (cardinality Y) (cardinality X).
Proof.
intros.
pose proof (choice (fun (y:Y) (x:X) => f x = y) H).
simpl in H0.
destruct H0 as [g].
exists g.
red; intros.
congruence.
Qed.

Section le_cardinal_total.

Variable X Y:Type.

Require Import ZornsLemma.
Require Import EnsemblesImplicit.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import Description.

Record partial_injection : Type := {
  pi_dom: Ensemble X;
  pi_func: forall x:X, In pi_dom x -> Y;
  pi_inj: forall (x1 x2:X) (i1:In pi_dom x1) (i2:In pi_dom x2),
    pi_func x1 i1 = pi_func x2 i2 -> x1 = x2
}.
Record partial_injection_ord (pi1 pi2:partial_injection) : Prop := {
  pi_dom_inc: Included (pi_dom pi1) (pi_dom pi2);
  pi_func_ext: forall (x:X) (i1:In (pi_dom pi1) x)
   (i2:In (pi_dom pi2) x),
    pi_func pi1 x i1 = pi_func pi2 x i2
}.

Lemma partial_injection_preord: preorder partial_injection_ord.
Proof.
constructor.
red; intros.
destruct x.
constructor.
auto with sets.
intros.
assert (i1 = i2).
apply proof_irrelevance.
rewrite H.
reflexivity.

red; intros.
destruct H.
destruct H0.
constructor.
auto with sets.
intros.
assert (In (pi_dom y) x0).
auto with sets.
transitivity (pi_func y x0 H); trivial.
Qed.

Lemma partial_injection_chain_ub: forall S:Ensemble partial_injection,
  chain partial_injection_ord S -> exists x:partial_injection,
  forall y:partial_injection, In S y -> partial_injection_ord y x.
Proof.
intros.
pose (ub_dom := [x:X | exists y:partial_injection,
  In S y /\ In (pi_dom y) x]).
assert (forall x:X, In ub_dom x -> { y:Y | exists z:partial_injection,
  In S z /\ exists i:In (pi_dom z) x, pi_func z x i = y }).
intros.
apply constructive_definite_description.
destruct H0.
destruct H0.
destruct H0.
exists (pi_func x0 x H1).
red; split.
exists x0.
split.
assumption.
exists H1.
reflexivity.
intros.
destruct H2.
destruct H2.
destruct H3.
pose proof (H x0 x1 H0 H2).
case H4.
intro.
rewrite <- H3.
apply pi_func_ext.
assumption.
intro.
rewrite <- H3.
symmetry.
apply pi_func_ext.
assumption.

assert (forall (x1 x2:X) (i1:In ub_dom x1) (i2:In ub_dom x2),
  proj1_sig (X0 x1 i1) = proj1_sig (X0 x2 i2) -> x1 = x2).
intros.
destruct X0 in H0.
destruct X0 in H0.
simpl in H0.
destruct H0.
destruct e.
destruct H0.
destruct H1.
destruct e0.
destruct H2.
destruct H3.
destruct H1.
case (H x0 x4 H0 H2).
intro.
assert (In (pi_dom x4) x1).
apply (pi_dom_inc _ _ H1).
assumption.
assert (pi_func x4 x1 H4 = pi_func x4 x2 x5).
rewrite H3.
symmetry.
apply pi_func_ext.
assumption.
apply pi_inj in H5.
assumption.

intro.
assert (In (pi_dom x0) x2).
apply (pi_dom_inc _ _ H1).
assumption.
assert (pi_func x0 x1 x3 = pi_func x0 x2 H4).
rewrite <- H3.
apply pi_func_ext.
assumption.
apply pi_inj in H5.
assumption.

exists (Build_partial_injection ub_dom
  (fun (x:X) (i:In ub_dom x) => proj1_sig (X0 x i)) H0).
intros.
constructor.
simpl.
red; intros.
constructor.
exists y.
tauto.
simpl.
intros.
destruct (X0 x i2).
simpl.
destruct e.
destruct H2.
destruct H3.
destruct H3.
case (H y x1 H1 H2).
intro.
apply pi_func_ext.
assumption.
intro.
symmetry.
apply pi_func_ext.
assumption.
Qed.

Lemma premaximal_partial_injection:
  exists x:partial_injection, premaximal partial_injection_ord x.
Proof.
apply ZornsLemmaForPreorders.
exact partial_injection_preord.
exact partial_injection_chain_ub.
Qed.

Lemma premaximal_pi_is_full_or_surj:
  forall x:partial_injection, premaximal partial_injection_ord x ->
    pi_dom x = Full_set \/
    forall y:Y, exists x0:X, exists i:(In (pi_dom x) x0),
      pi_func x x0 i = y.
Proof.
intros.
case (classic (pi_dom x = Full_set)).
left.
trivial.
intro.
assert (exists x0:X, ~ In (pi_dom x) x0).
apply NNPP.
intuition.
apply H0.
apply Extensionality_Ensembles.
red; split.
red; intros.
constructor.
red; intros.
apply NNPP.
intuition.
apply H1.
exists x0.
assumption.
right.
destruct H1.
intros.
apply NNPP.
intuition.

pose (pi_dom_ext := Add (pi_dom x) x0).
assert (forall (x':X), In pi_dom_ext x' ->
  { y':Y | (exists i2:In (pi_dom x) x', y' = pi_func x x' i2) \/
          (x' = x0 /\ y' = y) }).
intros.
apply constructive_definite_description.
case H3.
intros.
exists (pi_func x x1 H4).
red; split.
left.
exists H4.
reflexivity.
intros.
case H5.
intro.
destruct H6.
rewrite H6.
assert (H4 = x2).
apply proof_irrelevance.
rewrite H7.
reflexivity.

intros.
destruct H6.
contradict H1.
rewrite <- H6.
assumption.

intros.
destruct H4.
exists y.
red; split.
right.
tauto.
intros.
case H4.
intro.
destruct H5.
contradiction H1.
intros.
symmetry.
tauto.

pose (pi_func_ext0 := fun (x:X) (i:In pi_dom_ext x) =>
  proj1_sig (X0 x i)).

assert (forall (x1:X) (i:In (pi_dom x) x1) (i2:In pi_dom_ext x1),
  pi_func_ext0 x1 i2 = pi_func x x1 i).
intros.
unfold pi_func_ext0.
destruct (X0 x1 i2).
simpl.
case o.
intros.
destruct H3.
assert (i = x3).
apply proof_irrelevance.
rewrite H4.
assumption.
intros.
destruct H3.
contradiction H1.
rewrite <- H3.
assumption.

assert (forall (i:In pi_dom_ext x0), pi_func_ext0 x0 i = y).
intros.
unfold pi_func_ext0.
destruct (X0 x0 i); simpl.
case o.
intro.
destruct H4.
contradiction H1.
tauto.

assert (forall (x1 x2:X) (i1:In pi_dom_ext x1) (i2:In pi_dom_ext x2),
  pi_func_ext0 x1 i1 = pi_func_ext0 x2 i2 -> x1 = x2).
intros.
inversion i1.
inversion i2.
rewrite (H3 x1 H6 i1) in H5.
rewrite (H3 x2 H8 i2) in H5.
apply pi_inj in H5.
assumption.
destruct H8.
rewrite (H3 x1 H6 i1) in H5.
rewrite H4 in H5.
contradiction H2.
exists x1.
exists H6.
assumption.
destruct H6.
rewrite H4 in H5.
inversion i2.
rewrite (H3 x2 H6 i2) in H5.
contradiction H2.
exists x2.
exists H6.
symmetry; assumption.
destruct H6.
reflexivity.

pose (pi_ext := Build_partial_injection pi_dom_ext pi_func_ext0 H5).
assert (partial_injection_ord x pi_ext).
constructor.
unfold pi_ext; simpl.
unfold pi_dom_ext.
red; intros.
left.
assumption.
intros.
symmetry.
apply H3.

apply H in H6.
contradiction H1.
apply (pi_dom_inc _ _ H6).
simpl.
right.
auto with sets.
Qed.

Lemma types_comparable: (exists f:X->Y, injective f) \/
                        (exists f:Y->X, injective f).
Proof.
pose proof premaximal_partial_injection.
destruct H.
apply premaximal_pi_is_full_or_surj in H.
case H.
left.
assert (forall x0:X, In (pi_dom x) x0).
rewrite H0.
constructor.
exists (fun x0:X => pi_func x x0 (H1 x0)).
red; intros.
apply pi_inj in H2.
assumption.

right.
assert (forall y:Y, { x0:X | exists i:In (pi_dom x) x0, pi_func x x0 i = y }).
intro.
apply constructive_definite_description.
pose proof (H0 y).
destruct H1.
exists x0.
red; split.
assumption.
intros.
destruct H1.
destruct H2.
destruct H2.
apply pi_inj in H1.
assumption.

exists (fun y:Y => proj1_sig (X0 y)).
red; intros.
destruct X0 in H1; destruct X0 in H1; simpl in H1.
destruct e; destruct e0.
destruct H1.
assert (x4 = x5).
apply proof_irrelevance.
destruct H1.
destruct H2.
assumption.
Qed.

End le_cardinal_total.

Lemma le_cardinal_total: forall kappa lambda:Cardinal,
  le_cardinal kappa lambda \/ le_cardinal lambda kappa.
Proof.
intros.
destruct kappa.
destruct lambda.
pose proof (types_comparable T T0).
case H.
left.
destruct H0.
exists x.
assumption.
right.
destruct H0.
exists x.
assumption.
Qed.
