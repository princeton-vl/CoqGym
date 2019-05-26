Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Image.
Require Import ImageImplicit.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import Description.
Require Import ProofIrrelevance.
Require Import Proj1SigInjective.
Require Export EnsemblesSpec.

Set Implicit Arguments.
Section Quotient.
Variable A:Type.
Variable R:relation A.
Hypothesis equivR:equivalence R.

Definition equiv_class (x:A) : Ensemble A :=
  [ y:A | R x y ].

Lemma R_impl_equality_of_equiv_class:
  forall x y:A, R x y -> equiv_class x = equiv_class y.
Proof.
destruct equivR.
intros.
apply Extensionality_Ensembles; split; red; intros z ?.
constructor.
destruct H0.
apply equiv_trans with x; trivial.
apply equiv_sym; trivial.
destruct H0.
constructor.
apply equiv_trans with y; trivial.
Qed.

Lemma equality_of_equiv_class_impl_R:
  forall x y:A, equiv_class x = equiv_class y -> R x y.
Proof.
destruct equivR.
intros.
assert (In (equiv_class x) x).
constructor.
apply equiv_refl.
rewrite H in H0.
destruct H0.
apply equiv_sym.
assumption.
Qed.

Definition equiv_classes : Ensemble (Ensemble A) :=
  Im Full_set equiv_class.
Definition quotient : Type :=
  { S:Ensemble A | In equiv_classes S }.

Lemma equiv_class_in_quotient: forall x:A,
  In equiv_classes (equiv_class x).
Proof.
unfold equiv_classes.
intro.
apply Im_def.
constructor.
Qed.

Definition quotient_projection (x:A) : quotient :=
  exist _ (equiv_class x) (equiv_class_in_quotient x).

Lemma quotient_projection_correct: forall x:A,
  proj1_sig (quotient_projection x) = equiv_class x.
Proof.
trivial.
Qed.

Lemma quotient_projection_surjective: forall xbar:quotient,
  exists x:A, quotient_projection x = xbar.
Proof.
intro.
destruct xbar.
destruct i.
exists x.
unfold quotient_projection.
pose proof e.
symmetry in H; destruct H.
f_equal.
apply proof_irrelevance.
Qed.

Lemma quotient_projection_collapses_R: forall x1 x2:A,
  R x1 x2 -> quotient_projection x1 = quotient_projection x2.
Proof.
intros.
apply subset_eq_compatT.
apply R_impl_equality_of_equiv_class.
assumption.
Qed.

Lemma quotient_projection_minimally_collapses_R: forall x1 x2:A,
  quotient_projection x1 = quotient_projection x2 -> R x1 x2.
Proof.
intros.
apply equality_of_equiv_class_impl_R.
repeat rewrite <- quotient_projection_correct.
rewrite H.
reflexivity.
Qed.

End Quotient.

Section InducedFunction.

(* well-defined A->B induces a function A/R->B *)

Variable A B:Type.
Variable R:Relation A.
Variable f:A->B.
Hypothesis equiv:equivalence R.
Hypothesis well_defined: forall x y:A, R x y -> f x = f y.

Lemma description_of_fbar: forall xbar:quotient R, exists! y:B,
  exists x:A, quotient_projection R x = xbar /\ f x = y.
Proof.
intro.
pose proof (quotient_projection_surjective xbar).
destruct H.
exists (f x).
unfold unique.
split.
exists x.
tauto.
intros.
destruct H0.
destruct H0.
rewrite <- H1.
apply well_defined.
apply equality_of_equiv_class_impl_R; trivial.
transitivity (proj1_sig (quotient_projection R x)).
trivial.
rewrite H.
rewrite <- H0.
trivial.
Qed.

Definition induced_function (xbar:quotient R) : B :=
  proj1_sig (constructive_definite_description _
               (description_of_fbar xbar)).

Lemma induced_function_correct: forall x:A,
  induced_function (quotient_projection R x) = f x.
Proof.
intro.
unfold induced_function.
destruct constructive_definite_description.
simpl.
destruct e.
destruct H.
rewrite <- H0.
apply well_defined.
apply quotient_projection_minimally_collapses_R; trivial.
Qed.

Lemma induced_function_unique: forall fbar:quotient R->B,
  (forall x:A, fbar (quotient_projection R x) = f x) ->
  (forall xbar:quotient R, fbar xbar = induced_function xbar).
Proof.
intros.
destruct (quotient_projection_surjective xbar).
rewrite <- H0.
rewrite H.
rewrite induced_function_correct.
reflexivity.
Qed.

End InducedFunction.

Section InducedFunction2.

(* well-defined function A->B induces a function A/R->B/S *)

Variable A B:Type.
Variable R:relation A.
Variable S:relation B.
Variable f:A->B.
Hypothesis equivR: equivalence R.
Hypothesis equivS: equivalence S.
Hypothesis well_defined2: forall a1 a2:A, R a1 a2 -> S (f a1) (f a2).

Definition projf (a:A) : quotient S :=
  quotient_projection S (f a).
Lemma projf_well_defined: forall a1 a2:A,
  R a1 a2 -> projf a1 = projf a2.
Proof.
intros.
unfold projf.
apply quotient_projection_collapses_R; trivial.
apply well_defined2.
assumption.
Qed.

Definition induced_function2: quotient R -> quotient S :=
  induced_function projf equivR projf_well_defined.

Lemma induced_function2_correct: forall a:A,
  induced_function2 (quotient_projection R a) =
  quotient_projection S (f a).
Proof.
intros.
unfold induced_function2.
rewrite induced_function_correct.
reflexivity.
Qed.

End InducedFunction2.

Section InducedFunction2arg.

(* well-defined function A x B -> C induces a function
   (A/R) x (B/S) -> C *)

Variable A B C:Type.
Variable R:relation A.
Variable S:relation B.
Variable f:A->B->C.
Hypothesis equivR:equivalence R.
Hypothesis equivS:equivalence S.
Hypothesis well_defined_2arg: forall (a1 a2:A) (b1 b2:B),
  R a1 a2 -> S b1 b2 -> f a1 b1 = f a2 b2.

Lemma slices_well_defined: forall (a:A) (b1 b2:B),
  S b1 b2 -> f a b1 = f a b2.
Proof.
intros.
apply well_defined_2arg.
apply (equiv_refl equivR).
assumption.
Qed.

Definition induced1 (a:A) : quotient S -> C :=
   induced_function (f a) equivS (slices_well_defined a).

Definition eq_fn (f g:quotient S->C) :=
  forall b:quotient S, f b = g b.
Lemma eq_fn_equiv: equivalence eq_fn.
Proof.
constructor.
unfold reflexive.
unfold eq_fn.
reflexivity.
unfold transitive.
unfold eq_fn.
intros.
transitivity (y b).
apply H.
apply H0.
unfold symmetric.
unfold eq_fn.
symmetry.
apply H.
Qed.

Lemma well_defined_induced1: forall a1 a2:A, R a1 a2 ->
  eq_fn (induced1 a1) (induced1 a2).
Proof.
unfold eq_fn.
intros.
pose proof (quotient_projection_surjective b).
destruct H0.
rewrite <- H0.
unfold induced1.
rewrite induced_function_correct.
rewrite induced_function_correct.
apply well_defined_2arg.
assumption.
apply (equiv_refl equivS).
Qed.

Definition induced2 :=
  induced_function2 induced1 equivR eq_fn_equiv well_defined_induced1.

Definition eval (b:quotient S) (f:quotient S->C): C := f b.
Lemma well_defined_eval: forall (b:quotient S) (f g:quotient S->C),
  eq_fn f g -> eval b f = eval b g.
Proof.
intros.
unfold eval.
apply H.
Qed.

Definition induced_eval (b:quotient S) :=
  induced_function (eval b) eq_fn_equiv (well_defined_eval b).

Definition induced_function2arg (a:quotient R) (b:quotient S) : C :=
  induced_eval b (induced2 a).

Lemma induced_function2arg_correct: forall (a:A) (b:B),
  induced_function2arg (quotient_projection R a) (quotient_projection S b) =
  f a b.
Proof.
intros.
unfold induced_function2arg.
unfold induced_eval.
unfold induced2.
rewrite induced_function2_correct.
rewrite induced_function_correct.
unfold eval.
unfold induced1.
rewrite induced_function_correct.
reflexivity.
Qed.

End InducedFunction2arg.

Section InducedFunction3.

(* well-defined function A x B -> C induces a function
   (A/R) x (B/S) -> C/T *)

Variable A B C:Type.
Variable R:relation A.
Variable S:relation B.
Variable T:relation C.
Variable f:A->B->C.
Hypothesis equivR:equivalence R.
Hypothesis equivS:equivalence S.
Hypothesis equivT:equivalence T.
Hypothesis well_defined3: forall (a1 a2:A) (b1 b2:B),
  R a1 a2 -> S b1 b2 -> T (f a1 b1) (f a2 b2).

Definition projf2 (a:A) (b:B) :=
  quotient_projection T (f a b).

Lemma projf2_well_defined: forall (a1 a2:A) (b1 b2:B),
  R a1 a2 -> S b1 b2 -> projf2 a1 b1 = projf2 a2 b2.
Proof.
intros.
apply quotient_projection_collapses_R; trivial.
apply well_defined3.
assumption.
assumption.
Qed.

Definition induced_function3 : quotient R -> quotient S -> quotient T :=
  induced_function2arg projf2 equivR equivS projf2_well_defined.

Lemma induced_function3_correct: forall (a:A) (b:B),
  induced_function3 (quotient_projection R a)
                    (quotient_projection S b) =
  quotient_projection T (f a b).
Proof.
intros.
unfold induced_function3.
rewrite induced_function2arg_correct.
reflexivity.
Qed.

End InducedFunction3.
