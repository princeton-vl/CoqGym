Require Export Classical.
Require Import ClassicalChoice.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Import Proj1SigInjective.
Require Import InverseImage.

Section ZL'.

Variable T:Type.
Variable R:relation T.
Hypothesis ord:order R.
Definition chain (S: Ensemble T) : Prop :=
  forall x y:T, In S x -> In S y -> (R x y \/ R y x).
Definition maximal (x:T) : Prop :=
  forall y:T, R x y -> x = y.
Variable chain_sup: forall S: Ensemble T, chain S ->
  { x:T | (forall y:T, In S y -> R y x) /\
    (forall z:T, (forall y:T, In S y -> R y z) -> R x z) }.
Variable inflation: forall x:T,
  { y:T | R x y /\ x <> y /\ forall z:T, R x z -> R z y ->
                                     z = x \/ z = y }.

Inductive tower : Ensemble T :=
  | sup_intro: forall (S: Ensemble T), Included S tower ->
      forall c:chain S,
      In tower (proj1_sig (chain_sup S c))
  | inflation_intro: forall x:T, In tower x ->
      In tower (proj1_sig (inflation x)).

Lemma tower_is_chain: chain tower.
Proof.
unfold chain.
intros.
revert x H.
induction H0.
intros.
case (classic (forall y:T, In S y -> R y x)).
right.
apply (proj2_sig (chain_sup S c)).
assumption.

intro.
apply not_all_ex_not in H2.
destruct H2.
apply imply_to_and in H2.
destruct H2.
left.
apply (ord_trans ord) with x0.
pose proof (H0 x0 H2 x H1).
tauto.
apply (proj2_sig (chain_sup S c)).
assumption.

pose proof (proj2_sig (inflation x)).
simpl in H0.
destruct H0.
destruct H1.
remember (proj1_sig (inflation x)) as x'.

assert (forall y:T, In tower y -> R y x \/ R x' y).
intros.
induction H3.
case (classic (forall x0:T, In S x0 -> R x0 x)).
left.
apply (proj2_sig (chain_sup S c)).
assumption.

right.
apply not_all_ex_not in H5.
destruct H5.
apply imply_to_and in H5.
destruct H5.
apply (ord_trans ord) with x0.
pose proof (H4 x0).
tauto.
apply (proj2_sig (chain_sup S c)).
assumption.

assert (In tower x').
rewrite Heqx'.
apply inflation_intro.
assumption.

destruct IHtower0.
assert (In tower (proj1_sig (inflation x0))).
apply inflation_intro.
assumption.
case (IHtower (proj1_sig (inflation x0)) H6).
left.
assumption.
intro.
pose proof (proj2_sig (inflation x0)).
simpl in H8.
assert (x = x0 \/ x = proj1_sig (inflation x0)).
apply H8.
assumption.
assumption.
case H9.
right.
rewrite Heqx'.
rewrite H10.
apply (ord_refl ord).
left.
rewrite H10.
apply (ord_refl ord).
right.
apply (ord_trans ord) with x0.
assumption.
apply (proj2_sig (inflation x0)).

intros.
case (H3 x0 H4).
left.
apply (ord_trans ord) with x.
assumption.
assumption.
right.
assumption.
Qed.

(* can now show the given hypotheses are contradictory *)
Lemma ZL': False.
Proof.
pose proof (proj2_sig (chain_sup tower tower_is_chain)).
simpl in H.
remember (proj1_sig (chain_sup tower tower_is_chain)) as x0.
assert (In tower x0).
rewrite Heqx0.
constructor 1.
auto with sets.

pose (x' := proj1_sig (inflation x0)).
assert (In tower x').
constructor 2.
assumption.

pose proof (proj2_sig (inflation x0)).
simpl in H2.
destruct H2.
destruct H3.
contradict H3.
apply (ord_antisym ord).
assumption.
destruct H.
apply H.
assumption.
Qed.

End ZL'.

Arguments chain {T}.
Arguments maximal {T}.

Section ZL.

(* get rid of the need for a sup function and immediate successors *)

Variable T:Type.
Variable R:relation T.
Hypothesis ord: order R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S ->
  exists x:T, forall y:T, In S y -> R y x.

Definition chains := {S:Ensemble T | chain R S}.
Definition chains_ord := (fun S1 S2:chains =>
  Included (proj1_sig S1) (proj1_sig S2)).

Lemma chains_order: order chains_ord.
Proof.
constructor.
unfold reflexive.
unfold chains_ord.
auto with sets.

unfold transitive.
unfold chains_ord.
auto with sets.

unfold antisymmetric.
unfold chains_ord.
intros.
apply proj1_sig_injective.
auto with sets.
Qed.

Require Export EnsemblesSpec.

Definition chains_sup_def : forall F: Ensemble chains,
  chain chains_ord F -> chains.
refine (fun F H => exist _ [ x:T | exists S:chains, In F S /\
                             In (proj1_sig S) x ] _).
red; intros.
destruct H0.
destruct H1.
destruct H0.
destruct H1.
pose proof (H x0 x1).
destruct x0.
destruct x1.
simpl in H0.
destruct H0.
simpl in H1.
destruct H1.
apply H2 in H0.
unfold chains_ord in H0.
simpl in H0.
destruct H0.
apply c0.
apply H0.
exact H3.
exact H4.

apply c.
exact H3.
apply H0.
exact H4.
assumption.
Defined.

Lemma chains_sup_correct: forall (F:Ensemble chains)
  (P:chain chains_ord F), let U := chains_sup_def F P in
    (forall S:chains, In F S -> chains_ord S U) /\
    (forall T:chains, (forall S:chains, In F S -> chains_ord S T) ->
      chains_ord U T).
Proof.
intros.
split.
intros.
unfold chains_ord.
unfold Included.
intros.
unfold U.
simpl.
constructor.
exists S.
auto.
intros.
unfold chains_ord.
unfold Included.
intros.
unfold U in H0.
simpl in H0.
destruct H0.
destruct H0.
destruct H0.
apply H in H0.
apply H0.
assumption.
Qed.

Definition chains_sup (F:Ensemble chains) (P:chain chains_ord F) :=
  let U := chains_sup_def F P in
  exist (fun U:chains => 
    (forall S:chains, In F S -> chains_ord S U) /\
    (forall T:chains, (forall S:chains, In F S -> chains_ord S T) ->
      chains_ord U T))
  (chains_sup_def F P) (chains_sup_correct F P).

Theorem ZornsLemma: exists x:T, maximal R x.
Proof.
pose proof (ZL' chains chains_ord chains_order chains_sup).

apply NNPP.
unfold maximal.
dintuition.
assert (forall x:T, ~ forall y:T, R x y -> x = y).
apply not_ex_all_not.
exact H0.
assert (forall x:T, exists y:T, ~ (R x y -> x = y)).
intro.
apply not_all_ex_not.
apply H1.
assert (forall x:T, exists y:T, R x y /\ x <> y).
intro.
pose proof (H2 x).
destruct H3.
apply imply_to_and in H3.
exists x0.
assumption.
clear H0 H1 H2.

assert (forall x:chains, exists y:chains,
  chains_ord x y /\ x <> y /\ forall z:chains, chains_ord x z ->
  chains_ord z y -> z = x \/ z = y).
intro.
destruct x.
pose proof (ub_of_chain x c).
destruct H0.
pose proof (H3 x0).
destruct H1.

pose (x' := Add x x1).
assert (chain R x').
unfold chain.
intros.
case H2.
case H4.
intros.
apply c.
assumption.
assumption.
intros.
destruct H5.
left.
apply ord_trans with x0.
apply H0.
assumption.
apply H1.
intros.
destruct H5.
case H4.
right.
apply ord_trans with x0.
apply H0.
assumption.
apply H1.
intros.
destruct H5.
left.
apply ord_refl.

exists (exist _ x' H2).
split.
unfold chains_ord.
simpl.
unfold Included.
intros.
constructor.
assumption.

split.
intuition.
injection H4.
intro.
assert (In x x1).
rewrite H1.
constructor 2.
auto with sets.
contradict H6.
apply ord_antisym.
assumption.
apply H0.
assumption.

intros.
destruct z.
unfold chains_ord in H4.
simpl in H4.
unfold chains_ord in H5.
simpl in H5.

case (classic (In x2 x1)).
right.
apply subset_eq_compatT.
apply Extensionality_Ensembles.
split.
assumption.
unfold Included.
intros.
case H7.
exact H4.
intros.
destruct H8.
assumption.

left.
apply subset_eq_compatT.
apply Extensionality_Ensembles.
split.
unfold Included.
intros.
assert (In x' x3).
apply H5.
assumption.
inversion H8.
assumption.
destruct H9.
contradiction H6.
assumption.

apply choice in H0.
destruct H0 as [f].
apply H.
intro.
apply exist with (f x).
apply H0.
Qed.

End ZL.

Arguments ZornsLemma {T}.

Require Import Quotients.

Section ZL_preorder.

Variable T:Type.
Variable R:relation T.
Hypothesis Rpreord: preorder R.
Hypothesis ub_of_chain: forall S:Ensemble T, chain R S ->
  exists x:T, forall y:T, In S y -> R y x.

Definition premaximal (x:T) : Prop :=
  forall y:T, R x y -> R y x.

Lemma ZornsLemmaForPreorders: exists x:T, premaximal x.
Proof.
pose (Requiv (x y:T) := R x y /\ R y x).
assert (equivalence Requiv).
constructor.
red; intros.
split; apply preord_refl; trivial.
red; intros.
destruct H.
destruct H0.
split; apply preord_trans with y; trivial.
red; intros.
destruct H.
split; trivial.

pose (Rquo := quotient Requiv).
let Hnew:=fresh"_H" in
  unshelve refine (let Hnew:=_ in
     let inducedR := induced_function2arg R H H Hnew in
     let inducedR_prop := induced_function2arg_correct R H H Hnew in _).
intros.
assert (True_rect (R a1 b1) = True_rect (R a2 b2)).
apply Extensionality_Ensembles; split; red; intros.
destruct x.
red in H2.
simpl in H2.
red; simpl.
apply preord_trans with a1; trivial.
apply H0.
apply preord_trans with b1; trivial.
apply H1.
destruct x.
red in H2; simpl in H2.
red; simpl.
apply preord_trans with a2; trivial.
apply H0.
apply preord_trans with b2; trivial.
apply H1.
assert (True_rect (R a1 b1) I = True_rect (R a2 b2) I).
rewrite H2; trivial.
simpl in H3.
assumption.
clearbody inducedR_prop.
fold inducedR in inducedR_prop.

assert (exists x:Rquo, maximal inducedR x).
apply ZornsLemma.
constructor.
red; intros xbar.
destruct (quotient_projection_surjective xbar) as [x []].
rewrite inducedR_prop.
apply preord_refl; trivial.
red; intros xbar ybar zbar ? ?.
destruct (quotient_projection_surjective xbar) as [x].
destruct H2.
destruct (quotient_projection_surjective ybar) as [y].
destruct H2.
destruct (quotient_projection_surjective zbar) as [z].
destruct H2.
rewrite inducedR_prop in H0, H1.
rewrite inducedR_prop.
apply preord_trans with y; trivial.
red; intros xbar ybar ? ?.
destruct (quotient_projection_surjective xbar) as [x].
destruct H2.
destruct (quotient_projection_surjective ybar) as [y].
destruct H2.
rewrite inducedR_prop in H0, H1.
unfold quotient_projection.
apply subset_eq_compatT.
apply R_impl_equality_of_equiv_class; trivial.
split; trivial.

intros Sbar ?.
pose (S := inverse_image (quotient_projection _) Sbar).
unshelve refine (let H1:=ub_of_chain S _ in _).
red; intros.
pose proof (H0 (quotient_projection _ x) (quotient_projection _ y)).
rewrite 2 inducedR_prop in H3.
destruct H1.
destruct H2.
apply H3; trivial.

destruct H1.
exists (quotient_projection _ x).
intros ybar ?.
destruct (quotient_projection_surjective ybar) as [y].
destruct H3.
rewrite inducedR_prop.
apply H1.
constructor; exact H2.

destruct H0 as [xbar].
destruct (quotient_projection_surjective xbar) as [x].
destruct H1.
exists x.
red; intros.
red in H0.
unshelve refine (let H2:=H0 (quotient_projection Requiv y) _ in _).
rewrite inducedR_prop.
assumption.
unfold quotient_projection in H2.
injection H2; intros.
assert (In (equiv_class Requiv x) y).
rewrite H3.
constructor; apply equiv_refl; trivial.
destruct H4.
apply H4.
Qed.

End ZL_preorder.

Arguments premaximal {T}.
