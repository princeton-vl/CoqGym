Require Import Classical.
Require Export Ensembles.
Require Import EnsemblesImplicit.
Require Export Relation_Definitions.
Require Import Relation_Definitions_Implicit.
Require Import EnsemblesSpec.

Section MinimalElements.

Variable T:Type.
Variable R:relation T.

(* R is well-founded if and only if every nonempty subset of
   T has a minimal element *)

Definition minimal_element_property : Prop :=
  forall S:Ensemble T, Inhabited S -> exists x:T, In S x /\
    forall y:T, In S y -> ~ R y x.

Lemma WF_implies_MEP: well_founded R -> minimal_element_property.
Proof.
unfold well_founded.
unfold minimal_element_property.
intros WF S Hinh.
destruct Hinh.
revert x H.
apply (@well_founded_ind T R WF
 (fun x:T =>
  In S x -> exists y:T, In S y /\ (forall z:T, In S z -> ~ R z y))).
intros.
case (classic (forall y:T, In S y -> ~ R y x)).
exists x.
split.
assumption.
assumption.

intro.
apply not_all_ex_not in H1.
destruct H1.
apply imply_to_and in H1.
destruct H1.
apply H with x0.
apply NNPP.
assumption.
assumption.
Qed.

Lemma MEP_implies_WF: minimal_element_property -> well_founded R.
Proof.
unfold well_founded.
unfold minimal_element_property.
intro MEP.
apply NNPP.
intuition.
apply not_all_ex_not in H.
destruct H.
assert (Inhabited [x:T | ~ Acc R x]).
exists x.
constructor; assumption.
apply MEP in H0.
destruct H0.
destruct H0.
destruct H0.
contradict H0.
constructor.
intros.
apply NNPP.
intuition.
apply H1 with y.
constructor; assumption.
assumption.
Qed.

End MinimalElements.

Section DecreasingSequences.

(* R is well-founded if and only if there is no infinite strictly
   decreasing sequence of elements of T *)

Variable T:Type.
Variable R:relation T.

Definition decreasing_sequence_property :=
  forall a:nat->T, exists n:nat, ~ R (a (S n)) (a n).

Lemma WF_implies_DSP: well_founded R -> decreasing_sequence_property.
Proof.
unfold decreasing_sequence_property.
intros WF a.
remember (a 0) as a0.
revert a0 a Heqa0.
apply (well_founded_ind WF (fun x:T =>
  forall a:nat->T, x = a 0 -> exists n:nat, ~ R (a (S n)) (a n))).
intros.
case (classic (R (a 1) (a 0))).
intro.
pose (b := fun n:nat => a (S n)).
assert (exists n:nat, ~ R (b (S n)) (b n)).
apply H with (a 1).
rewrite H0.
assumption.
trivial.
destruct H2.
exists (S x0).
unfold b in H2.
assumption.

exists 0.
assumption.
Qed.

Require Import ClassicalChoice.

Lemma DSP_implies_WF: decreasing_sequence_property -> well_founded R.
Proof.
unfold decreasing_sequence_property.
intro DSP.
apply MEP_implies_WF.
unfold minimal_element_property.
intro S0.
intros.
apply NNPP.
intuition.
assert (forall x:T, In S0 x -> exists y:T, In S0 y /\ R y x).
intros.
apply NNPP.
intuition.
assert (forall y:T, ~(In S0 y /\ R y x)).
apply not_ex_all_not.
assumption.
apply H0.
exists x.
split.
assumption.
intros.
apply H3 with y.
tauto.

pose (S_type := {x:T | In S0 x}).
assert (exists f:S_type -> S_type, forall x:S_type,
  R (proj1_sig (f x)) (proj1_sig x)).
apply choice with (R:=fun x y:S_type => R (proj1_sig y) (proj1_sig x)).
intro.
destruct x.
simpl.
pose proof (H1 x i).
destruct H2.
destruct H2.
exists (exist (fun x:T => In S0 x) x0 H2).
simpl.
assumption.

destruct H2 as [f Hf].

destruct H.
pose (b := nat_rect (fun n:nat => S_type)
  (exist (fun x:T => In S0 x) x H)
  (fun (n:nat) (x:S_type) => f x)).
simpl in b.
pose (a := fun n:nat => (proj1_sig (b n))).
assert (forall n:nat, R (a (S n)) (a n)).
unfold a.
intro.
simpl.
apply Hf.

contradict DSP.
apply ex_not_not_all.
exists a.
apply all_not_not_ex.
auto.
Qed.

End DecreasingSequences.
