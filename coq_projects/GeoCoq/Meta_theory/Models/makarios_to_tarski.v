Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.makarios_variant_axioms.

(** In this file we formalize the result given in T. J. M. Makarios:
 A further simplification of Tarski's axioms of geometry, June 2013. *)

Section Makarios_variant_to_Tarski83.

Context `{MTn:Tarski_neutral_dimensionless_variant_with_decidable_point_equality}.

Ltac prolong A B x C D :=
 assert (sg:= Msegment_construction A B C D);
 ex_and sg x.

Lemma Mcong_reflexivity : forall A B,
 CongM A B A B.
Proof.
intros.
prolong B A x A B.
eapply Mcong_inner_transitivity with A x;auto.
Qed.

Lemma Mcong_symmetry : forall A B C D ,
 CongM A B C D -> CongM C D A B.
Proof.
intros.
eapply Mcong_inner_transitivity.
apply H.
apply Mcong_reflexivity.
Qed.

Lemma between_trivial : forall A B, BetM A B B.
Proof.
intros.
prolong A B x B B.
assert (x = B)
 by (apply Mcong_identity in H0;auto).
subst;assumption.
Qed.

Lemma Mcong_trivial_identity : forall A B, CongM A A B B.
Proof.
  intros.
  assert (sg:= Msegment_construction A A B B);
  ex_and sg x.
  assert( A = x) by (eapply Mcong_identity;eauto).
  subst.
  assumption.
Qed.

Lemma LmCoghGrab : forall A B C D E F,
  A <> B -> BetM B A C -> BetM D A E ->
  CongM B A D A -> CongM A C A E -> CongM B F D F ->
  CongM F C E F.
Proof.
  intros.
  assert(CongM A F A F) by (eapply Mcong_reflexivity;eauto).
  assert(forall A A' B B' C C' D D':MTpoint,
   CongM A B A' B' -> CongM B C B' C' ->
   CongM A D A' D' -> CongM B D B' D' ->
   BetM A B C -> BetM A' B' C' -> A <> B ->
   CongM D C C' D') by apply Mfive_segment.
  apply (H6 B D A A);auto.
Qed.

Lemma cong_pre_pseudo_reflexivity : forall A B C D,
  C <> D -> BetM D C B -> CongM A B B A.
Proof.
  intros.
  assert(CongM C B C B) by (eapply Mcong_reflexivity;eauto).
  assert(CongM D C D C) by (eapply Mcong_reflexivity;eauto).
  assert(CongM D A D A) by (eapply Mcong_reflexivity;eauto).
  eapply LmCoghGrab;eauto.
Qed.

Lemma cong_pseudo_reflexivity : forall A B, CongM A B B A.
Proof.
  intros.
  elim (Mpoint_equality_decidability A B).
    intros.
    subst.
    eapply Mcong_trivial_identity;eauto.

    intros.
    assert(BetM B A A) by (eapply between_trivial;eauto).
    eapply Mcong_symmetry;eauto.
    eapply cong_pre_pseudo_reflexivity;eauto.
Qed.

Lemma five_segment : forall A A' B B' C C' D D',
  CongM A B A' B' ->
  CongM B C B' C' ->
  CongM A D A' D' ->
  CongM B D B' D' ->
  BetM A B C -> BetM A' B' C' -> A <> B ->
  CongM C D C' D'.
Proof.
  intros.
  assert(CongM D C C' D').
  intros.
  eapply Mfive_segment with A A' B B';assumption.
  assert(CongM D C C D).
  eapply cong_pseudo_reflexivity;eauto.
  eapply Mcong_inner_transitivity with D C;eauto.
Qed.

Instance Tarski_follows_from_Makarios_Variant : Tarski_neutral_dimensionless.
Proof.
exact (Build_Tarski_neutral_dimensionless
 MTpoint BetM CongM
 cong_pseudo_reflexivity
 Mcong_inner_transitivity
 Mcong_identity
 Msegment_construction
 five_segment
 Mbetween_identity
 Minner_pasch
 MPA MPB MPC
 Mlower_dim).
Defined.

Instance Tarski_follows_from_Makarios_Variant_with_decidable_point_equality' :
  Tarski_neutral_dimensionless_with_decidable_point_equality Tarski_follows_from_Makarios_Variant.
Proof. split; apply Mpoint_equality_decidability. Defined.

End Makarios_variant_to_Tarski83.