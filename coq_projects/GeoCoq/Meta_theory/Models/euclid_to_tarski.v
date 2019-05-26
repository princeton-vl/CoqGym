Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Elements.OriginalProofs.proposition_01.
Require Import GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Import GeoCoq.Elements.OriginalProofs.lemma_extension.
Require Import Classical.

Section Euclid_to_Tarski.

Context `{Ax:euclidean_neutral_ruler_compass}.

Definition Bet A B C := BetS A B C \/ A=B \/ B=C.

Lemma Bet_sym : forall A B C,
  Bet A B C -> Bet C B A.
Proof.
intros.
unfold Bet in *.
decompose [or] H.
left.
eauto using axiom_betweennesssymmetry.
right;right;auto.
right;left;auto.
Qed.

Definition TCong A B C D := Cong A B C D \/ (A=B /\ C=D).

Lemma cong_sym : forall A B C D, Cong A B C D -> Cong C D A B.
Proof.
intros.
apply (cn_congruencetransitive C D A B A B).
assumption.
apply (cn_congruencereflexive).
Qed. 

Lemma cong_eq : forall A B C, Cong B C A A -> B=C.
Proof.
intros.
destruct (classic (B=C)).
assumption.
assert (A<>A).
apply axiom_nocollapse with B C;auto.
intuition.
Qed.

Lemma nullsegment2 : forall A B, TCong A A B B.
Proof.
intros.
unfold TCong;auto.
Qed.

Lemma Tcong_reflexive: forall A B, TCong A B A B.
Proof.
intros.
unfold TCong.
left.
apply cn_congruencereflexive.
Qed.

Lemma Tcong_symmetric: forall A B C D, TCong A B C D -> TCong C D A B.
Proof.
intros.
unfold TCong in *.
destruct  H.
left.
apply cong_sym.
assumption.
right;intuition.
Qed.

Lemma nullsegment1 : forall A B C, TCong A A B C -> B=C.
Proof.
intros.
unfold TCong in *.
destruct H.
apply cong_sym in H.
apply cong_eq in H.
assumption.
intuition.
Qed.

Lemma TCong_neq_Cong : forall A B C D, A<>B -> TCong A B C D -> Cong A B C D.
Proof.
intros.
destruct H0.
assumption.
intuition.
Qed.

Lemma lemma_congruenceflip : 
   forall A B C D, 
   Cong A B C D ->
   Cong B A D C.
Proof.
intros.
assert (Cong B A A B) by (auto using cn_equalityreverse).
assert (Cong C D D C) by (auto using cn_equalityreverse).
assert (Cong B A C D) by (conclude lemma_congruencetransitive).
conclude lemma_congruencetransitive.
Qed.


Instance Tarski_follows_Euclid: Tarski_neutral_dimensionless.
Proof.
eapply (Build_Tarski_neutral_dimensionless Point Bet TCong) with (PA:=PA) (PB:=PB) (PC:=PC).
- intros.
  unfold TCong.
  left; apply cn_equalityreverse.
- intros.
  unfold TCong in *.
  destruct H;destruct H0.
  left;apply cn_congruencetransitive with A B;auto.
  spliter;subst.
  apply cong_sym in H.
  apply cong_eq in H.
  subst;auto.
  spliter;subst.
   apply cong_sym in H0.
  apply cong_eq in H0.
  subst;auto.
  spliter;subst.
  auto.
- intros.
  unfold TCong in *.
  destruct H.
  apply cong_eq with C.
  assumption.
  intuition.
- intros.
  elim (classic (C=D));intro.
  subst.
  exists B.
  split.
  unfold Bet;auto.
  apply nullsegment2.
  elim (classic (A=B));intro.
  subst.
  elim (classic (B=C));intro.
  * subst.
    exists D.
    split.
    unfold Bet;right;auto.
    apply Tcong_reflexive.
  * destruct (lemma_extension  C B C D) as [X [HXA HXB]];unfold neq;auto.
    exists X.
    split.
    unfold Bet;right;auto.
    unfold TCong;auto.
  * destruct (lemma_extension A B C D) as [X [HXA HXB]];
  unfold neq;auto.
  exists X.
  unfold Bet, TCong;auto. 
- intros.
  elim (classic (B=C));intro.
  subst.
  assert (B'=C'). 
  apply nullsegment1 with C;assumption.
  subst.
  assumption.
  assert (B'<>C').
  {
  intro;subst.
  apply H6.
  apply nullsegment1 with C'.
  apply Tcong_symmetric.
  assumption.
  }
  assert (A'<>B').
  {
  intro;subst.
  apply H5.
  apply nullsegment1 with B'.
  apply Tcong_symmetric.
  assumption.
  }
 apply TCong_neq_Cong in H0;auto.
 apply TCong_neq_Cong in H;auto.
 destruct (classic (A=D)).
 * subst.
   assert (A'=D') by (apply nullsegment1 with D;auto).
   subst.
   unfold TCong.
   left.
   apply cn_sumofparts with B B'.
   apply lemma_congruenceflip;auto.
   apply lemma_congruenceflip;auto.
   unfold Bet in H3.
   apply axiom_betweennesssymmetry.
   destruct H3;intuition.
   apply axiom_betweennesssymmetry.
   destruct H4;intuition.
 * assert (A'<>D').
  {
  intro;subst.
  apply H9.
  apply nullsegment1 with D'.
  apply Tcong_symmetric.
  assumption.
  }
  apply TCong_neq_Cong in H1;auto.
  destruct (classic (B=D)).
  subst.
  assert (B'=D').
  apply nullsegment1 with D.
  assumption.
  subst.
  unfold TCong.
  left.
  apply lemma_congruenceflip;assumption.
 apply TCong_neq_Cong in H2;auto.
 assert (Cong D C D' C').
 apply (axiom_5_line A B C D A' B' C' D' H0 H1 H2);try assumption.
 unfold Bet in *.
 intuition.
 unfold Bet in *.
 intuition.
 unfold TCong;left.
 apply (lemma_congruenceflip);auto.
- intros.
  unfold Bet in *.
  destruct H.
  exfalso.
  apply (axiom_betweennessidentity A B);auto.
  intuition.
- intros A B C P Q H H0.
  destruct H.
  destruct H0.
  elim (classic (Col A B C));intro.
  unfold Col in *.
  decompose [or] H1;clear H1;
  unfold eq in *;subst.
  * exists B;split;unfold Bet;auto.
  * exfalso; apply lemma_betweennotequal in H.
    unfold neq,eq in *;spliter.
    intuition.
  * exfalso;apply lemma_betweennotequal in H0.
    unfold neq,eq in *;intuition.
  * exists A.
  split.
  unfold Bet;left. 
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  unfold Bet;auto.
  * exists B.
  split.
  unfold Bet;auto.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  * exists C.
  split.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  unfold Bet;left.
  eauto using lemma_3_6a, axiom_betweennesssymmetry.
  * assert (T:exists X : Point, BetS A X Q /\ BetS B X P).
   apply  (postulate_Pasch_inner A B C P Q H H0).
   unfold nCol,neq.
   unfold Col in *.
  assert (BetS B A C <-> BetS C A B)
     by (split;intro;apply axiom_betweennesssymmetry;auto).
  assert (eq C B <-> eq B C) by (split;unfold eq;intro;auto).
  tauto.
  destruct T as [X [HXA HXB]].
  exists X.
  split;unfold Bet;left;auto using axiom_betweennesssymmetry.
  * destruct H0.
  subst.
  exists Q;unfold Bet;auto.
  subst.
  exists P.
  unfold Bet;auto using axiom_betweennesssymmetry.
  * destruct H.
  subst;exists P; unfold Bet;auto.
  subst;exists Q;split.
  auto using Bet_sym.
  unfold Bet;auto.
- assert (T:=axiom_lower_dim).
  unfold nCol,Bet,neq,eq in *.
  intro;spliter.
  decompose [or] H;try
  solve [auto using  axiom_betweennesssymmetry].
Qed.

End Euclid_to_Tarski.


