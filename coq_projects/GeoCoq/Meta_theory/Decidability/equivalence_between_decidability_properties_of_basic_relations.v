Require Export GeoCoq.Tarski_dev.Ch04_col.
Require Import GeoCoq.Utils.all_equiv.

Section Equivalence_between_decidability_properties_of_basic_relations.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_dec_eq_dec :
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
    intros H A B.
    elim (H A B A A); intro HCong.
      left; apply cong_identity with A; assumption.
    right; intro; subst; apply HCong.
    apply cong_pseudo_reflexivity.
Qed.

Lemma eq_dec_implies_l2_11 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C A' B' C',
  Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
intro eq_dec; intros.
induction (eq_dec A B).
subst B.
assert (A' = B') by (apply (cong_identity A' B' A); Cong).
subst; Cong.
apply cong_commutativity; apply (five_segment A A' B B' C C' A A'); Cong.
Qed.

Lemma eq_dec_implies_construction_uniqueness :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall Q A B C X Y,
  Q <> A -> Bet Q A X -> Cong A X B C -> Bet Q A Y -> Cong A Y B C -> X=Y.
Proof.
intro eq_dec; intros.
assert (Cong A X A Y) by eCong.
assert (Cong Q X Q Y) by (apply (eq_dec_implies_l2_11 eq_dec Q A X Q A Y);Cong).
assert(OFSC Q A X Y Q A X X) by (unfold OFSC;repeat split;Cong).
apply five_segment_with_def in H6; try assumption.
apply cong_identity with X; Cong.
Qed.

Lemma eq_dec_implies_outer_transitivity_between2 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D, Bet A B C -> Bet B C D -> B<>C -> Bet A C D.
Proof.
intro eq_dec; intros.
prolong A C x C D.
assert (x = D) by (apply (eq_dec_implies_construction_uniqueness eq_dec B C C D); try apply (between_exchange3 A B C x); Cong).
subst x;assumption.
Qed.

Lemma eq_dec_implies_between_exchange4 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D, Bet A B C -> Bet A C D -> Bet A B D.
Proof.
intro eq_dec; intros.
induction (eq_dec B C); [subst; auto|].
apply between_symmetry;
apply eq_dec_implies_outer_transitivity_between2 with C; eBetween.
Qed.

Lemma eq_dec_implies_two_distinct_points :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  exists X, exists Y: Tpoint, X <> Y.
Proof.
intro eq_dec.
assert (ld:=lower_dim_ex).
ex_elim ld A.
ex_elim H B.
ex_elim H0 C.
induction (eq_dec A B).
subst A; exists B; exists C; Between.
exists A; exists B; assumption.
Qed.

Lemma eq_dec_implies_point_construction_different :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B, exists C, Bet A B C /\ B <> C.
Proof.
intro eq_dec; intros.
assert (tdp := eq_dec_implies_two_distinct_points eq_dec).
ex_elim tdp x.
ex_elim H y.
prolong A B F x y.
exists F.
show_distinct B F.
intuition.
intuition.
Qed.

Lemma eq_dec_implies_l4_2 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D A' B' C' D', IFSC A B C D A' B' C' D' -> Cong B D B' D'.
Proof.
unfold IFSC.
intro eq_dec; intros.
spliter.

induction (eq_dec A C).

treat_equalities;assumption.

assert (exists E, Bet A C E /\ C <> E)
 by (apply eq_dec_implies_point_construction_different; auto).
ex_and H6 E.
prolong A' C' E' C E.

assert  (Cong E D E' D')
 by (
  apply (five_segment_with_def A C E D A' C' E' D');[
  unfold OFSC;  repeat split;Cong|
  assumption]).

apply (five_segment_with_def E C B D E' C' B' D').
unfold OFSC.
repeat split; try solve [eBetween| Cong ].
auto.
Qed.

Lemma eq_dec_implies_l4_5 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C A' C',
  Bet A B C -> Cong A C A' C' ->
  exists B', Bet A' B' C' /\ Cong_3 A B C A' B' C'.
Proof.
intro eq_dec; intros.
unfold Cong_3.

assert (exists D', Bet C' A' D' /\ A' <> D')
 by (apply eq_dec_implies_point_construction_different; auto).
ex_and H1 x'.
prolong x' A' B' A B.
prolong x' B' C'' B C.

assert (Bet A' B' C'') by eBetween.

assert (C'' = C').
eapply (eq_dec_implies_construction_uniqueness eq_dec x' A' ).

auto.

apply eq_dec_implies_between_exchange4 with B'; auto.

apply (eq_dec_implies_l2_11 eq_dec A' B' C'' A B C);Between.

eBetween.
Cong.

subst C''.
exists B'.
repeat split;Cong.
Qed.

Lemma eq_dec_implies_l4_6 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C A' B' C', Bet A B C -> Cong_3 A B C A' B' C' -> Bet A' B' C'.
Proof.
unfold Cong_3.
intro eq_dec; intros.
assert (exists B'', Bet A' B'' C' /\ Cong_3 A B C A' B'' C')
  by (eapply eq_dec_implies_l4_5;intuition).
ex_and H1 x.
unfold Cong_3 in *;spliter.

assert (Cong_3 A' x C' A' B' C')
 by (unfold Cong_3;repeat split;eCong).
unfold Cong_3 in H7;spliter.

assert (IFSC A' x C' x  A' x C' B')
 by (unfold IFSC;repeat split;Cong).
assert (Cong x x x B')
 by (eapply eq_dec_implies_l4_2; try apply H10; auto).
Between.
Qed.

Lemma eq_dec_implies_l4_16 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D A' B' C' D',
  FSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
unfold FSC.
unfold Col.
intro eq_dec; intros.
decompose [or and] H; clear H.
assert (Bet A' B' C') by (eapply eq_dec_implies_l4_6;eauto).
unfold Cong_3 in *; spliter.
assert(OFSC A B C D A' B' C' D') by (unfold OFSC;repeat split; assumption).
eapply five_segment_with_def; eauto.
assert(Bet B' C' A') by (apply (eq_dec_implies_l4_6 eq_dec B C A B' C' A'); Cong;auto with cong3).
apply (eq_dec_implies_l4_2 eq_dec B C A D B' C' A' D').
unfold IFSC; unfold Cong_3 in *; spliter; repeat split;Between;Cong.
assert (Bet C' A' B') by (eapply (eq_dec_implies_l4_6 eq_dec C A B C' A' B'); auto with cong3).
eapply (five_segment_with_def B A C D B' A'); unfold OFSC; unfold Cong_3 in *; spliter; repeat split; Between; Cong.
Qed.

Lemma eq_dec_implies_l4_17 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C P Q,
  A<>B -> Col A B C -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q.
Proof.
intros.
assert (FSC A B C P A B C Q) by (unfold FSC; unfold Cong_3; repeat split;Cong).
eapply eq_dec_implies_l4_16; eauto.
Qed.

Lemma eq_dec_implies_l5_1 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet A C D \/ Bet A D C.
Proof.
intro eq_dec; intros.
prolong A D C' C D.
prolong A C D' C D.
prolong A C' B' C B.
prolong A D' B'' D B.
assert (Cong B C' B'' C).
apply (eq_dec_implies_l2_11 eq_dec B D C' B'' D' C).
apply between_exchange3 with A; Between.
apply between_inner_transitivity with A; Between.
Cong.
apply cong_transitivity with C D; Cong.
assert (Cong B B' B'' B).
  {
  apply (eq_dec_implies_l2_11 eq_dec B C' B' B'' C B); Cong.

    {
    assert (Bet A B C'); [|eBetween].
    induction (eq_dec B D); [treat_equalities; auto|].
    apply between_symmetry.
    apply eq_dec_implies_outer_transitivity_between2 with D; eBetween.
    }

    {
    induction (eq_dec C D'); [treat_equalities; eBetween|].
    apply eq_dec_implies_outer_transitivity_between2 with D'; eBetween.
    }
  }
assert(B'' =  B').
apply (eq_dec_implies_construction_uniqueness eq_dec A B B B''); try Cong.
apply eq_dec_implies_between_exchange4 with D'; Between;
apply eq_dec_implies_between_exchange4 with C; Between.
apply eq_dec_implies_between_exchange4 with C'; Between;
apply eq_dec_implies_between_exchange4 with D; Between.
subst B''.
assert (FSC B C D' C' B' C' D C).
unfold FSC.
repeat split; unfold Col; try Cong.
left; apply between_exchange3 with A; Between.
apply (eq_dec_implies_l2_11 eq_dec B C D' B' C' D); Cong.
apply between_exchange3 with A; assumption.
apply between_symmetry.
apply between_exchange3 with A; assumption.
apply cong_transitivity with C D; Cong.
apply cong_transitivity with C D; Cong.
induction (eq_dec B C).
subst C; auto.
assert (Cong D' C' D C) by (eapply eq_dec_implies_l4_16; try apply H12; assumption).
assert (exists E, Bet C E C' /\ Bet D E D') by (apply inner_pasch with A; Between).
ex_and H15 E.
assert (IFSC D E D' C D E D' C') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
assert (IFSC C E C' D C E C' D') by (unfold IFSC; repeat split; Cong; apply cong_transitivity with C D; Cong).
assert (Cong E C E C') by (eapply eq_dec_implies_l4_2; try apply H17; auto).
assert (Cong E D E D') by (eapply eq_dec_implies_l4_2; try apply H18; auto).
induction (eq_dec C C').
subst C'; right; assumption.
show_distinct C D'; intuition.
prolong C' C P C D'.
prolong D' C R C E.
prolong P R Q R P.
assert (FSC D' C R P P C E D').
unfold FSC.
unfold Cong_3.
assert_cols.
repeat split; Cong.
apply eq_dec_implies_l2_11 with C C; Cong.
apply between_inner_transitivity with C'; Between.
assert (Cong R P E D') by (eauto using eq_dec_implies_l4_16).
assert (Cong R Q E D).
eapply cong_transitivity.
apply cong_transitivity with R P; Cong.
apply cong_transitivity with E D'; Cong.
assert (FSC D' E D C P R Q C).
unfold FSC.
repeat split; Cong.
unfold Col; Between.
eapply (eq_dec_implies_l2_11 eq_dec D' E D P R Q); Between; Cong.
assert (Cong D C Q C).
induction (eq_dec D' E).
unfold FSC, IFSC, Cong_3 in *; spliter; treat_equalities; Cong.
apply eq_dec_implies_l4_16 with D' E P R; assumption.
assert (Cong C P C Q).
unfold FSC in *;unfold Cong_3 in *.
spliter.
apply cong_transitivity with C D.
apply cong_transitivity with C D'; Cong.
Cong.
show_distinct R C.
intuition.
assert (Cong D' P D' Q) by (apply (eq_dec_implies_l4_17 eq_dec R C); unfold Col; Between; Cong).
assert (Cong B P B Q).
apply eq_dec_implies_l4_17 with C D'; try assumption.
unfold Col; right;right.
apply between_exchange3 with A; assumption.
assert (Cong B' P B' Q).
eapply (eq_dec_implies_l4_17 eq_dec C D'); Cong.
unfold Col; left.
apply between_exchange3 with A; assumption.
assert (Cong C' P C' Q).
induction(eq_dec B B').
subst B'.
unfold IFSC,FSC, Cong_3 in *.
spliter.
clean_duplicated_hyps.
clean_trivial_hyps.
apply eq_dec_implies_l4_17 with C D'; try assumption.
unfold Col; left.
apply between_exchange3 with A; try assumption.
apply eq_dec_implies_between_exchange4 with B; try assumption.
apply eq_dec_implies_between_exchange4 with D; assumption.
eapply eq_dec_implies_l4_17 with B B'; Cong.
unfold Col; right; left.
apply between_symmetry.
apply between_exchange3 with A; try assumption.
apply eq_dec_implies_between_exchange4 with D; assumption.
assert (Cong P P P Q).
apply eq_dec_implies_l4_17 with C C'; try assumption.
unfold Col; right; right.
apply between_symmetry; assumption.
unfold IFSC,FSC, Cong_3 in *; spliter.
treat_equalities.
Between.
Qed.

Lemma eq_dec_implies_l5_2 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C D,
  A<>B -> Bet A B C -> Bet A B D -> Bet B C D \/ Bet B D C.
Proof.
intros.
assert (Bet A C D \/ Bet A D C) by (eapply eq_dec_implies_l5_1; eauto).
induction H3.
left; eBetween.
right; eBetween.
Qed.

Lemma eq_dec_implies_segment_construction_2 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A Q B C, A<>Q -> exists X, (Bet Q A X \/ Bet Q X A) /\ Cong Q X B C.
Proof.
intro eq_dec; intros.
prolong A Q A' A Q.
prolong A' Q X B C.
exists X.
show_distinct A' Q.
solve [intuition].
split; try assumption.
eapply (eq_dec_implies_l5_2 eq_dec A' Q); Between.
Qed.

Lemma eq_dec_implies_between_cong :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B C, Bet A C B -> Cong A C A B -> C=B.
Proof.
intros.
assert (Bet A B C).
eapply eq_dec_implies_l4_6 with A C B; unfold Cong_3; repeat split; Cong.
eapply between_equality; eBetween.
Qed.

Lemma eq_dec_cong_dec :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C D, Cong A B C D \/ ~ Cong A B C D).
Proof.
intro eq_dec; intros.
elim (eq_dec A B); intro; subst; elim (eq_dec C D); intro; subst.
left; Cong.
right; intro; apply H; apply cong_identity with B; Cong.
right; intro; apply H; apply cong_identity with D; Cong.
elim (eq_dec_implies_segment_construction_2 eq_dec B A C D).
intros D' HD'.
spliter.
elim (eq_dec B D');intro.
subst; left; assumption.
right; intro.
assert (Cong A D' A B) by eCong.
elim H1; intro; clear H1.
assert (B = D') by (apply (eq_dec_implies_between_cong eq_dec A D' B); Cong).
subst;intuition.
assert (D'=B) by (apply (eq_dec_implies_between_cong eq_dec A B D');assumption).
subst;intuition.
intuition.
Qed.

Lemma bet_dec_eq_dec :
  (forall A B C, Bet A B C \/ ~ Bet A B C) ->
  (forall A B:Tpoint, A=B \/ A<>B).
Proof.
intros.
induction (H A B A).
left; apply between_identity; assumption.
right; intro; subst; apply H0;  apply between_trivial.
Qed.

Lemma eq_dec_implies_between_cong_3 :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  forall A B D E, A <> B -> Bet A B D -> Bet A B E -> Cong B D B E -> D = E.
Proof.
intro eq_dec; intros.
assert (T:=eq_dec_implies_l5_2 eq_dec A B D E H H0 H1).
elim T; intro; clear T.
apply eq_dec_implies_between_cong with B; Cong.
symmetry; apply eq_dec_implies_between_cong with B; Cong.
Qed.

Lemma eq_dec_bet_dec :
  (forall A B:Tpoint, A=B \/ A<>B) ->
  (forall A B C, Bet A B C \/ ~ Bet A B C).
Proof.
intro eq_dec; intros.
elim (segment_construction A B B C); intros C' HC'.
spliter.
elim (eq_dec C C'); intro.
subst; tauto.
elim (eq_dec A B);intro.
left; subst; Between.
right; intro; apply H1; apply eq_dec_implies_between_cong_3 with A B; Cong.
Qed.

Definition decidability_of_equality_of_points := forall A B:Tpoint, A=B \/ A<>B.

Definition decidability_of_congruence_of_points := forall A B C D:Tpoint,
  Cong A B C D \/ ~ Cong A B C D.

Definition decidability_of_betweenness_of_points := forall A B C:Tpoint,
  Bet A B C \/ ~ Bet A B C.

Theorem equivalence_between_decidability_properties_of_basic_relations :
  all_equiv  (decidability_of_equality_of_points::
              decidability_of_congruence_of_points::
              decidability_of_betweenness_of_points::nil).
Proof.
unfold all_equiv.
simpl.
intros.
assert (P:=cong_dec_eq_dec).
assert (Q:=eq_dec_cong_dec).
assert (R:=bet_dec_eq_dec).
assert (S:=eq_dec_bet_dec).
decompose [or] H;clear H;decompose [or] H0;clear H0;subst; tauto.
Qed.

End Equivalence_between_decidability_properties_of_basic_relations.
