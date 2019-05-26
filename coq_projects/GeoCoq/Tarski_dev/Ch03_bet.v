Require Export GeoCoq.Tarski_dev.Ch02_cong.

Section T2_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma bet_col : forall A B C, Bet A B C -> Col A B C.
Proof.
    intros;unfold Col;auto.
Qed.

Lemma between_trivial : forall A B : Tpoint, Bet A B B.
Proof.
    intros.
    prolong A B x B B.
    assert (x = B) by (apply cong_reverse_identity with B; Cong).
    subst;assumption.
Qed.

Lemma between_symmetry : forall A B C : Tpoint, Bet A B C -> Bet C B A.
Proof.
    intros.
    assert (Bet B C C) by (apply between_trivial).
    assert(exists x, Bet B x B /\ Bet C x A) by (apply inner_pasch with C;auto).
    ex_and H1 x.
    apply between_identity in H1; subst; assumption.
Qed.

(** This lemma is used by tactics for trying several permutations. *)
Lemma Bet_cases :
 forall A B C,
 Bet A B C \/ Bet C B A ->
 Bet A B C.
Proof.
    intros.
    decompose [or] H; auto using between_symmetry.
Qed.

Lemma Bet_perm :
  forall A B C,
 Bet A B C ->
 Bet A B C /\ Bet C B A.
Proof.
    intros.
    auto using between_symmetry.
Qed.

Lemma between_trivial2 : forall A B : Tpoint, Bet A A B.
Proof.
    intros.
    apply between_symmetry.
    apply between_trivial.
Qed.

Lemma between_equality : forall A B C : Tpoint, Bet A B C -> Bet B A C -> A = B.
Proof.
    intros.
    assert (exists x, Bet B x B /\ Bet A x A) by (apply (inner_pasch A B C);assumption).
    ex_and H1 x.
    apply between_identity in H1.
    apply between_identity in H2.
    congruence.
Qed.

Lemma between_equality_2 : forall A B C : Tpoint, Bet A B C -> Bet A C B -> B = C.
Proof.
    intros.
    apply between_equality with A; auto using between_symmetry.
Qed.

Lemma between_exchange3 : forall A B C D, Bet A B C -> Bet A C D -> Bet B C D.
Proof.
intros.
assert (exists x, Bet C x C /\ Bet B x D)
  by (apply inner_pasch with A; apply between_symmetry; auto).
ex_and H1 x.
assert (C = x) by (apply between_identity; auto); subst; auto.
Qed.

Lemma bet_neq12__neq : forall A B C, Bet A B C -> A <> B -> A <> C.
Proof.
    intros A B C HBet HAB Heq.
    subst C; apply HAB, between_identity; trivial.
Qed.

Lemma bet_neq21__neq : forall A B C, Bet A B C -> B <> A -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq12__neq with B; auto.
Qed.

Lemma bet_neq23__neq : forall A B C, Bet A B C -> B <> C -> A <> C.
Proof.
    intros A B C HBet HBC Heq.
    subst C; apply HBC; symmetry.
    apply between_identity; trivial.
Qed.

Lemma bet_neq32__neq : forall A B C, Bet A B C -> C <> B -> A <> C.
Proof.
    intros A B C HBet HAB.
    apply bet_neq23__neq with B; auto.
Qed.

Lemma not_bet_distincts : forall A B C, ~ Bet A B C -> A <> B /\ B <> C.
Proof.
    intros A B C HNBet.
    repeat split; intro; subst B; apply HNBet.
      apply between_trivial2.
      apply between_trivial.
Qed.

End T2_1.

(** Some tactics *)

Ltac not_exist_hyp_perm_col A B C := not_exist_hyp (Col A B C); not_exist_hyp (Col A C B);
                                 not_exist_hyp (Col B A C); not_exist_hyp (Col B C A);
                                 not_exist_hyp (Col C A B); not_exist_hyp (Col C B A).

Ltac assert_cols :=
repeat
 match goal with
      | H:Bet ?X1 ?X2 ?X3 |- _ =>
     not_exist_hyp_perm_col X1 X2 X3;assert (Col X1 X2 X3) by (apply bet_col;apply H)
 end.

Ltac clean_trivial_hyps :=
  repeat
  match goal with
   | H:(Cong ?X1 ?X1 ?X2 ?X2) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X2 ?X1) |- _ => clear H
   | H:(Cong ?X1 ?X2 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Bet ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X1 ?X2) |- _ => clear H
   | H:(Col ?X2 ?X1 ?X1) |- _ => clear H
   | H:(Col ?X1 ?X2 ?X1) |- _ => clear H
end.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(Col ?A ?B ?C), H2 : Col ?A ?C ?B |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?A ?C |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?B ?C ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?B ?A |- _ => clear H2
   | H:(Col ?A ?B ?C), H2 : Col ?C ?A ?B |- _ => clear H2
   | H:(Bet ?A ?B ?C), H2 : Bet ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?A ?B ?D ?C |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?C ?D ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?B ?A |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?D ?C ?A ?B |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?C ?D |- _ => clear H2
   | H:(Cong ?A ?B ?C ?D), H2 : Cong ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
end.

Ltac clean := clean_trivial_hyps;clean_reap_hyps.

Ltac smart_subst X := subst X;clean.

Ltac treat_equalities_aux :=
  repeat
  match goal with
   | H:(?X1 = ?X2) |- _ => smart_subst X2
end.

Ltac treat_equalities :=
try treat_equalities_aux;
repeat
  match goal with
   | H:(Cong ?X3 ?X3 ?X1 ?X2) |- _ =>
      apply cong_symmetry in H; apply cong_identity in H;smart_subst X2
   | H:(Cong ?X1 ?X2 ?X3 ?X3) |- _ =>
      apply cong_identity in H;smart_subst X2
   | H:(Bet ?X1 ?X2 ?X1) |- _ => apply  between_identity in H;smart_subst X2
end.

Ltac show_distinct X Y := assert (X<>Y);[unfold not;intro;treat_equalities|idtac].

Hint Resolve between_symmetry bet_col : between.
Hint Resolve between_trivial between_trivial2 : between_no_eauto.

Ltac eBetween := treat_equalities;eauto with between.
Ltac Between := treat_equalities;auto with between between_no_eauto.

Section T2_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma between_inner_transitivity : forall A B C D, Bet A B D -> Bet B C D -> Bet A B C.
Proof.
    intros.
    assert (exists x, Bet B x B /\ Bet C x A) by (apply inner_pasch with D;auto).
    ex_and H1 x.
    Between.
Qed.

Lemma outer_transitivity_between2 : forall A B C D, Bet A B C -> Bet B C D -> B<>C -> Bet A C D.
Proof.
    intros.
    prolong A C x C D.
    assert (x = D) by (apply (construction_uniqueness B C C D); try apply (between_exchange3 A B C x); Cong).
    subst x;assumption.
Qed.

End T2_2.

Hint Resolve outer_transitivity_between2 between_inner_transitivity between_exchange3 : between.

Section T2_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma between_exchange2 : forall A B C D, Bet A B D -> Bet B C D -> Bet A C D.
Proof.
    intros.
    induction (eq_dec_points B C);eBetween.
Qed.

Lemma outer_transitivity_between : forall A B C D, Bet A B C -> Bet B C D -> B<>C -> Bet A B D.
Proof.
    intros.
    apply between_symmetry.
    apply (outer_transitivity_between2) with C; Between.
Qed.

Lemma between_exchange4 : forall A B C D, Bet A B C -> Bet A C D -> Bet A B D.
Proof.
    intros.
    apply between_symmetry.
    apply between_exchange2 with C; Between.
Qed.

End T2_3.

Hint Resolve between_exchange2 outer_transitivity_between between_exchange4 : between.

Section T2_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l3_9_4 : forall A1 A2 A3 A4, Bet_4 A1 A2 A3 A4 -> Bet_4 A4 A3 A2 A1.
Proof.
    unfold Bet_4.
    intros;spliter; auto with between.
Qed.

Lemma l3_17 : forall A B C A' B' P,
  Bet A B C -> Bet A' B' C -> Bet A P A' -> exists Q, Bet P Q C /\ Bet B Q B'.
Proof.
    intros.
    assert (exists Q', Bet B' Q' A /\ Bet P Q' C) by (eapply inner_pasch;eBetween).
    ex_and H2 x.
    assert (exists y, Bet x y C /\ Bet B y B') by (eapply inner_pasch;eBetween).
    ex_and H4 y.
    exists y;eBetween.
Qed.

(** The prove the former version of lower dimension axiom for compatibility. *)

Lemma lower_dim_ex : exists A B C,
  ~ (Bet A B C \/ Bet B C A \/ Bet C A B).
Proof.
exists PA.
exists PB.
exists PC.
apply lower_dim.
Qed.

Lemma two_distinct_points : exists X, exists Y: Tpoint, X <> Y.
Proof.
    assert (ld:=lower_dim_ex).
    ex_elim ld A.
    ex_elim H B.
    ex_elim H0 C.
    exists A; exists B.
    intro; subst; apply H.
    right; right; apply between_trivial.
Qed.

Lemma point_construction_different : forall A B, exists C, Bet A B C /\ B <> C.
Proof.
    intros.
    assert (tdp := two_distinct_points).
    ex_elim tdp x.
    ex_elim H y.
    prolong A B F x y.
    exists F.
    show_distinct B F.
      intuition.
    intuition.
Qed.

Lemma another_point : forall A: Tpoint, exists B, A<>B.
Proof.
    intros.
    assert (pcd := point_construction_different A A).
    ex_and pcd B.
    exists B;assumption.
Qed.

End T2_4.

Section Beeson_1.

(** Another proof of l2_11 without eq_dec_points but using Cong stability
inspired by Micheal Beeson. #<a href="http://www.michaelbeeson.com/research/papers/AxiomatizingConstructiveGeometry.pdf"></a> # *)

Context `{Tn:Tarski_neutral_dimensionless}.

Variable Cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.

Lemma l2_11_b : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    apply Cong_stability; intro.
    assert (A<>B).
      intro; subst.
      assert (A'=B') by (apply (cong_identity A' B' B); Cong).
      subst; tauto.
    assert (Cong C A C' A') by (apply (five_segment _ _ _ _ _ _ _ _ H1 );auto using cong_trivial_identity, cong_commutativity).
    apply H3; Cong.
Qed.

Lemma cong_dec_eq_dec_b :
 (forall A B:Tpoint, ~ A <> B -> A = B).
Proof.
    intros A B HAB.
    apply cong_identity with A.
    apply Cong_stability.
    intro HNCong.
    apply HAB.
    intro HEq.
    subst.
    apply HNCong.
    apply cong_pseudo_reflexivity.
Qed.

End Beeson_1.

Section Beeson_2.

Context `{Tn:Tarski_neutral_dimensionless}.

Variable Bet_stability : forall A B C, ~ ~ Bet A B C -> Bet A B C.

Lemma bet_dec_eq_dec_b :
 (forall A B:Tpoint, ~ A <> B -> A = B).
Proof.
    intros A B HAB.
    apply between_identity.
    apply Bet_stability.
    intro HNBet.
    apply HAB.
    intro HEq.
    subst.
    apply HNBet.
    apply between_trivial.
Qed.

Lemma BetSEq : forall A B C, BetS A B C <-> Bet A B C /\ A <> B /\ A <> C /\ B <> C.
Proof.
intros; unfold BetS; split; intro; spliter;
repeat split; auto; intro; treat_equalities; auto.
Qed.

End Beeson_2.