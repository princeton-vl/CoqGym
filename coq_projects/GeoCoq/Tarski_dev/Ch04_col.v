Require Export GeoCoq.Tarski_dev.Ch04_cong_bet.

Section T4_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma col_permutation_1 : forall A B C,Col A B C -> Col B C A.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma col_permutation_2 : forall A B C, Col A B C -> Col C A B.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma col_permutation_3 : forall A B C, Col A B C -> Col C B A.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma col_permutation_4 : forall A B C, Col A B C -> Col B A C.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

Lemma col_permutation_5 : forall A B C, Col A B C -> Col A C B.
Proof.
    unfold Col.
    intros.
    intuition.
Qed.

End T4_1.

Hint Resolve bet_col col_permutation_1 col_permutation_2
col_permutation_3 col_permutation_4 col_permutation_5 : col.

Ltac Col := auto 3 with col.
Ltac Col5 := auto with col.

Section T4_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma not_col_permutation_1 :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col B C A.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma not_col_permutation_2 :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col C A B.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma not_col_permutation_3 :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col C B A.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma not_col_permutation_4 :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col B A C.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

Lemma not_col_permutation_5 :
 forall (A B C : Tpoint), ~ Col A B C -> ~ Col A C B.
Proof.
    intros.
    intro.
    apply H.
    Col.
Qed.

End T4_2.

Hint Resolve not_col_permutation_1 not_col_permutation_2
not_col_permutation_3 not_col_permutation_4 not_col_permutation_5 : col.

Section T4_3.

Context `{Tn:Tarski_neutral_dimensionless}.

(** This lemma is used by tactics for trying several permutations. *)
Lemma Col_cases :
 forall A B C,
 Col A B C \/ Col A C B \/ Col B A C \/
 Col B C A \/ Col C A B \/ Col C B A ->
 Col A B C.
Proof.
    intros.
    decompose [or] H; Col.
Qed.

Lemma Col_perm :
 forall A B C,
 Col A B C ->
 Col A B C /\ Col A C B /\ Col B A C /\
 Col B C A /\ Col C A B /\ Col C B A.
Proof.
    intros.
    repeat split; Col.
Qed.

Lemma col_trivial_1 : forall A B, Col A A B.
Proof.
    unfold Col.
    intros.
    Between.
Qed.

Lemma col_trivial_2 : forall A B, Col A B B.
Proof.
    unfold Col.
    intros.
    Between.
Qed.

Lemma col_trivial_3 : forall A B, Col A B A.
Proof.
    unfold Col.
    intros.
    right;Between.
Qed.

End T4_3.

Hint Immediate col_trivial_1 col_trivial_2 col_trivial_3: col.

Section T4_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l4_13 : forall A B C A' B' C',
 Col A B C -> Cong_3 A B C A' B' C' -> Col A' B' C'.
Proof.
    unfold Col.
    intros.
    decompose [or] H;
      eauto 6  using l4_6 with cong3.
Qed.

Lemma l4_14 : forall A B C A' B',
  Col A B C -> Cong A B A' B' -> exists C', Cong_3 A B C A' B' C'.
Proof.
    unfold Col.
    intros.
    intuition.
      prolong A' B' C' B C.
      exists C'.
      assert (Cong A C A' C') by (eapply l2_11;eCong).
      unfold Cong_3;intuition.
      assert (exists C', Bet A' C' B' /\ Cong_3 A C B A' C' B') by (eapply l4_5;Between).
      ex_and H1 C'.
      exists C'.
      auto with cong3.
    prolong B' A' C' A C.
    exists C'.
    assert (Cong B C B' C') by (eapply l2_11;eBetween;Cong).
    unfold Cong_3;intuition.
Qed.

Lemma l4_16 : forall A B C D A' B' C' D',
   FSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    unfold FSC.
    unfold Col.
    intros.
    decompose [or and] H; clear H.
      assert (Bet A' B' C') by (eapply l4_6;eauto).
      unfold Cong_3 in *; spliter.
      assert(OFSC A B C D A' B' C' D') by (unfold OFSC;repeat split; assumption).
      eapply five_segment_with_def; eauto.
      assert(Bet B' C' A') by (apply (l4_6 B C A B' C' A'); Cong;auto with cong3).
      apply (l4_2 B C A D B' C' A' D').
      unfold IFSC; unfold Cong_3 in *; spliter; repeat split;Between;Cong.
    assert (Bet C' A' B') by (eapply (l4_6 C A B C' A' B'); auto with cong3).
    eapply (five_segment_with_def B A C D B' A'); unfold OFSC; unfold Cong_3 in *; spliter; repeat split; Between; Cong.
Qed.

Lemma l4_17 : forall A B C P Q,
  A<>B -> Col A B C -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q.
Proof.
    intros.
    assert (FSC A B C P A B C Q) by (unfold FSC; unfold Cong_3;repeat split; Cong).
    eapply l4_16; eauto.
Qed.

Lemma l4_18 : forall A B C C',
  A<>B -> Col A B C -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof.
    intros.
    apply cong_identity with C.
    apply (l4_17 A B); Cong.
Qed.

Lemma l4_19 : forall A B C C',
 Bet A C B -> Cong A C A C' -> Cong B C B C' -> C=C'.
Proof.
    intros.
    induction (eq_dec_points A B).
      treat_equalities; reflexivity.
    apply (l4_18 A B); Cong.
    auto using bet_col with col.
Qed.

Lemma not_col_distincts : forall A B C ,
 ~ Col A B C ->
 ~ Col A B C /\ A <> B /\ B <> C /\ A <> C.
Proof.
    intros.
    repeat split;(auto;intro); subst; apply H; Col.
Qed.

Lemma NCol_cases :
 forall A B C,
 ~ Col A B C \/ ~ Col A C B \/ ~ Col B A C \/
 ~ Col B C A \/ ~ Col C A B \/ ~ Col C B A ->
 ~ Col A B C.
Proof.
    intros.
    decompose [or] H; Col.
Qed.

Lemma NCol_perm :
 forall A B C,
 ~ Col A B C ->
 ~ Col A B C /\ ~ Col A C B /\ ~ Col B A C /\
 ~ Col B C A /\ ~ Col C A B /\ ~ Col C B A.
Proof.
    intros.
    repeat split; Col.
Qed.

Lemma col_cong_3_cong_3_eq : forall A B C A' B' C1 C2,
  A <>B -> Col A B C -> Cong_3 A B C A' B' C1 -> Cong_3 A B C A' B' C2 -> C1 = C2.
Proof.
intros A B C A' B' C1 C2 HAB HCol HCong1 HCong2.
apply l4_18 with A' B'; try apply l4_13 with A B C; Col;
unfold Cong_3 in *; spliter.
  intro; treat_equalities; intuition.
  apply cong_transitivity with A C; Cong.
  apply cong_transitivity with B C; Cong.
Qed.

End T4_4.
