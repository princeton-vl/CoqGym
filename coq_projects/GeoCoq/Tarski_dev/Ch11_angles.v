Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

Ltac permut :=
match goal with
   |H : (Col ?X ?Y ?Z) |- Col ?X ?Y ?Z => assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Y ?Z ?X => apply col_permutation_1; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Z ?X ?Y => apply col_permutation_2; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?X ?Z ?Y => apply col_permutation_5; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Y ?X ?Z => apply col_permutation_4; assumption
   |H : (Col ?X ?Y ?Z) |- Col ?Z ?Y ?X => apply col_permutation_3; assumption
   |_ : _ |- _ => idtac
end.

Ltac bet :=
match goal with
   |H0 : Bet ?A ?B ?C |- Bet ?A ?B ?C => assumption
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?A ?B ?D => apply (outer_transitivity_between _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?A ?C ?D => apply (outer_transitivity_between2 _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?A ?B ?C => apply (between_inner_transitivity _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?B ?C ?D => apply (between_exchange3 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?A ?C ?D => apply (between_exchange2 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?A ?B ?D => apply (between_exchange4 _ _ _ _ H0 H1)

   |H0 : Bet ?A ?B ?C |- Bet ?A ?B ?C => assumption
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?D ?B ?A => apply between_symmetry; apply (outer_transitivity_between _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?B ?C ?D , H : ?B <> ?C |- Bet ?D ?C ?A => apply (outer_transitivity_between2 _ _ _ _ H0 H1 H)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?C ?B ?A => apply between_symmetry; apply (between_inner_transitivity _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?D ?C ?B => apply between_symmetry; apply (between_exchange3 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?D, H1 : Bet ?B ?C ?D  |- Bet ?D ?C ?A => apply between_symmetry; apply (between_exchange2 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C, H1 : Bet ?A ?C ?D  |- Bet ?D ?B ?A => apply between_symmetry; apply (between_exchange4 _ _ _ _ H0 H1)
   |H0 : Bet ?A ?B ?C |- Bet ?C ?B ?A => apply (between_symmetry _ _ _  H0)

   |H0 : Bet ?A ?B ?C |- Bet ?C ?B ?A => apply (between_symmetry _ _ _  H0)
   |_ : _ |- Bet ?A ?B ?B => apply between_trivial
   |_ : _ |- Bet ?A ?A ?B => apply between_trivial2
   |_ : _ |- _ => idtac
end.

Ltac cong :=
match goal with
   |_ :  Cong ?A ?B ?C ?BD |- Cong ?A ?B ?C ?D => assumption
   |_ : _ |- Cong ?A ?B ?A ?B => apply cong_reflexivity
   |_ : _ |- Cong ?A ?A ?B ?B => apply cong_trivial_identity

   |H0 : Cong ?A ?B ?C ?D |- Cong ?A ?B ?C ?C => assumption
   |H0 : Cong ?A ?B ?C ?D |- Cong ?A ?B ?D ?C => apply (cong_right_commutativity _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?B ?A ?D ?C => apply (cong_commutativity _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?B ?A ?C ?D => apply (cong_left_commutativity _ _ _ _ H0)

   |H0 : Cong ?A ?B ?C ?D |- Cong ?C ?D ?A ?B => apply (cong_symmetry _ _ _ _ H0)
   |H0 : Cong ?A ?B ?C ?D |- Cong ?C ?D ?B ?A => apply (cong_symmetry _ _ _ _ (cong_left_commutativity _ _ _ _ H0))
   |H0 : Cong ?A ?B ?C ?D |- Cong ?D ?C ?B ?B => apply (cong_symmetry _ _ _ _ (cong_commutativity _ _ _ _ H0))
   |H0 : Cong ?A ?B ?C ?D |- Cong ?D ?C ?A ?B => apply (cong_symmetry _ _ _ _ (cong_right_commutativity _ _ _ _ H0))
   |_ : _ |- _ => idtac
end.

Section T11_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l11_3 : forall A B C D E F,
 CongA A B C D E F ->
 exists A', exists C', exists D', exists F',
 Out B A' A /\ Out B C C' /\ Out E D' D /\ Out E F F' /\
 Cong_3 A' B C' D' E F'.
Proof.
    intros.
    unfold CongA in H.
    spliter.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    assert_diffs.
    repeat split;finish.
      apply cong_left_commutativity.
      eapply l2_11 with A D;finish.
    apply cong_left_commutativity.
    eapply l2_11; eBetween; Cong.
Qed.

Lemma l11_aux : forall B A A' A0 E D D' D0,
      Out B A A' -> Out E D D' -> Cong B A' E D' ->
      Bet B A A0 -> Bet E D D0 -> Cong A A0 E D ->
      Cong D D0 B A ->
      Cong B A0 E D0 /\ Cong A' A0 D' D0.
Proof.
    intros.
    assert (A <> B).
      unfold Out in H.
      spliter.
      assumption.
    assert(Cong B A0 E D0).
      apply cong_right_commutativity.
      apply l2_11 with A D;finish.
    split.
      apply H7.
    unfold Out in *.
    spliter.
    induction H9; induction H11.
      assert(Bet B A' A0 \/ Bet B A0 A').
        eauto using l5_1.

      induction H12.
        assert(Bet E D' D0).
          eapply cong_preserves_bet.
            2: apply H1.
            apply H12.
            assumption.
          unfold Out.
          repeat split.
            assumption.
            assert_diffs.
            auto.
          eapply l5_1.
            2:apply H9.
            auto.
          assumption.
        apply cong_commutativity.
        eapply l4_3  with B E;finish.
      assert(Bet E D0 D').
        eapply cong_preserves_bet.
          2: apply H7.
          apply H12.
          assumption.
        unfold Out.
        repeat split.
          assert_diffs;auto.
          assert_diffs;auto.
        eapply l5_1.
          2:apply H3.
          auto.
        assumption.
      eapply l4_3 with B E;finish.
      apply cong_commutativity.
      eapply l4_3.
        3:apply cong_commutativity.
        3:apply H7.
        apply between_symmetry.
        eapply between_exchange4.
          apply H11.
        assumption.
        apply between_symmetry.
        eapply cong_preserves_bet.
          2: apply H1.
          2: apply H7.
          eapply between_exchange4.
            apply H11.
          assumption.
        unfold Out.
        repeat split.
          assumption.
          assert_diffs;auto.
        eapply l5_1.
          2:apply H9.
          auto.
        assumption.
      finish.
      apply cong_commutativity.
      eapply l4_3.
        3:apply cong_commutativity.
        3:apply H7.
        apply between_symmetry.
        eapply cong_preserves_bet.
          2:apply cong_symmetry.
          2:apply H1.
          2:apply cong_symmetry.
          2:apply H7.
          eapply between_exchange4.
            apply H9.
          assumption.
        unfold Out.
        repeat split.
          assumption.
          assert_diffs;auto.
        eauto using l5_1.
        apply between_symmetry.
        eapply between_exchange4.
          apply H9.
        assumption.
      finish.
    apply cong_commutativity.
    eapply l4_3.
      3:apply cong_commutativity.
      3:apply H7.
      apply between_symmetry.
      eapply between_exchange4.
        apply H11.
      assumption.
      apply between_symmetry.
      eapply between_exchange4.
        apply H9.
      assumption.
    finish.
Qed.

Lemma l11_3_bis : forall A B C D E F,
 (exists A', exists C', exists D', exists F',
 Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
 Cong_3 A' B C' D' E F') -> CongA A B C D E F.
Proof.
    intros.
    unfold CongA.
    ex_and H A'.
    ex_and H0 C'.
    ex_and H D'.
    ex_and H0 F'.
    prolong B A A0 E D.
    prolong B C C0 E F.
    prolong E D D0 B A.
    prolong E F F0 B C.
    assert(HH0:=H0).
    assert(HH1:=H1).
    assert(HH2:=H2).
    assert(HH:=H).
    unfold Out in HH.
    unfold Out in HH0.
    unfold Out in HH1.
    unfold Out in HH2.
    spliter.
    repeat split;try assumption.
    repeat split;try assumption.
    exists A0.
    exists C0.
    exists D0.
    exists F0.
    repeat split; try (assumption).
    unfold Cong_3 in H3.
    spliter.
    assert(Cong B A0 E D0 /\ Cong A' A0 D' D0).
      eapply l11_aux with A D;finish.
    assert(Cong B C0 E F0 /\ Cong C' C0 F' F0).
      eapply l11_aux with C F;finish.
    spliter.
    assert (Cong_3 B A' A0 E D' D0)
      by (repeat split;finish).
    assert (Cong_3 B C' C0 E F' F0)
      by (repeat split;finish).
    assert (Cong C0 A' F0 D').
      apply l4_16 with B C' E F';
        unfold FSC;repeat split;finish;ColR.
    apply l4_16 with B A' E D';
    unfold FSC;repeat split;finish;ColR.
Qed.

Lemma l11_4_1 : forall A B C D E F,
  CongA A B C D E F -> A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F').
Proof.
    intros.
    assert (HH:=H).
    apply l11_3 in HH.
    unfold CongA in H.
    spliter.
    repeat split; try assumption.
    clear H3.
    intros.
    ex_and HH A0.
    ex_and H4 C0.
    ex_and H10 D0.
    ex_and H4 F0.
    unfold Cong_3 in H13.
    spliter.
    assert (Out B A' A0).
      eapply l6_7.
        apply H3.
      apply l6_6.
      assumption.
    assert (Out E D' D0).
      eapply l6_7.
        apply H6.
      apply l6_6.
      assumption.
    assert(Cong A' A0 D' D0).
      eapply out_cong_cong.
        apply H16.
        apply H17.
        assumption.
      Cong.
    assert (Cong A' C0 D' F0).
      eapply (l4_16 B A0 A' C0 E D0 D' F0).
        unfold FSC.
        repeat split.
          assert_cols;Col.
          Cong.
          assumption.
          Cong.
          assumption.
        assumption.
      intro.
      subst A0.
      unfold Out in H4.
      spliter.
      absurde.
    assert (Out B C' C0).
      eapply l6_7.
        apply H5.
      assumption.
    assert (Out E F' F0).
      eapply l6_7.
        apply H7.
      assumption.
    assert(Cong C' C0 F' F0).
      eapply out_cong_cong.
        3:apply H9.
        assumption.
        assumption.
      assumption.
    apply cong_commutativity.
    eapply (l4_16 B C0 C' A' E F0 F' D').
      unfold FSC.
      repeat split.
        apply out_col.
        apply l6_6.
        assumption.
        assumption.
        assumption.
        Cong.
        assumption.
      Cong.
    intro.
    subst C0.
    unfold Out in H10.
    spliter.
    absurde.
Qed.



Lemma l11_4_2 : forall A B C D E F,
  (A<>B /\ C<>B /\ D<>E /\ F<>E /\
  (forall A' C' D' F', Out B A' A /\ Out B C' C /\ Out E D' D /\ Out E F' F /\
  Cong B A' E D' /\ Cong B C' E F' -> Cong A' C' D' F')) ->  CongA A B C D E F.
Proof.
    intros.
    spliter.
    apply l11_3_bis.
    prolong B A A' E D.
    prolong B C C' E F.
    prolong E D D' B A.
    prolong E F F' B C.
    exists A'.
    exists C'.
    exists D'.
    exists F'.
    assert(Cong A' B D' E).
     {
      apply cong_right_commutativity.
      eapply l2_11 with A D;finish.
     }
    assert (Cong B C' E F').
      apply cong_right_commutativity.
      eapply l2_11 with C F;finish.
    assert_diffs;repeat split;finish.
    apply H3;repeat split;finish.
Qed.

Lemma conga_refl : forall A B C, A <> B -> C <> B -> CongA A B C A B C.
Proof.
    intros.
    apply l11_3_bis.
    exists A.
    exists C.
    exists A.
    exists C.
    repeat split; finish.
Qed.

Lemma conga_sym : forall A B C A' B' C', CongA A B C A' B' C' -> CongA A' B' C' A B C.
Proof.
    unfold CongA.
    intros.
    spliter.
    ex_and H3 A0.
    ex_and H4 C0.
    ex_and H3 D0.
    ex_and H4 F0.
    repeat split; try assumption.
    exists D0.
    exists F0.
    exists A0.
    exists C0.
    repeat split; finish.
Qed.

Lemma out_conga :
 forall A B C A' B' C' A0 C0 A1 C1,
 CongA A B C A' B' C' ->
 Out B A A0 ->
 Out B C C0 ->
 Out B' A' A1 ->
 Out B' C' C1 ->
 CongA A0 B C0 A1 B' C1.
Proof.
    intros.
    apply l11_4_1 in H.
    spliter.
    apply l11_4_2.
    assert_diffs.
    repeat split;try assumption.
    intros.
    spliter.
    apply H7.
    assert_diffs.
    repeat split;finish.
      eapply l6_7 with A0;finish.
      eapply l6_7 with C0;finish.
      eapply l6_7 with A1;finish.
      eapply l6_7 with C1;finish.
Qed.

Lemma cong3_diff : forall A B C A' B' C',
 A<>B -> Cong_3 A B C A' B' C' -> A' <> B'.
Proof.
unfold Cong_3 in *.
intros.
spliter.
assert_diffs.
auto.
Qed.

Lemma cong3_diff2: forall A B C A' B' C',
 B<>C -> Cong_3 A B C A' B' C' -> B' <> C'.
Proof.
unfold Cong_3 in *.
intros.
spliter.
assert_diffs.
auto.
Qed.

Lemma cong3_conga : forall A B C A' B' C',
 A <> B -> C <> B ->
 Cong_3 A B C A' B' C' ->
 CongA A B C A' B' C'.
Proof.
    intros.
    assert (A' <> B') by (eauto using cong3_diff).
    assert (B' <> C') by (eauto using cong3_diff2).
    apply (l11_3_bis A B C A' B' C').
    exists A. exists C. exists A'. exists C'.
    intuition finish.
Qed.

Lemma cong3_conga2 : forall A B C A' B' C' A'' B'' C'',
  Cong_3 A B C A' B' C' ->
  CongA A B C A'' B'' C'' ->
  CongA A' B' C' A'' B'' C''.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A2.
    ex_and H5 C2.
    unfold Cong_3 in H.
    spliter.
    unfold CongA.
    assert_diffs.
    repeat split;try solve [auto].
    prolong B' A' A1 B'' A''.
    prolong B' C' C1 B'' C''.
    exists A1.
    exists C1.
    exists A2.
    exists C2.
    repeat split;try assumption.
      eapply cong_transitivity with B A;finish.
      eapply cong_transitivity with B C;finish.
    assert (Cong A A0 A' A1).
      eapply cong_transitivity with B'' A'';finish.
    assert(Cong B A0 B' A1).
      eapply l2_11 with A A';finish.
    assert (Cong C C0 C' C1).
      eapply cong_transitivity with B'' C'';finish.
    assert(Cong B C0 B' C1).
      eapply l2_11 with C C';finish.
    assert(FSC B A A0 C B' A' A1 C').
      unfold FSC;assert_cols;repeat split;finish.
    assert(Cong A0 C A1 C').
      eauto using l4_16.
    apply cong_commutativity.
    assert(Cong C0 A0 C1 A1).
      eapply (l4_16 B C C0 A0 B' C' C1 A1).
        unfold FSC;assert_cols;repeat split;finish.
      auto.
    apply cong_transitivity with A0 C0; Cong.
Qed.

Lemma conga_diff1 : forall A B C A' B' C', CongA A B C A' B' C' -> A <> B.
Proof.
    intros.
    unfold CongA in H.
    spliter.
    assumption.
Qed.

Lemma conga_diff2 : forall A B C A' B' C', CongA A B C A' B' C' -> C <> B.
Proof.
    intros.
    unfold CongA in H.
    spliter.
    assumption.
Qed.

Lemma conga_diff45 : forall A B C A' B' C', CongA A B C A' B' C' -> A' <> B'.
Proof.
  intros A B C A' B' C' H.
  apply (conga_diff1 A' B' C' A B C); apply conga_sym; auto.
Qed.

Lemma conga_diff56 : forall A B C A' B' C', CongA A B C A' B' C' -> C' <> B'.
Proof.
  intros A B C A' B' C' H.
  apply (conga_diff2 A' B' C' A B C); apply conga_sym; auto.
Qed.

Lemma conga_trans : forall A B C A' B' C' A'' B'' C'',
  CongA A B C A' B' C' -> CongA A' B' C' A'' B'' C'' ->
  CongA A B C A'' B'' C''.
Proof.
    intros.
    assert (HH:=H).
    unfold CongA in H.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert_diffs.
    assert(A'' <> B'' /\ C'' <> B'').
      unfold CongA in H0.
      spliter.
      split; assumption.
    spliter.
    assert(CongA A1 B' C1 A'' B'' C'')
      by (apply out_conga with A' C' A'' C'';finish).
    assert (CongA A0 B C0 A' B' C')
      by (apply out_conga with A C A' C';finish).
    assert (Cong B A0 B' A1).
      {
      apply cong_right_commutativity.
      apply l2_11 with A A';finish.
      }
    assert (Cong B C0 B' C1).
      {
      apply cong_right_commutativity.
      eapply l2_11 with C C';finish.
      }
    assert (Cong A0 C0 A1 C1).
    {
      apply (l11_4_1) in H24.
      spliter.
      apply H30.
      repeat split;finish.
    }
    assert (Cong_3 A0 B C0 A1 B' C1)
      by (repeat split;finish).
    apply cong3_symmetry in H28.
    assert( CongA A0 B C0 A'' B'' C'')
      by (eauto using cong3_conga2).
    eapply out_conga with A0 C0 A'' C'';finish.
Qed.

Lemma conga_pseudo_refl : forall A B C,
 A <> B -> C <> B -> CongA A B C C B A.
Proof.
    intros.
    unfold CongA.
    repeat split; try assumption.
    prolong B A A' B C.
    prolong B C C' B A.
    prolong B A A'' B C.
    prolong B C C'' B A.
    exists A'.
    exists C'.
    exists C''.
    exists A''.
    repeat split; try assumption.
    assert (A' = A'') by (eauto using (construction_uniqueness B A)).
    subst A''.
    assert (C' = C'') by (eauto using (construction_uniqueness B C)).
    subst C''.
    Cong.
Qed.

Lemma conga_trivial_1 : forall A B C D,
  A<>B -> C<>D -> CongA A B A C D C.
Proof.
    intros.
    unfold CongA.
    repeat split; try assumption.
    prolong B A A' D C.
    prolong D C C' B A.
    exists A'.
    exists A'.
    exists C'.
    exists C'.
    repeat split;finish.
Qed.

Lemma l11_10 : forall A B C D E F A' C' D' F',
  CongA A B C D E F -> Out B A' A -> Out B C' C -> Out E D' D -> Out E F' F ->
  CongA A' B C' D' E F'.
Proof.
    intros.
    apply (out_conga A B C D E F); auto using l6_6.
Qed.

Lemma out2__conga : forall A B C A' C', Out B A' A -> Out B C' C -> CongA A B C A' B C'.
Proof.
  intros A B C A' C' HAOut HCOut.
  assert_diffs.
  apply l11_10 with A C A C;finish.
  apply conga_refl;auto.
Qed.

Lemma l11_13 : forall A B C D E F A' D',
 CongA A B C D E F -> Bet A B A' -> A'<> B -> Bet D E D' -> D'<> E -> CongA A' B C D' E F.
Proof.
    intros.
    unfold CongA in H.
    spliter.
    ex_and H7 A''.
    ex_and H8 C''.
    ex_and H7 D''.
    ex_and H8 F''.
    prolong B A' A0 E D'.
    prolong E D' D0 B A'.
    unfold CongA.
    repeat split; try assumption.
    exists A0.
    exists C''.
    exists D0.
    exists F''.
    repeat split; try assumption.
    apply (five_segment_with_def A'' B A0 C'' D'' E D0 F'').
      unfold OFSC.
      repeat split.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H7.
          eapply outer_transitivity_between.
            apply H0.
            assumption.
          auto.
        assumption.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H11.
          eapply outer_transitivity_between.
            apply H2.
            assumption.
          auto.
        assumption.
        apply cong_left_commutativity.
        eapply l2_11.
          apply H7.
          apply between_symmetry.
          apply H11.
          Cong.
        Cong.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H16.
          apply between_symmetry.
          apply H18.
          apply cong_symmetry.
          Cong.
        Cong.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11 with C F;finish.
    assert_diffs;auto.
Qed.

Lemma conga_right_comm : forall A B C D E F, CongA A B C D E F -> CongA A B C F E D.
Proof.
    intros.
    apply conga_trans with D E F.
    apply H.
    unfold CongA in H.
    spliter.
    apply conga_pseudo_refl;auto.
Qed.

Lemma conga_left_comm : forall A B C D E F, CongA A B C D E F -> CongA C B A D E F.
Proof.
    intros.
    apply conga_sym.
    apply conga_trans with A B C.
      apply conga_sym.
      apply H.
    unfold CongA in H.
    spliter.
    apply conga_pseudo_refl.
      assumption.
    assumption.
Qed.

Lemma conga_comm : forall A B C D E F, CongA A B C D E F -> CongA C B A F E D.
Proof.
    intros.
    apply conga_left_comm.
    apply conga_right_comm.
    assumption.
Qed.

Lemma conga_line : forall A B C A' B' C',
 A <> B -> B <> C -> A' <> B' -> B' <> C' -> Bet A B C -> Bet A' B' C' ->
 CongA A B C A' B' C'.
Proof.
    intros.
    assert_diffs.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold CongA.
    repeat split; try assumption.
      auto.
      auto.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    apply (l2_11 A0 B C0 A1 B' C1).
      eapply outer_transitivity_between2.
        apply between_symmetry.
        apply H11.
        eapply outer_transitivity_between.
          apply H3.
          assumption.
        assumption.
      assumption.
      eapply outer_transitivity_between2.
        apply between_symmetry.
        apply H13.
        eapply outer_transitivity_between.
          apply H4.
          assumption.
        assumption.
      assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply between_symmetry.
        apply H11.
        apply H13.
        apply cong_left_commutativity.
        assumption.
      apply cong_symmetry.
      apply cong_right_commutativity.
      assumption.
    apply cong_right_commutativity.
    eapply l2_11.
      apply H7.
      apply between_symmetry.
      apply H9.
      apply cong_symmetry.
      apply cong_left_commutativity.
      assumption.
    apply cong_right_commutativity.
    assumption.
Qed.


Lemma l11_14 : forall A B C A' C',
 Bet A B A' -> A <> B -> A' <> B -> Bet C B C' -> B <> C -> B <> C' ->
 CongA A B C A' B C'.
Proof.
    intros.
    assert_diffs.
    assert (CongA A' B C  C' B A).
    {
      apply l11_13 with A C;finish.
      apply conga_pseudo_refl;finish.
    }
      apply l11_13 with A' A;finish.
      apply conga_right_comm.
      auto.
Qed.

End T11_1.

Section T11_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l11_16 : forall A B C A' B' C',
 Per A B C    -> A <> B  -> C <> B ->
 Per A' B' C' -> A'<> B' -> C'<> B'->
 CongA A B C A' B' C'.
Proof.
    intros.
    prolong B C C0 B' C'.
    prolong B' C' C1 B C.
    prolong B A A0 B' A'.
    prolong B' A' A1 B A.
    unfold CongA.
    repeat split; try assumption.
    exists A0.
    exists C0.
    exists A1.
    exists C1.
    repeat split; try assumption.
    apply (l10_12 A0 B C0 A1 B' C1).
      eapply (per_col _ _ C).
        intro;subst.
        auto.
        apply l8_2.
        eapply (per_col _ _ A).
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      eapply (per_col _ _ C').
        auto.
        apply l8_2.
        eapply (per_col _ _ A').
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply between_symmetry.
        apply H9.
        apply H11.
        apply cong_left_commutativity.
        assumption.
      apply cong_symmetry.
      apply cong_right_commutativity.
      assumption.
    apply cong_right_commutativity.
    eapply l2_11.
      apply H5.
      apply between_symmetry.
      apply H7.
      apply cong_symmetry.
      apply cong_left_commutativity.
      assumption.
    apply cong_right_commutativity.
    assumption.
Qed.


Lemma l11_17 : forall A B C A' B' C',
  Per A B C -> CongA A B C A' B' C' -> Per A' B' C'.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (Per A0 B C0).
      eapply (per_col _ _ C).
        auto.
        apply l8_2.
        eapply (per_col _ _ A).
          auto.
          apply l8_2.
          assumption.
        unfold Col.
        left.
        assumption.
      unfold Col.
      left.
      assumption.
    assert(Per A1 B' C1).
      eapply l8_10.
        apply H13.
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply between_symmetry.
          apply H4.
          apply H8.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_left_commutativity.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    eapply (per_col _ _ C1).
      intro.
      subst C1.
      apply between_identity in H10.
      subst C'.
      absurde.
      apply l8_2.
      eapply (per_col _ _ A1).
        intro.
        subst A1.
        apply between_identity in H8.
        subst A'.
        absurde.
        apply l8_2.
        assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
    unfold Col.
    right; left.
    apply between_symmetry.
    assumption.
Qed.

Lemma l11_18_1 : forall A B C D,
  Bet C B D -> B <> C -> B <> D -> A <> B -> Per A B C -> CongA A B C A B D.
Proof.
    intros.
    spliter.
    assert (Per A B D).
      eapply per_col.
        apply H0.
        assumption.
      unfold Col.
      right; right.
      apply between_symmetry.
      assumption.
    eapply l11_16; try assumption.
      auto.
    auto.
Qed.

Lemma l11_18_2 : forall A B C D,
  Bet C B D -> CongA A B C A B D -> Per A B C.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 D0.
    assert( A0 = A1).
      eapply construction_uniqueness.
        2: apply H4.
        auto.
        apply H5.
        assumption.
      assumption.
    subst A1.
    assert(Per A0 B C0).
      unfold Per.
      exists D0.
      repeat split.
        eapply outer_transitivity_between2.
          apply between_symmetry.
          apply H6.
          eapply outer_transitivity_between.
            apply H.
            assumption.
          auto.
        assumption.
        eapply l2_11.
          apply between_symmetry.
          apply H6.
          apply H10.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
      assumption.
    eapply (per_col _ _ C0).
      intro.
      subst C0.
      apply between_identity in H6.
      subst C.
      absurde.
      apply l8_2.
      eapply (per_col _ _ A0).
        intro.
        subst A0.
        apply between_identity in H8.
        subst A.
        absurde.
        apply l8_2.
        assumption.
      unfold Col.
      right; left.
      apply between_symmetry.
      assumption.
    unfold Col.
    right; left.
    apply between_symmetry.
    assumption.
Qed.

Lemma cong3_preserves_out : forall A B C A' B' C',
  Out A B C -> Cong_3 A B C A' B' C' -> Out A' B' C'.
Proof.
    intros.
    unfold Out in *.
    spliter.
    assert(HH:=H0).
    unfold Cong_3 in H0.
    spliter.
    repeat split.
      intro.
      subst A'.
      apply cong_identity in H0.
      subst A.
      absurde.
      intro.
      subst A'.
      apply cong_identity in H3.
      subst A.
      absurde.
    induction H2.
      left.
      eapply l4_6.
        2:apply HH.
      assumption.
    right.
    eapply l4_6.
      apply H2.
    unfold Cong_3.
    repeat split.
      assumption.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.

Lemma l11_21_a : forall A B C A' B' C', Out B A C -> CongA A B C A' B' C' -> Out B' A' C'.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (Out B A0 C0).
      unfold Out.
      repeat split.
        intro.
        subst A0.
        apply between_identity in H4.
        subst A.
        absurde.
        intro.
        subst C0.
        apply between_identity in H6.
        subst C.
        absurde.
      unfold Out in H.
      spliter.
      induction H14.
        eapply l5_1.
          2: apply H4.
          auto.
        eapply between_exchange4.
          apply H14.
        assumption.
      eapply l5_1.
        3: apply H6.
        auto.
      eapply between_exchange4.
        apply H14.
      assumption.
    assert (Out B' A1 C1).
      eapply cong3_preserves_out.
        apply H13.
      unfold Cong_3.
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H4.
          apply between_symmetry.
          apply H8.
          apply cong_symmetry.
          apply cong_left_commutativity.
          assumption.
        apply cong_right_commutativity.
        assumption; apply H8.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H6.
          apply between_symmetry.
          apply H10.
          apply cong_symmetry.
          apply cong_left_commutativity.
          assumption.
        apply cong_right_commutativity.
        assumption.
      assumption.
    eapply l6_7.
      apply l6_6.
      eapply l6_7.
        apply H14.
      eapply l6_7.
        apply l6_6.
        apply H14.
      unfold Out.
      repeat split.
        intro.
        subst A1.
        unfold Out in H14.
        spliter.
        absurde.
        assumption.
      right.
      assumption.
    eapply l6_7.
      apply H14.
    unfold Out.
    repeat split.
      intro.
      subst C1.
      unfold Out in H14.
      spliter.
      absurde.
      assumption.
    right.
    assumption.
Qed.

Lemma l11_21_b : forall A B C A' B' C',
 Out B A C -> Out B' A' C' -> CongA A B C A' B' C'.
Proof.
    intros.
    prolong A B A0 A B.
    prolong C B C0 B C.
    prolong A' B' A1 A' B'.
    prolong C' B' C1 B' C'.
    eapply l11_13.
      eapply conga_line.
        5: apply between_symmetry.
        5: apply H3.
        5: apply between_symmetry.
        5: apply H7.
        intro.
        subst C0.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst C.
        unfold Out in H.
        spliter.
        absurde.
        intro.
        subst C.
        unfold Out in H.
        spliter.
        absurde.
        intro.
        subst C1.
        apply cong_symmetry in H8.
        apply cong_identity in H8.
        subst C'.
        unfold Out in H0.
        spliter.
        absurde.
        intro.
        subst C'.
        unfold Out in H0.
        spliter.
        absurde.
      unfold Out in H0.
      spliter.
      auto.
      unfold Out in H.
      spliter.
      induction H12.
        eapply between_inner_transitivity.
          apply between_symmetry.
          apply H3.
        assumption.
      eapply outer_transitivity_between.
        apply between_symmetry.
        apply H3.
        assumption.
      auto.
      unfold Out in H.
      spliter.
      assumption.
      unfold Out in H0.
      spliter.
      induction H10.
        eapply between_inner_transitivity.
          apply between_symmetry.
          apply H7.
        assumption.
      eapply outer_transitivity_between.
        apply between_symmetry.
        apply H7.
        assumption.
      auto.
    unfold Out in H0.
    spliter.
    assumption.
Qed.

Lemma conga_cop__or_out_ts : forall A B C C', Coplanar A B C C' -> CongA A B C A B C' ->
  Out B C C' \/ TS A B C C'.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert (A0=A1).
      eapply construction_uniqueness.
        3:apply H5.
        2:apply H4.
        auto.
        assumption.
      assumption.
    subst A1.
    induction (eq_dec_points C0 C1).
      subst C1.
      left.
      unfold Out.
      repeat split; try assumption.
      eapply l5_3.
        apply H6.
      assumption.
    right.
    assert(exists M, Midpoint M C0 C1).
      apply midpoint_existence.
    ex_and H14 M.
    assert(Cong B C0 B C1).
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_symmetry.
        apply cong_left_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert(Per A0 M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per B M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert(Per A0 M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Per B M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert (B <> A0).
      intro.
      subst A0.
      apply between_identity in H8.
      subst A.
      absurde.
    assert (Cong A C0 A C1).
      eapply (l4_2 B A A0 C0 B A A0 C1).
      unfold IFSC.
      repeat split; try assumption.
        apply cong_reflexivity.
      apply cong_reflexivity.
    assert (Per A M C0).
      unfold Per.
      exists C1.
      split.
        assumption.
      assumption.
    assert (Per A M C1).
      unfold Per.
      exists C0.
      split.
        apply l7_2.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Col B A M).
      apply cop_per2__col with C0.
        apply coplanar_perm_12, col_cop__cop with C1; Col.
        apply coplanar_perm_12, col_cop__cop with C'; Col.
        apply coplanar_perm_5, col_cop__cop with C; Col; Cop.
        intro.
        subst M.
        apply is_midpoint_id in H15.
        contradiction.
        assumption.
      assumption.
    (************)
    induction(eq_dec_points B M).
      subst M.
      assert(~Col A B C).
        eapply per_not_col.
          assumption.
          auto.
        eapply per_col.
          2:apply H23.
          intro.
          subst C1.
          apply l7_2 in H15.
          apply is_midpoint_id in H15.
          subst C0.
          absurde.
        assert(Bet C B C1).
          eapply between_exchange3.
            apply between_symmetry.
            apply H6.
          apply midpoint_bet.
          assumption.
        unfold Col.
        right; right.
        assumption.
      assert(~Col A B C').
        eapply per_not_col.
          assumption.
          auto.
        eapply per_col.
          2:apply H23.
          intro.
          subst C1.
          apply l7_2 in H15.
          apply is_midpoint_id in H15.
          subst C0.
          absurde.
        assert(Bet C' B C0).
          eapply between_exchange3.
            apply between_symmetry.
            apply H10.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
      unfold TS.
      repeat split.
        Col.
        Col.
      exists B.
      split.
        Col.
      apply between_symmetry.
      eapply between_exchange3.
        apply between_symmetry.
        apply H10.
      apply between_symmetry.
      eapply between_exchange3.
        apply between_symmetry.
        apply H6.
      apply midpoint_bet.
      assumption.
    (***********)
    assert(TS B M C0 C1).
      unfold TS.
      repeat split.
        intro.
        apply per_not_col in H17.
          apply H17.
          apply col_permutation_1.
          assumption.
          assumption.
        intro.
        subst C0.
        apply is_midpoint_id in H15.
        subst C1.
        absurde.
        intro.
        apply per_not_col in H19.
          apply H19.
          Col.
          assumption.
        intro.
        subst C1.
        apply l7_2 in H15.
        apply is_midpoint_id in H15.
        subst C0.
        absurde.
      exists M.
      split.
        apply col_trivial_3.
      apply midpoint_bet.
      assumption.
    apply (col_two_sides _ _ A) in H26.
      apply invert_two_sides in H26.
      (*************************)
      assert(TS A B C C1).
        eapply l9_5.
          apply H26.
          apply col_trivial_3.
        unfold Out.
        repeat split.
          intro.
          subst C0.
          apply cong_symmetry in H14.
          apply cong_identity in H14.
          subst C1.
          absurde.
          assumption.
        right.
        assumption.
      apply l9_2.
      eapply l9_5.
        apply l9_2.
        apply H27.
        apply col_trivial_3.
      unfold Out.
      repeat split.
        intro.
        subst C1.
        apply cong_identity in H14.
        subst C0.
        absurde.
        intro.
        subst C'.
        apply cong_identity in H7.
        subst C0.
        absurde.
      right.
      assumption.
      Col.
    auto.
Qed.


Lemma cong2_conga_cong : forall A B C A' B' C',
 CongA A B C A' B' C' -> Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    unfold CongA in H.
    spliter.
    ex_and H5 A0.
    ex_and H6 C0.
    ex_and H5 A1.
    ex_and H6 C1.
    assert(Cong A C0 A' C1).
      eapply (l4_2 B A A0 C0 B' A' A1 C1).
      repeat split; try assumption.
        eapply l2_11.
          apply H5.
          apply H9.
          apply cong_commutativity.
          assumption.
        eapply cong_transitivity.
          apply H6.
        apply cong_commutativity.
        apply cong_symmetry.
        eapply cong_transitivity.
          2: apply H0.
        apply cong_commutativity.
        assumption.
        eapply cong_transitivity.
          apply H6.
        apply cong_commutativity.
        apply cong_symmetry.
        eapply cong_transitivity.
          2: apply H0.
        apply cong_commutativity.
        assumption.
      eapply cong_transitivity.
        eapply l2_11.
          apply H7.
          apply H11.
          assumption.
        eapply cong_transitivity.
          apply H8.
        apply cong_symmetry.
        eapply cong_transitivity.
          apply H12.
        assumption.
      apply cong_reflexivity.
    apply cong_commutativity.
    eapply (l4_2 B C C0 A B' C' C1 A').
    repeat split; try assumption.
      eapply l2_11.
        apply H7.
        apply H11.
        assumption.
      eapply cong_transitivity.
        apply H8.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H1.
      apply cong_symmetry.
      assumption.
      eapply cong_transitivity.
        apply H8.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H1.
      apply cong_symmetry.
      assumption.
      apply cong_commutativity.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.


Lemma angle_construction_1 : forall A B C A' B' P,
 ~ Col A B C -> ~ Col A' B' P ->
 exists C', CongA A B C A' B' C' /\ OS A' B' C' P.
Proof.
    intros.
    assert (exists C0, Col B A C0 /\ Perp B A C C0).
      eapply l8_18_existence.
      intro.
      apply H.
      apply col_permutation_4.
      assumption.
    ex_and H1 C0.
    induction(eq_dec_points B C0).
      subst C0.
      assert (exists  C', Per C' B' A' /\ Cong C' B' C B /\ OS A' B' C' P).
        apply ex_per_cong.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply col_trivial_2.
        assumption.
      ex_and  H3 C'.
      exists C'.
      split.
        eapply l11_16.
          apply perp_perp_in in H2.
          apply perp_in_comm in H2.
          apply perp_in_per in H2.
          assumption.
          intro.
          subst A.
          apply H.
          apply col_trivial_1.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply l8_2.
          assumption.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
        intro.
        subst C'.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst C.
        apply H.
        apply col_trivial_2.
      assumption.
    (*********** B <> C0 ***********)
    induction (out_dec B A C0).
      assert (exists C0', Out B' A' C0' /\ Cong B' C0' B C0).
        eapply segment_construction_3.
          intro.
          subst A'.
          apply H0.
          apply col_trivial_1.
        assert (Perp_at C0 C0 C B C0).
          eapply perp_perp_in.
          apply perp_sym.
          eapply perp_col.
            assumption.
            apply perp_right_comm.
            apply H2.
          assumption.
        assumption.
      ex_and H5 C0'.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ OS B' C0' C' P).
        apply ex_per_cong.
          intro.
          subst C0'.
          unfold Out in H5.
          spliter.
          absurde.
          intro.
          subst C0.
          unfold Perp in H2.
          ex_and H2 X.
          unfold Perp_at in H7.
          spliter.
          absurde.
          apply col_trivial_2.
        intro.
        apply H0.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ C0').
          intro.
          subst C0'.
          unfold Out in H5.
          spliter.
          absurde.
          assumption.
        apply out_col.
        apply l6_6.
        assumption.
      ex_and H7 C'.
      assert (Cong_3 C0 B C C0' B' C').
        unfold Cong_3.
        repeat split.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        eapply (l10_12 _ C0).
          assert(Perp  B C0 C C0 ).
            eapply perp_col.
              intro.
              subst C0.
              apply perp_distinct in H2.
              spliter.
              absurde.
              apply H2.
            assumption.
          apply perp_left_comm in H10.
          apply perp_perp_in in H10.
          apply perp_in_per.
          apply perp_in_comm.
          assumption.
          apply l8_2.
          apply H7.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      exists C'.
      split.
        eapply (l11_10 C0 _ _ C0').
          apply cong3_conga.
            3: apply H10.
            intro.
            subst C0.
            absurde.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          assumption.
          apply out_trivial.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          assumption.
        apply out_trivial.
        intro.
        subst C'.
        apply l8_8 in H7.
        subst C0'.
        unfold Out in H5.
        spliter.
        absurde.
      apply invert_one_side.
      eapply col_one_side.
        3: apply H9.
        apply out_col.
        apply l6_6.
        assumption.
      intro.
      subst A'.
      apply H0.
      apply col_trivial_1.
    (*********************)
    apply not_out_bet in H4.
      prolong A' B' C0' B C0.
      assert (exists C' , Per C' C0' B' /\ Cong C' C0' C C0 /\ OS B' C0' C' P).
        apply ex_per_cong.
          intro.
          subst C0'.
          apply cong_symmetry in H6.
          apply cong_identity in H6.
          subst C0.
          absurde.
          intro.
          subst C0.
          apply perp_distinct in H2.
          spliter.
          absurde.
          apply col_trivial_2.
        intro.
        apply H0.
        apply col_permutation_2.
        eapply col_transitivity_1.
          2:apply H7.
          intro.
          subst C0'.
          apply cong_symmetry in H6.
          apply cong_identity in H6.
          subst C0.
          absurde.
        unfold Col.
        right; right.
        assumption.
      ex_and H7 C'.
      exists C'.
      split.
        assert (Cong_3 C0 B C C0' B' C').
          repeat split.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_commutativity.
          eapply (l10_12 _ C0 _ _ C0').
            assert(Perp  B C0 C C0 ).
              eapply perp_col.
                intro.
                subst C0.
                apply perp_distinct in H2.
                spliter.
                absurde.
                apply H2.
              assumption.
            apply perp_left_comm in H10.
            apply perp_perp_in in H10.
            apply perp_in_per.
            apply perp_in_sym.
            assumption.
            assumption.
            apply cong_symmetry.
            assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        eapply l11_13.
          apply cong3_conga.
            3: apply H10.
            auto.
          intro.
          subst C.
          apply H.
          apply col_trivial_2.
          apply between_symmetry.
          assumption.
          intro.
          subst A.
          apply H.
          apply col_trivial_1.
          apply between_symmetry.
          assumption.
        intro.
        subst A'.
        apply H0.
        apply col_trivial_1.
      apply invert_one_side.
      eapply col_one_side.
        3: apply H9.
        unfold Col.
        right; right.
        assumption.
      intro.
      subst A'.
      apply H0.
      apply col_trivial_1.
    apply col_permutation_4.
    assumption.
Qed.

Lemma angle_construction_2 : forall A B C A' B' P,
 A <> B -> A <> C -> B <> C -> A' <> B' -> ~ Col A' B' P ->
 exists C', CongA A B C A' B' C' /\ (OS A' B' C' P \/ Col A' B' C').
Proof.
    intros.
    spliter.
    induction (col_dec A B C).
      induction (out_dec B A C).
        exists A'.
        split.
          assert(CongA A B A A B C).
            eapply l11_10.
              apply conga_refl.
                3: apply H5.
              auto.
              2: apply H5.
              auto.
              assumption.
            apply out_trivial.
            auto.
          assert (CongA A B A A' B' A').
            apply conga_trivial_1.
              assumption.
            assumption.
          apply conga_sym.
          eapply conga_trans.
            apply conga_sym.
            apply H7.
          assumption.
        right.
        apply col_trivial_3.
      apply not_out_bet in H5.
        prolong A' B' C' A'  B'.
        exists C'.
        split.
          eapply conga_line; try assumption.
            intro.
            subst C'.
            apply cong_symmetry in H7.
            apply cong_identity in H7.
            subst A'.
            absurde.
        right.
        unfold Col.
        left.
        assumption.
      assumption.
    assert(exists C' , CongA A B C A' B' C' /\ OS A' B' C' P).
      apply angle_construction_1.
        assumption.
      assumption.
    ex_and H5 C'.
    exists C'.
    split.
      assumption.
    left.
    assumption.
Qed.

Lemma ex_conga_ts : forall A B C A' B' P,
    ~ Col A B C -> ~ Col A' B' P ->
    exists C' : Tpoint, CongA A B C A' B' C' /\ TS A' B' C' P.
Proof.
  intros A B C A' B' P HNCol HNCol'.
  assert (HP' : exists P', Midpoint A' P P') by (apply symmetric_point_construction).
  destruct HP' as [P' HMid].
  assert (~ Col A' B' P').
  { intro HCol.
    apply HNCol'.
    assert (Col A' P P') by (apply midpoint_col; auto).
    apply (col3 A' P'); Col.
    intro; treat_equalities; Col.
  }
  assert (HC' : exists C', CongA A B C A' B' C' /\ OS A' B' C' P').
  apply (angle_construction_1 A B C A' B' P'); auto.
  destruct HC' as [C' [HConga HOne]].
  exists C'.
  split; auto.
  apply (l9_8_2 A' B' P'); Side.
  split; Col; split; Col.
  exists A'.
  split; Col.
  destruct HMid; Between.
Qed.


Lemma l11_15 : forall A B C D E P, ~ Col A B C -> ~ Col D E P ->
 exists F, CongA A B C D E F /\ OS E D F P /\
          (forall F1 F2, ((CongA A B C D E F1 /\ OS E D F1 P) /\
                          (CongA A B C D E F2 /\ OS E D F2 P)) -> Out E F1 F2).
Proof.
    intros.
    assert(exists F, CongA A B C D E F /\  OS D E F P)
      by (apply angle_construction_1; assumption).
    ex_and H1 F.
    exists F.
    split.
      assumption.
    split.
      apply invert_one_side.
      assumption.
    intros.
    spliter.
    assert(Out E F1 F2 \/ TS D E F1 F2).
      apply conga_cop__or_out_ts.
      apply coplanar_trans_1 with P; Cop; Col.
      eapply conga_trans.
        apply conga_sym.
        apply H3.
      assumption.
    induction H7.
      assumption.
    assert(OS E D F1 F2).
      eapply one_side_transitivity.
        apply H6.
      apply one_side_symmetry.
      assumption.
    apply l9_9_bis in H8.
    apply invert_two_sides in H7.
    contradiction.
Qed.

Lemma l11_19 : forall A B P1 P2,
  Per A B P1 -> Per A B P2 -> OS A B P1 P2 ->
  Out B P1 P2.
Proof.
    intros.
    induction (col_dec A B P1).
      induction (l8_9 A B P1 H H2).
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        intuition.
      subst.
      unfold OS in *.
      decompose [ex and] H1.
      unfold TS in *.
      spliter.
      assert (Col B A B) by Col.
      intuition.
    induction (col_dec A B P2).
      induction (l8_9 A B P2 H0 ).
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        intuition.
        subst.
        unfold OS in *.
        decompose [ex and] H1.
        unfold TS in *.
        spliter.
        assert (Col B A B) by Col.
        intuition.
      Col.
    assert (T:=l11_15 A B P1 A B P2 H2 H3).
    decompose [ex and] T.
    apply H7.
    split.
      split.
        apply conga_refl.
          intro;subst;Col.
        intro;subst;Col.
      apply invert_one_side;auto.
    split.
      apply l11_16;try assumption.
        intro;subst;Col.
        intro;subst;Col.
        intro;subst;Col.
      intro;subst;Col.
    apply one_side_reflexivity.
    Col.
Qed.

Lemma l11_22_bet :
 forall A B C P A' B' C' P',
  Bet A B C ->
  TS P' B' A' C' ->
  CongA A B P A' B' P' /\ CongA P B C  P' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    spliter.
    prolong A' B' C'' B C.
    assert(CongA C B P C'' B' P').
      eapply l11_13.
        2:apply H.
        apply H1.
        unfold CongA in H2.
        spliter.
        assumption.
        assumption.
      intro.
      subst C''.
      apply cong_symmetry in H4.
      apply cong_identity in H4.
      subst C.
      unfold CongA in H2.
      spliter.
      absurde.
    assert (CongA C'' B' P' C' B' P').
      eapply conga_trans.
        apply conga_sym.
        apply H5.
      apply conga_comm.
      assumption.
    assert(Out B' C' C'' \/ TS P' B' C' C'').
      apply conga_cop__or_out_ts.
      apply coplanar_perm_2, col_cop__cop with A'; Col; Cop.
      apply ts_distincts in H0.
      spliter.
      auto.
      apply conga_comm.
      apply conga_sym.
      assumption.
    induction H7.
      unfold Out in H7.
      spliter.
      induction H9.
        eapply between_inner_transitivity.
          apply H3.
        assumption.
      eapply outer_transitivity_between.
        apply H3.
        assumption.
      auto.
    induction (col_dec C' B' P').
      unfold TS in H7.
      spliter.
      apply False_ind.
      apply H7.
      apply col_permutation_5.
      assumption.
    assert (B' <> P').
      intro.
      subst P'.
      apply H8.
      apply col_trivial_2.
    assert (TS B' P' A' C'').
      unfold TS.
      repeat split.
        unfold TS in H0.
        spliter.
        intro.
        apply H0.
        apply col_permutation_5.
        assumption.
        intro.
        unfold TS in H7.
        spliter.
        apply H11.
        apply col_permutation_5.
        assumption.
      exists B'.
      split.
        apply col_trivial_1.
      assumption.
    assert (OS B' P' C' C'').
      eapply l9_8_1.
        apply l9_2.
        apply invert_two_sides.
        apply H0.
      apply l9_2.
      assumption.
    apply l9_9_bis in H11.
    apply invert_two_sides in H7.
    contradiction.
Qed.

Lemma l11_22a :
 forall A B C P A' B' C' P',
 TS B P A C /\ TS B' P' A' C' /\
 CongA A B P A' B' P' /\ CongA P B C  P' B' C' ->
 CongA A B C A' B' C'.
Proof.
    intros.
    spliter.
    assert (A <> B /\ A' <> B' /\ P <> B /\ P' <> B' /\ C <> B /\ C' <> B').
      unfold CongA in *.
      spliter.
      repeat split; assumption.
    assert(A <> C /\ A' <> C').
      unfold TS in *.
      spliter.
      ex_and H12 T.
      ex_and H10 T'.
      split.
        intro.
        subst C.
        apply between_identity in H13.
        subst T.
        contradiction.
      intro.
      subst C'.
      apply between_identity in H14.
      subst T'.
      contradiction.
    spliter.
    assert(exists A'', Out B' A' A'' /\ Cong B' A'' B A).
      eapply segment_construction_3; auto.
    ex_and H11 A''.
    unfold TS in H.
    assert (~ Col A B P).
      spliter.
      assumption.
    spliter.
    ex_and H15 T.
    induction (eq_dec_points B T).
      subst T.
      assert(Bet A' B' C').
        eapply l11_22_bet.
          apply H16.
          apply invert_two_sides.
          apply H0.
        split.
          apply H1.
        assumption.
      apply conga_line.
        assumption.
        auto.
        assumption.
        auto.
      assumption.
      assumption.
    induction(bet_dec P B T).
      assert(exists T'', Col B' P' T'' /\ (Out B' P' T'' <-> Out B P T) /\ Cong B' T'' B T).
        prolong P' B' T'' B T.
        exists T''.
        split.
          unfold Col.
          right; right.
          apply between_symmetry.
          assumption.
        split.
          split.
            intro.
            assert(Bet P' B' T'' /\ Out B' P' T'').
              split; assumption.
            apply (not_bet_and_out _ _  _)in H22.
            contradiction.
          intro.
          assert(Bet P B T /\ Out B P T).
            split; assumption.
          apply (not_bet_and_out _ _  _)in H22.
          contradiction.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply cong_symmetry in H21.
        apply cong_identity in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(CongA A B T A' B' T'').
        apply conga_comm.
        eapply l11_13.
          apply conga_comm.
          apply H1.
          assumption.
          auto.
          eapply out_to_bet.
            apply col_permutation_4.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        auto.
      assert(CongA A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        spliter.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A C A'' C'').
        eapply l2_11.
          apply H16.
          apply H24.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong C B C'' B').
        eapply (five_segment).
          5:apply H16.
          5: apply H24.
          assumption.
          apply cong_symmetry.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        intro.
        subst T.
        apply H13.
        assumption.
      assert(CongA A B C A'' B' C'').
        apply cong3_conga.
          assumption.
          assumption.
        repeat split.
          apply cong_commutativity.
          apply cong_symmetry.
          assumption.
          assumption.
        apply cong_commutativity.
        assumption.
      assert(CongA C B T  C'' B' T'').
        apply cong3_conga.
          assumption.
          auto.
        repeat split.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert (CongA P B C P' B' C'').
        eapply l11_13.
          apply conga_comm.
          apply H32.
          apply between_symmetry.
          assumption.
          assumption.
          apply between_symmetry.
          eapply out_to_bet.
            eapply col_permutation_4.
            assumption.
            split.
              apply H22.
            assumption.
          assumption.
        assumption.
      assert(CongA P' B' C' P' B' C'').
        eapply conga_trans.
          apply conga_sym.
          apply H2.
        assumption.
      assert(Out B' C' C'' \/ TS P' B' C' C'').
        apply conga_cop__or_out_ts.
        assert (HH := H0); destruct HH as [HNCol].
        apply coplanar_trans_1 with A'; Col.
          Cop.
        assert_diffs; apply coplanar_perm_19, col_cop__cop with A''; Col.
        exists T''.
        right.
        left.
        split; Col.
        assumption.
      induction H35.
        eapply l11_10.
          apply H31.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        assumption.
      assert(TS B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply col_trivial_1.
          assumption.
          apply col_trivial_1.
        apply out_trivial.
        auto.
      apply invert_two_sides in H35.
      apply l9_2 in H35.
      assert(OS B' P'  A'' C'').
        unfold OS.
        exists C'.
        split; assumption.
      assert (TS B' P' A''  C'').
        unfold TS.
        repeat split.
          intro.
          unfold TS in H0.
          assert (~ Col A' B' P').
            spliter.
            assumption.
          spliter.
          apply H39.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ A'').
            intro.
            subst A''.
            unfold Out in H11.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          apply out_col in H11.
          apply col_permutation_5.
          assumption.
          intro.
          unfold TS in H35.
          spliter.
          apply H35.
          assumption.
        exists T''.
        split.
          apply col_permutation_2.
          assumption.
        assumption.
      apply l9_9 in H38.
      contradiction.
    apply not_bet_out in H18.
      assert(exists T'', Col B' P' T'' /\ (Out B' P' T'' <-> Out B P T) /\ Cong B' T'' B T).
        assert (exists T'', Out B' P' T'' /\ Cong B' T'' B T).
          apply segment_construction_3.
            auto.
          assumption.
        ex_and H19 T''.
        exists T''.
        split.
          apply out_col in H19.
          assumption.
        split.
          split.
            intro.
            assumption.
          intro.
          assumption.
        assumption.
      ex_and H19 T''.
      destruct H20.
      assert (B' <> T'').
        intro.
        subst T''.
        apply cong_symmetry in H21.
        apply cong_identity in H21.
        contradiction.
      assert(exists C'', Bet A'' T'' C'' /\ Cong T'' C'' T C).
        prolong A'' T'' C'' T C.
        exists C''.
        split; assumption.
      ex_and H24 C''.
      assert(CongA A B T A' B' T'').
        eapply l11_10.
          apply H1.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply l6_6.
        apply H22.
        assumption.
      assert(CongA A B T A'' B'  T'').
        eapply l11_10.
          apply H26.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A T A'' T'').
        assert(HH:= l11_4_1 A B T A'' B' T'' H27).
        spliter.
        apply H32.
        split.
          apply out_trivial.
          auto.
        split.
          apply out_trivial.
          assumption.
        split.
          apply out_trivial.
          intro.
          subst A''.
          absurde.
        split.
          apply out_trivial.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A C A'' C'').
        eapply l2_11.
          apply H16.
          apply H24.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong C B C'' B').
        eapply (five_segment).
          5:apply H16.
          5: apply H24.
          assumption.
          apply cong_symmetry.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        intro.
        apply H13.
        subst T.
        assumption.
      assert(CongA A B C A'' B' C'').
        apply cong3_conga.
          assumption.
          assumption.
        repeat split.
          apply cong_commutativity.
          apply cong_symmetry.
          assumption.
          assumption.
        apply cong_commutativity.
        assumption.
      assert(CongA C B T  C'' B' T'').
        apply cong3_conga.
          assumption.
          auto.
        repeat split.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      eapply l11_10.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        assumption.
      assert(Out B' C' C'' \/ TS P' B' C' C'').
        apply conga_cop__or_out_ts.
        assert (HH := H0); destruct HH as [HNCol].
        apply coplanar_trans_1 with A'; Col.
          Cop.
        assert_diffs; apply coplanar_perm_19, col_cop__cop with A''; Col.
        exists T''.
        right.
        left.
        split; Col.
        apply conga_comm.
        eapply conga_trans.
          apply conga_comm.
          apply conga_sym.
          apply H2.
        eapply l11_10.
          apply H32.
          apply out_trivial.
          auto.
          assumption.
          apply out_trivial.
          intro.
          subst C''.
          apply cong_identity in H30.
          contradiction.
        apply H22.
        assumption.
      induction H33.
        assumption.
      assert(TS B' P' A'' C').
        apply l9_2.
        eapply l9_5.
          eapply l9_2.
          eapply l9_5.
            apply H0.
            apply col_trivial_1.
          assumption.
          apply col_trivial_1.
        apply out_trivial.
        auto.
      assert(OS B' P'  A'' C'').
        unfold OS.
        exists C'.
        split.
          assumption.
        apply invert_two_sides in H33.
        apply l9_2 in H33.
        assumption.
      assert (TS B' P' A''  C'').
        unfold TS.
        repeat split.
          intro.
          unfold TS in H34.
          spliter.
          apply H34.
          assumption.
          intro.
          unfold TS in H33.
          spliter.
          apply H37.
          apply col_permutation_5.
          assumption.
        exists T''.
        split.
          apply col_permutation_2.
          assumption.
        assumption.
      apply l9_9 in H36.
      contradiction.
      auto.
    apply col_permutation_3.
    assumption.
Qed.

Lemma l11_22b :
 forall A B C P A' B' C' P',
 OS B P A C /\ OS B' P' A' C' /\
 CongA A B P A' B' P' /\ CongA P B C  P' B' C' ->
 CongA A B C A' B' C'.
Proof.
    intros.
    spliter.
    prolong A B D A B.
    prolong A' B' D' A' B'.
    assert(CongA D B P D' B' P').
      eapply l11_13.
        apply H1.
        assumption.
        intro.
        subst D.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst A.
        unfold CongA in H1.
        spliter.
        absurde.
        assumption.
      intro.
      subst D'.
      apply cong_symmetry in H6.
      apply cong_identity in H6.
      subst A'.
      unfold CongA in H1.
      spliter.
      absurde.
    assert (CongA D B C D' B' C').
      eapply (l11_22a _ _ _ P _ _ _ P').
      split.
        eapply l9_2.
        eapply l9_8_2.
          2: apply H.
        unfold OS in H.
        ex_and H T.
        unfold TS in H.
        unfold TS in H8.
        spliter.
        repeat split.
          assumption.
          intro.
          apply H.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D).
            intro.
            subst D.
            unfold CongA in H7.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B.
        split.
          apply col_trivial_1.
        assumption.
      split.
        eapply l9_2.
        eapply l9_8_2.
          2: apply H0.
        unfold OS in H0.
        ex_and H0 T'.
        unfold TS in H0.
        unfold TS in H8.
        spliter.
        repeat split.
          assumption.
          intro.
          apply H0.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ D').
            intro.
            subst D'.
            unfold CongA in H7.
            spliter.
            absurde.
            apply col_permutation_4.
            assumption.
          unfold Col.
          right; right.
          assumption.
        exists B'.
        split.
          apply col_trivial_1.
        assumption.
      split; assumption.
    eapply l11_13.
      apply H8.
      apply between_symmetry.
      assumption.
      intro.
      subst A.
      unfold CongA in H1.
      spliter.
      absurde.
      apply between_symmetry.
      assumption.
    intro.
    subst A'.
    unfold CongA in H1.
    spliter.
    absurde.
Qed.

Lemma l11_22 :
 forall A B C P A' B' C' P',
 ((TS B P A C /\ TS B' P' A' C')\/
  (OS B P A C /\ OS B' P' A' C')) /\
  CongA A B P A' B' P' /\ CongA P B C  P' B' C' ->
 CongA A B C A' B' C'.
Proof.
    intros.
    spliter.
    induction H.
      eapply (l11_22a _ _ _ P _ _ _ P');tauto.
    eapply (l11_22b _ _ _ P _ _ _ P');tauto.
Qed.

Lemma l11_24 :
 forall P A B C,
  InAngle P A B C -> InAngle P C B A.
Proof.
    unfold InAngle.
    intros.
    spliter.
    ex_and H2 X.
    repeat split; try assumption.
    exists X.
    split.
      apply between_symmetry.
      assumption.
    assumption.
Qed.

Lemma out_in_angle :
 forall A B C P,
  Out B A C -> Out B P A ->
  InAngle P A B C.
Proof.
    intros.
    unfold InAngle.
    unfold Out in H.
    unfold Out in H0.
    spliter.
    split.
      assumption.
    split.
      assumption.
    split.
      assumption.
    induction H4; induction H2.
      assert(exists X, Midpoint X A C).
        eapply midpoint_existence.
      ex_and H5 X.
      exists X.
      split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H6.
        assert (A = B).
          eapply between_equality.
            apply H6.
          assumption.
        contradiction.
        assumption.
      right.
      induction (eq_dec_points P A).
        subst P.
        eapply between_inner_transitivity.
          apply H4.
        apply midpoint_bet.
        assumption.
      assert(Bet P A C).
        eapply between_exchange3.
          apply H2.
        assumption.
      assert(Bet P A X).
        eapply between_inner_transitivity.
          apply H7.
        apply midpoint_bet.
        assumption.
      eapply outer_transitivity_between.
        apply H2.
        assumption.
      assumption.
      assert(exists X, Midpoint X A C).
        eapply midpoint_existence.
      ex_and H5 X.
      exists X.
      repeat split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H6.
        assert (A = B).
          eapply between_equality.
            apply H6.
          assumption.
        contradiction.
        assumption.
      assert(Bet B C P \/ Bet B P C).
        eapply l5_1.
          2: apply H4.
          auto.
        assumption.
      induction H5.
        left.
        assert(Bet B X C).
          eapply between_exchange2.
            apply H4.
          apply midpoint_bet.
          assumption.
        eapply between_exchange4.
          apply H7.
        assumption.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H4.
        apply  midpoint_bet.
        assumption.
      eapply l5_1.
        2:apply H7.
        auto.
      assumption.
      assert(Bet B P C \/ Bet B C P).
        eapply l5_3.
          apply H2.
        assumption.
      induction H5.
        assert(exists X, Midpoint X A C).
          eapply midpoint_existence.
        ex_and H6 X.
        exists X.
        split.
          apply midpoint_bet.
          assumption.
        right.
        repeat split.
          intro.
          subst X.
          apply midpoint_bet in H7.
          apply between_symmetry in H7.
          assert (C = B).
            eapply between_equality.
              apply H7.
            assumption.
          contradiction.
          assumption.
        right.
        assert(Bet B C X).
          eapply between_inner_transitivity.
            apply H4.
          apply midpoint_bet.
          apply l7_2.
          assumption.
        eapply between_exchange4.
          apply H5.
        assumption.
      assert(exists X, Midpoint X A C).
        eapply midpoint_existence.
      ex_and H6 X.
      exists X.
      repeat split.
        apply midpoint_bet.
        assumption.
      right.
      repeat split.
        intro.
        subst X.
        apply midpoint_bet in H7.
        apply between_symmetry in H7.
        assert (C = B).
          eapply between_equality.
            apply H7.
          assumption.
        contradiction.
        assumption.
      assert (Bet B C X).
        eapply between_inner_transitivity.
          apply H4.
        apply midpoint_bet.
        eapply l7_2.
        assumption.
      eapply l5_1.
        2:apply H6.
        auto.
      assumption.
    assert(exists X, Midpoint X A C).
      eapply midpoint_existence.
    ex_and H5 X.
    exists X.
    split.
      apply midpoint_bet.
      assumption.
    right.
    repeat split.
      intro.
      subst X.
      apply midpoint_bet in H6.
      apply between_symmetry in H6.
      assert (C = B).
        eapply between_equality.
          apply H6.
        assumption.
      contradiction.
      assumption.
    left.
    assert(Bet B X A).
      eapply between_exchange2.
        apply H4.
      apply midpoint_bet.
      apply l7_2.
      assumption.
    eapply between_exchange4.
      apply H5.
    assumption.
Qed.


Lemma col_in_angle :
 forall A B C P,
  A <> B -> C <> B -> P <> B ->
  Out B A P \/ Out B C P ->
  InAngle P A B C.
Proof.
    intros.
    induction H2.
      repeat split; try assumption.
      exists A.
      split.
        apply between_symmetry.
        apply between_trivial.
      right.
      assumption.
    repeat split; try assumption.
    exists C.
    split.
      apply between_trivial.
    right.
    assumption.
Qed.


Lemma out321__inangle :
 forall A B C P,
  C <> B -> Out B A P ->
  InAngle P A B C.
Proof.
    intros.
    assert_diffs.
    apply col_in_angle; auto.
Qed.


Lemma inangle1123 :
 forall A B C,
  A <> B -> C <> B ->
  InAngle A A B C.
Proof.
    intros.
    apply out321__inangle; auto.
    apply out_trivial; auto.
Qed.


Lemma out341__inangle :
 forall A B C P,
  A <> B -> Out B C P ->
  InAngle P A B C.
Proof.
    intros.
    assert_diffs.
    apply col_in_angle; auto.
Qed.


Lemma inangle3123 :
 forall A B C,
  A <> B -> C <> B ->
  InAngle C A B C.
Proof.
    intros.
    apply out341__inangle; auto.
    apply out_trivial; auto.
Qed.


Lemma in_angle_two_sides :
 forall A B C P,
  ~ Col B A P -> ~ Col B C P ->
  InAngle P A B C ->
  TS P B A C.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      unfold TS.
      repeat split.
        intro.
        apply H.
        apply col_permutation_2.
        assumption.
        intro.
        apply H0.
        apply col_permutation_2.
        assumption.
      exists B.
      split.
        apply col_trivial_3.
      assumption.
    repeat split.
      intro.
      apply H.
      apply col_permutation_2.
      assumption.
      intro.
      apply H0.
      apply col_permutation_2.
      assumption.
    exists X.
    split.
      apply out_col in H5.
      apply col_permutation_1.
      assumption.
    assumption.
Qed.

Lemma in_angle_out :
 forall A B C P,
  Out B A C ->
  InAngle P A B C ->
  Out B A P.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      assert( Bet A B C /\ Out B A C).
        split; assumption.
      apply not_bet_and_out in H4.
      contradiction.
    unfold Out in *.
    spliter.
    induction H8; induction H6.
      repeat split; try assumption.
      left.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H8.
        apply H3.
      eapply between_exchange4.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H8.
        assumption.
      eapply l5_3.
        apply H9.
      assumption.
      repeat split; try assumption.
      assert(Bet B X A).
        eapply between_exchange2.
          apply H8.
        apply between_symmetry.
        assumption.
      eapply l5_1.
        2: apply H9.
        auto.
      assumption.
    repeat split; try assumption.
    right.
    assert(Bet B X A).
      eapply between_exchange2.
        apply H8.
      apply between_symmetry.
      assumption.
    eapply between_exchange4.
      apply H6.
    assumption.
Qed.

Lemma col_in_angle_out :
 forall A B C P,
  Col B A P ->
  ~ Bet A B C ->
  InAngle P A B C ->
  Out B A P.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      contradiction.
    induction (eq_dec_points A X).
      subst X.
      assumption.
    apply not_bet_out in H0.
      assert(Out B A P /\ Out B C P).
        eapply out2_bet_out.
          assumption.
          apply H5.
        assumption.
      spliter.
      assumption.
    assert (Col B A X).
      eapply col_transitivity_1.
        2: apply col_permutation_5.
        2: apply H.
        auto.
      apply out_col in H5.
      apply col_permutation_5.
      assumption.
    eapply col_transitivity_2.
      2: apply col_permutation_3.
      2:apply H7.
      auto.
    unfold Col.
    right; right.
    apply between_symmetry.
    assumption.
Qed.

Lemma l11_25_aux : forall P A B C A',
 InAngle P A B C ->
 ~ Bet A B C ->
 Out B A' A ->
 InAngle P A' B C.
Proof.
    intros.
    unfold Out in H1.
    unfold InAngle in H.
    spliter.
    repeat  split ; try assumption.
    induction H3.
      ex_and H6 X.
      assert(exists T, Bet A' T C /\ Bet X T B).
        eapply inner_pasch.
          apply H3.
        apply between_symmetry.
        assumption.
      ex_and H8 T.
      exists T.
      split.
        assumption.
      right.
      induction H7.
        subst B.
        contradiction.
      unfold Out in *.
      spliter.
      repeat split.
        intro.
        subst T.
        apply H0.
        apply between_symmetry.
        eapply outer_transitivity_between.
          apply between_symmetry.
          apply H8.
          assumption.
        auto.
        assumption.
      induction H11.
        left.
        eapply between_exchange4.
          apply between_symmetry.
          apply H9.
        assumption.
      eapply l5_3.
        apply between_symmetry.
        apply H9.
      assumption.
    ex_and H6 X.
    induction H7.
      subst X.
      contradiction.
    assert(exists T, Bet A' T C /\ Bet B X T).
      eapply outer_pasch.
        apply between_symmetry.
        apply H3.
      apply between_symmetry.
      assumption.
    ex_and H8 T.
    exists T.
    split.
      assumption.
    right.
    unfold Out in H7.
    spliter.
    repeat split.
      intro.
      subst T.
      apply between_identity in H9.
      subst X.
      absurde.
      assumption.
    induction H11.
      eapply l5_1.
        2: apply H9.
        auto.
      assumption.
    right.
    eapply between_exchange4.
      apply H11.
    assumption.
Qed.

Lemma l11_25 : forall P A B C A' C' P',
 InAngle P A B C ->
 Out B A' A ->
 Out B C' C ->
 Out B P' P ->
 InAngle P' A' B C'.
Proof.
    intros.
    induction (bet_dec A B C).
      repeat split.
        unfold Out in H0.
        spliter.
        assumption.
        unfold Out in H1.
        spliter.
        assumption.
        unfold Out in H2.
        spliter.
        assumption.
      exists B.
      split.
        eapply bet_out_out_bet.
          apply H3.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      left.
      reflexivity.
    assert(InAngle P A' B C).
      eapply l11_25_aux.
        apply H.
        assumption.
      assumption.
    assert(InAngle P A' B C').
      apply l11_24.
      eapply l11_25_aux.
        apply l11_24.
        apply H4.
        intro.
        apply H3.
        apply between_symmetry.
        eapply bet_out_out_bet.
          apply H5.
          apply out_trivial.
          unfold InAngle in H.
          spliter.
          auto.
        assumption.
      assumption.
    unfold InAngle in H5.
    spliter.
    ex_and H8 X.
    induction H9.
      subst X.
      apply False_ind.
      apply H3.
      eapply bet_out_out_bet.
        apply H8.
        assumption.
      assumption.
    repeat split.
      assumption.
      assumption.
      intro.
      subst P'.
      unfold Out in H2.
      spliter.
      absurde.
    exists X.
    split.
      assumption.
    right.
    eapply l6_7.
      apply H9.
    apply l6_6.
    assumption.
Qed.

Lemma inangle_distincts : forall A B C P, InAngle P A B C ->
  A <> B /\ C <> B /\ P <> B.
Proof.
  intros; unfold InAngle in *; spliter; repeat split; assumption.
Qed.

Lemma segment_construction_0 : forall A B A', exists B', Cong A' B' A B.
Proof.
    intros.
    induction (eq_dec_points A B).
      exists A'.
      subst B.
      apply cong_trivial_identity.
    assert(exists X : Tpoint, A' <> X).
      apply another_point.
    ex_and H0 X.
    assert(HH:=segment_construction_3 A' X A B H1 H).
    ex_and HH B'.
    exists B'.
    assumption.
Qed.

Lemma angle_construction_3 :
 forall A B C A' B',
  A <> B -> C <> B -> A' <> B' ->
  exists C', CongA A B C A' B' C'.
Proof.
    intros.
    assert(exists P, ~Col A' B' P).
      eapply not_col_exists.
      assumption.
    ex_and H2 P.
    induction (eq_dec_points A C).
      subst C.
      exists A'.
      apply conga_trivial_1; assumption.
    assert(exists C', CongA A B C A' B' C' /\ (OS A' B' C' P \/ Col A' B' C')).
      apply angle_construction_2.
        assumption.
        assumption.
        auto.
        assumption.
      assumption.
    ex_and H4 C'.
    exists C'.
    assumption.
Qed.

Lemma l11_28 : forall A B C D A' B' C',
 Cong_3 A B C A' B' C' -> Col A C D ->
 exists D', Cong A D A' D' /\ Cong B D B' D' /\ Cong C D C' D'.
Proof.
    intros.
    induction (eq_dec_points A C).
      subst C.
      unfold Cong_3 in H.
      spliter.
      apply cong_symmetry in H1.
      apply cong_identity in H1.
      subst C'.
      induction(eq_dec_points A B).
        subst B.
        apply cong_symmetry in H2.
        apply cong_identity in H2.
        subst B'.
        assert(exists D', Cong A' D' A D).
          apply segment_construction_0.
        ex_and H1 D'.
        exists D'.
        apply cong_symmetry in H2.
        repeat split; assumption.
      induction (eq_dec_points A D).
        exists A'.
        subst D.
        repeat split.
          apply cong_trivial_identity.
          assumption.
        apply cong_trivial_identity.
      induction (eq_dec_points B D).
        subst D.
        exists B'.
        repeat split.
          assumption.
          apply cong_trivial_identity.
        assumption.
      assert(exists D'', CongA B A D B' A' D'').
        eapply angle_construction_3.
          auto.
          auto.
        intro.
        subst B'.
        apply cong_identity in H.
        contradiction.
      ex_and H5 D''.
      assert(exists D', Out A' D'' D' /\ Cong A' D' A D).
        apply segment_construction_3.
          unfold CongA in H6.
          spliter.
          auto.
        assumption.
      ex_and H5 D'.
      exists D'.
      repeat split.
        apply cong_symmetry.
        assumption.
        assert(CongA B A D B' A' D').
          eapply (l11_10 B A D B' A' D''); try apply out_trivial; try solve [auto].
            intro.
            subst B'.
            unfold CongA in H6.
            spliter.
            absurde.
          apply l6_6.
          assumption.
        eapply (cong2_conga_cong _ A _ _ A' _).
          apply H8.
          assumption.
        Cong.
      Cong.
    unfold Cong_3 in H.
    spliter.
    (*****************)
    induction(eq_dec_points A D).
      subst D.
      exists A'.
      repeat split.
        apply cong_trivial_identity.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    unfold Col in H0.
    induction H0.
      prolong A' C' D' C D.
      exists D'.
      repeat split.
        eapply (l2_11 A C D A' C' D'); try assumption.
        apply cong_symmetry.
        assumption.
        apply cong_commutativity.
        eapply (five_segment_with_def A C D B A' C' D' B').
          repeat split; try assumption.
            apply cong_symmetry.
            assumption.
          apply cong_commutativity.
          assumption.
        assumption.
      apply cong_symmetry.
      assumption.
    induction H0.
      assert(exists D', Bet A' D' C' /\ Cong_3 A D C A' D' C').
        eapply l4_5.
          apply between_symmetry.
          assumption.
        assumption.
      ex_and H5 D'.
      unfold Cong_3 in H6.
      spliter.
      exists D'.
      repeat split.
        assumption.
        apply cong_commutativity.
        eapply (l4_2 A D C B A' D' C' B').
        repeat split; try assumption.
          apply between_symmetry.
          assumption.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    prolong C' A' D' A D.
    exists D'.
    repeat split.
      apply cong_symmetry.
      assumption.
      apply cong_commutativity.
      eapply (five_segment_with_def C A D B C' A' D' B').
        repeat split; try assumption.
          apply between_symmetry.
          assumption.
          apply cong_commutativity.
          assumption.
          apply cong_symmetry.
          assumption.
        apply cong_commutativity.
        assumption.
      auto.
    eapply l2_11.
      apply between_symmetry.
      apply H0.
      apply H5.
      apply cong_commutativity.
      assumption.
    apply cong_symmetry.
    assumption.
Qed.

Lemma bet_conga__bet :
 forall A B C A' B' C',
  Bet A B C ->
  CongA A B C A' B' C' ->
  Bet A' B' C'.
Proof.
    intros.
    unfold CongA in H0.
    spliter.
    ex_and H4 A0.
    ex_and H5 C0.
    ex_and H4 A1.
    ex_and H5 C1.
    assert(Bet A0 B C0).
      eapply outer_transitivity_between.
        2:apply H6.
        apply between_symmetry.
        eapply outer_transitivity_between.
          2:apply H4.
          apply between_symmetry.
          assumption.
        auto.
      auto.
    assert(Cong_3 A0 B C0 A1 B' C1).
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply between_symmetry.
          apply H4.
          apply H8.
          apply cong_left_commutativity.
          assumption.
        apply cong_symmetry.
        apply cong_right_commutativity.
        assumption.
        assumption.
      apply cong_right_commutativity.
      eapply l2_11.
        apply H6.
        apply between_symmetry.
        apply H10.
        apply cong_symmetry.
        apply cong_left_commutativity.
        assumption.
      apply cong_right_commutativity.
      assumption.
    assert(Bet A1 B' C1).
      eapply l4_6.
        apply H13.
      assumption.
    eapply between_inner_transitivity.
      2:apply H10.
    eapply between_exchange3.
      apply between_symmetry.
      apply H8.
    assumption.
Qed.

Lemma out_in_angle_out :
 forall A B C P,
  Out B A C ->
  InAngle P A B C ->
  Out B A P.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      unfold Out in H.
      spliter.
      induction H5.
        assert (A = B).
          eapply between_equality.
            apply H3.
          assumption.
        contradiction.
      assert (C = B).
        eapply between_equality.
          apply between_symmetry.
          apply H3.
        assumption.
      contradiction.
    unfold Out in H.
    spliter.
    induction H6.
      assert(Bet B A X).
        eapply between_inner_transitivity.
          apply H6.
        assumption.
      unfold Out in H4.
      spliter.
      induction H9.
        assert(Bet B A P).
          eapply between_exchange4.
            apply H7.
          assumption.
        apply bet_out; assumption.
      assert(Bet B A P \/ Bet B P A).
        eapply l5_3.
          apply H7.
        assumption.
      unfold Out.
      repeat split; assumption.
    assert (Bet B X A).
      eapply between_exchange2.
        apply H6.
      apply between_symmetry.
      assumption.
    unfold Out in H4.
    spliter.
    induction H9.
      assert(Bet B A P \/ Bet B P A).
        eapply l5_1.
          2: apply H7.
          auto.
        assumption.
      unfold Out.
      repeat split; try assumption.
    assert(Bet B P A).
      eapply between_exchange4.
        apply H9.
      assumption.
    eapply l6_6.
    apply bet_out; assumption.
Qed.

Lemma in_angle_one_side :
 forall A B C P,
  ~ Col A B C ->
  ~ Col B A P ->
  InAngle P A B C ->
  OS A B P C.
Proof.
    intros.
    unfold InAngle in H1.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      apply False_ind.
      apply H.
      unfold Col.
      left.
      assumption.
    unfold OS.
    prolong C A C' C A.
    exists C'.
    assert(TS A B X C').
      repeat split.
        intro.
        apply H0.
        eapply (col_transitivity_1 _ X).
          intro.
          subst X.
          apply H.
          left.
          assumption.
          eapply (col_transitivity_1 _ A).
            auto.
            apply col_permutation_3.
            assumption.
          apply col_trivial_2.
        apply out_col.
        assumption.
        intro.
        apply H.
        eapply (col_transitivity_1 _  C').
          intro.
          subst C'.
          apply cong_symmetry in H7.
          apply cong_identity in H7.
          subst C.
          apply H.
          apply col_trivial_3.
          apply col_permutation_4.
          assumption.
        unfold Col.
        right; right.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      eapply between_exchange3.
        2: apply H6.
      apply between_symmetry.
      assumption.
    split.
      eapply l9_5.
        apply H8.
        2: apply H5.
      apply col_trivial_3.
    repeat split.
      intro.
      apply H.
      apply col_permutation_1.
      assumption.
      intro.
      apply H.
      eapply (col_transitivity_1 _ C').
        intro.
        subst C'.
        unfold TS in H8.
        spliter.
        apply H10.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      unfold Col.
      right; right.
      assumption.
    exists A.
    split.
      apply col_trivial_1.
    assumption.
Qed.

Lemma inangle_one_side : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q ->
    InAngle P A B C -> InAngle Q A B C ->
    OS A B P Q.
Proof.
    intros.
    unfold InAngle in *.
    spliter.
    ex_and H9 P'.
    ex_and H6 Q'.
    induction H10.
      subst P'.
      apply bet_col in H9.
      contradiction.
    induction H11.
      subst Q'.
      apply bet_col in H6.
      contradiction.
    assert(OS A B P' Q').
      prolong P' A T A C.
      unfold OS.
      exists T.
      unfold TS.
      assert(A <> P').
        intro.
        subst P'.
        apply out_col in H10.
        apply H0.
        Col.
      repeat split; auto.
        intro.
        apply H0.
        assert(P' <> B).
          unfold Out in H10.
          spliter.
          assumption.
        apply out_col in H10.
        ColR.
        intro.
        induction(eq_dec_points A T).
          subst T.
          apply cong_symmetry in H13.
          apply cong_identity in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply bet_col in H9.
        apply bet_col in H12.
        assert(Col T A C).
          ColR.
        eapply (col_transitivity_1 _ T); Col.
        exists A.
        split; Col.
        intro.
        apply H1.
        assert(Q' <> B).
          unfold Out in H11.
          spliter.
          assumption.
        apply out_col in H11.
        ColR.
        intro.
        induction(eq_dec_points A T).
          subst T.
          apply cong_symmetry in H13.
          apply cong_identity in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply bet_col in H9.
        apply bet_col in H12.
        assert(Col T A C).
          ColR.
        eapply (col_transitivity_1 _ T); Col.
      exists A.
      split; Col.
      assert(Bet A P' Q' \/ Bet A Q' P').
        eapply l5_3.
          apply H9.
        assumption.
      induction H15.
        eapply (outer_transitivity_between2 _ P'); Between.
      eapply (between_exchange3 P'); Between.
    assert(OS A B P P').
      eapply (out_one_side_1  _ _ _ _  B); Col.
      apply l6_6.
      auto.
    assert(OS A B Q Q').
      eapply (out_one_side_1  _ _ _ _ B); Col.
      apply l6_6.
      auto.
    eapply one_side_transitivity.
      apply H13.
    apply one_side_symmetry.
    eapply one_side_transitivity.
      apply H14.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma inangle_one_side2 : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q ->
    ~ Col C B P -> ~ Col C B Q ->
    InAngle P A B C -> InAngle Q A B C ->
    OS A B P Q /\ OS C B P Q.
Proof.
    intros.
    split.
      apply (inangle_one_side _ _ C); Col.
    apply (inangle_one_side _ _ A); Col.
      apply l11_24.
      auto.
    apply l11_24.
    auto.
Qed.

Lemma col_conga_col : forall A B C D E F, Col A B C -> CongA A B C D E F -> Col D E F.
Proof.
    intros.
    induction H.
      assert (Bet D E F).
        eapply bet_conga__bet.
          apply H.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert (Out E D F).
        eapply l11_21_a.
          2: apply H0.
        apply bet_out in H.
          apply l6_6.
          assumption.
          unfold CongA in H0.
          spliter.
          assumption.
      unfold Out in H1.
      spliter.
      unfold Col.
      induction H3.
        right; right.
        apply between_symmetry.
        assumption.
      right; left.
      assumption.
    assert (Out E D F).
      eapply l11_21_a.
        2: apply H0.
      apply between_symmetry in H.
      apply bet_out in H.
        assumption.
        unfold CongA in H0.
        spliter.
        assumption.
    unfold Out in H1.
    spliter.
    unfold Col.
    induction H3.
      right; right.
      apply between_symmetry.
      assumption.
    right; left.
    assumption.
Qed.

Lemma ncol_conga_ncol : forall A B C D E F, ~ Col A B C -> CongA A B C D E F -> ~ Col D E F.
Proof.
    intros.
    intro.
    apply H.
    eapply col_conga_col.
      apply H1.
    apply conga_sym.
    assumption.
Qed.

Lemma angle_construction_4 :
 forall A B C A' B' P,
  A <> B -> C <> B -> A' <> B' ->
  exists C', CongA A B C A' B' C' /\ Coplanar A' B' C' P.
Proof.
    intros.
    destruct (col_dec A' B' P).
      destruct (angle_construction_3 A B C A' B') as [C']; auto.
      exists C'; split; Cop.
    destruct (col_dec A B C).
      destruct (angle_construction_3 A B C A' B') as [C']; auto.
      exists C'; split; auto.
      exists C'; left; split; Col.
      apply (col_conga_col A B C); assumption.
    destruct (angle_construction_1 A B C A' B' P) as [C' []]; auto.
    exists C'; split; Cop.
Qed.

Lemma lea_distincts : forall A B C D E F, LeA A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E.
Proof.
  intros A B C D E F Hlea.
  destruct Hlea as [X [HInAngle HConga]].
  destruct HInAngle as [HDE [HEF _]].
  repeat split; auto.
  apply (conga_diff1 A B C D E X); auto.
  apply (conga_diff2 A B C D E X); auto.
Qed.

Lemma gea_distincts : forall A B C D E F, GeA A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E.
Proof.
  intros A B C D E F Hgea.
  apply lea_distincts in Hgea.
  spliter.
  repeat split; auto.
Qed.

Lemma l11_29_a : forall A B C D E F, LeA A B C D E F ->
  exists Q, InAngle C A B Q /\ CongA A B Q D E F.
Proof.
    intros.
    unfold LeA in H.
    ex_and H P.
    assert(E <> D /\ B <> A /\ E <> F /\ E <> P /\ B <> C).
      unfold CongA in *.
      unfold InAngle in H.
      spliter.
      repeat split.
        auto.
        auto.
        auto.
        auto.
      auto.
    spliter.
    assert(A <> B /\ C <> B).
      intuition.
    spliter.
    assert(HH:=or_bet_out A B C).
    induction HH.
      assert(Bet D E P).
        eapply bet_conga__bet.
          apply H8.
        assumption.
      exists C.
      split.
        apply inangle3123; assumption.
      assert(HH:=H).
      unfold InAngle in HH.
      spliter.
      ex_and H13 X.
      induction H14.
        subst X.
        assert(Bet E F P \/ Bet E P F).
          eapply (l5_2 D).
            auto.
            assumption.
          assumption.
        eapply l11_10.
          apply H0.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          assumption.
        repeat split.
          auto.
          auto.
        assumption.
      assert(Out E P F).
        unfold Out in H14.
        spliter.
        induction H16.
          assert( Bet D X P).
            eapply between_exchange2.
              apply H9.
            assumption.
          assert(Bet D E X).
            eapply between_inner_transitivity.
              apply H9.
            assumption.
          assert(Bet D E F).
            eapply between_exchange4.
              apply H18.
            assumption.
          unfold Out.
          repeat split.
            auto.
            auto.
          eapply l5_2.
            2:apply H9.
            auto.
          assumption.
        assert(Bet D P X).
          eapply outer_transitivity_between2.
            apply H9.
            assumption.
          assumption.
        assert(Bet D P F).
          eapply between_exchange4.
            apply H17.
          assumption.
        assert(Bet E P F).
          eapply between_exchange3.
            apply H9.
          assumption.
        repeat split.
          auto.
          auto.
        left.
        assumption.
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        assumption.
      eapply l6_6.
      assumption.
    induction H8.
      assert(exists Q, CongA D E F A B Q).
        apply angle_construction_3.
          auto.
          auto.
        assumption.
      ex_and H9 Q.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold CongA in H10.
          spliter.
          intuition.
          auto.
        (* absurde.
        assumption. *)
        exists A.
        split.
          apply between_trivial2.
        right.
        assumption.
      apply conga_sym.
      assumption.
    assert(D <> E /\ F <> E).
      intuition.
    spliter.
    assert(HH:=or_bet_out D E F).
    induction HH.
      prolong A B Q E F.
      exists Q.
      split.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          auto.
          assumption.
        exists B.
        split.
          assumption.
        left.
        reflexivity.
      eapply conga_line; try assumption.
        intro.
        treat_equalities.
        auto.
    induction H11.
      assert(Out E D P).
        eapply in_angle_out.
          apply H11.
        assumption.
      assert (Out B A C).
        eapply l11_21_a.
          apply H12.
        apply conga_sym.
        assumption.
      apply False_ind.
      apply H8.
      apply out_col in H13.
      Col.
    (************)
    assert(exists Q, CongA D E F A B Q /\ OS A B Q C).
      apply angle_construction_1; assumption.
    ex_and H12 Q.
    exists Q.
    assert(exists DD, Out E D DD /\ Cong E DD B A).
      eapply segment_construction_3; auto.
    ex_and H14 DD.
    assert(exists FF, Out E F FF /\ Cong E FF B Q).
      eapply segment_construction_3.
        auto.
      unfold CongA in H12.
      spliter.
      auto.
    ex_and H16 FF.
    assert(InAngle P DD E FF).
      eapply l11_25.
        apply H.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      apply out_trivial.
      auto.
    assert(HH18:=H18).
    unfold InAngle in H18.
    spliter.
    ex_and H21 X.
    induction H22.
      subst X.
      assert (Bet D E F).
        eapply bet_out_out_bet.
          apply H21.
          apply l6_6.
          assumption.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H11.
      unfold Col.
      left.
      assumption.
    assert(exists CC, Out B C CC /\ Cong B CC E X).
      apply segment_construction_3.
        auto.
      unfold Out in H22.
      spliter.
      auto.
    ex_and H23 CC.
    assert (CongA A B CC DD E X).
      eapply l11_10.
        apply H0.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
        apply l6_6.
        assumption.
      assumption.
    assert(Cong A CC DD X).
      eapply cong2_conga_cong.
        apply H25.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      assumption.
    assert(CongA A B Q DD E FF).
      eapply l11_10.
        apply conga_sym.
        apply H12.
        apply out_trivial.
        auto.
        apply out_trivial.
        intro.
        subst Q.
        apply cong_identity in H17.
        subst FF.
        absurde.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(Cong A Q DD FF).
      eapply cong2_conga_cong.
        apply H27.
        apply cong_symmetry.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(CongA CC B Q X E FF).
      eapply (l11_22b _ _ _ A).
      split.
        apply one_side_symmetry.
        eapply out_out_one_side.
          apply invert_one_side.
          apply H13.
        assumption.
      split.
        assert(InAngle X DD E FF).
          eapply l11_25.
            apply HH18.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        apply in_angle_one_side in H29.
          apply invert_one_side in H29.
          apply H29.
          intro.
          apply H11.
          eapply col_out2_col.
            apply H30.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
        intro.
        apply H8.
        eapply col_conga_col.
          2:apply conga_sym.
          2: apply H0.
        eapply col_out2_col.
          apply col_permutation_4.
          apply H30.
          apply l6_6.
          assumption.
        assumption.
      split.
        apply conga_sym.
        eapply l11_10.
          apply conga_sym.
          apply conga_comm.
          apply H0.
          assumption.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
        apply out_trivial.
        auto.
      assumption.
    assert(Cong CC Q X FF).
      eapply cong2_conga_cong.
        apply H29.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    split.
      assert(InAngle CC A B Q).
        repeat split.
          assumption.
          intro.
          subst Q.
          unfold CongA in H12.
          spliter.
          absurde.
          intro.
          subst CC.
          unfold CongA in H25.
          spliter.
          auto.
        exists CC.
        split.
          eapply l4_6.
            apply H21.
          repeat split.
            cong.
            cong.
          cong.
        right.
        apply out_trivial.
        unfold Out in H23.
        spliter.
        auto.
      eapply l11_25.
        apply H31.
        apply out_trivial.
        auto.
        apply out_trivial.
        unfold CongA in H27.
        spliter.
        auto.
      assumption.
    apply conga_sym.
    assumption.
Qed.

Lemma in_angle_line : forall A B C P, P <> B -> A <> B -> C <> B -> Bet A B C -> InAngle P A B C.
Proof.
    intros.
    repeat split; try assumption.
    exists B.
    split.
      assumption.
    left.
    reflexivity.
Qed.


Lemma l11_29_b : forall A B C D E F, (exists Q, InAngle C A B Q /\ CongA A B Q D E F) ->
  LeA A B C D E F.
Proof.
    intros.
    ex_and H Q.
    unfold LeA.
    assert(HH:=H).
    unfold InAngle in HH.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      assert(exists P, CongA A B C D E P).
        apply angle_construction_3.
          assumption.
          assumption.
        unfold CongA in H0.
        spliter.
        assumption.
      ex_and H5 P.
      exists P.
      split.
        assert(Bet D E F).
          eapply bet_conga__bet.
            apply H4.
          assumption.
        apply in_angle_line.
          unfold CongA in H6.
          spliter.
          assumption.
          unfold CongA in H6.
          spliter.
          assumption.
          unfold CongA in H0.
          spliter.
          assumption.
        assumption.
      assumption.
    assert(exists DD, Out E D DD /\ Cong E DD B A).
      apply segment_construction_3.
        unfold CongA in H0.
        spliter.
        auto.
      auto.
    ex_and H6 DD.
    assert(exists FF, Out E F FF /\ Cong E FF B Q).
      apply segment_construction_3.
        unfold CongA in H0.
        spliter.
        auto.
      auto.
    ex_and H8 FF.
    assert(D <> E /\ DD <> E /\ F <> E /\ FF <> E).
      unfold Out in *.
      spliter.
      repeat split; try assumption.
    spliter.
    assert(HI:=or_bet_out A B C).
    induction HI.
      exists F.
      split.
        apply inangle3123.
          assumption.
        assumption.
      assert(CongA A B C A B Q).
        eapply l11_10.
          apply conga_refl.
            apply H1.
          apply H3.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        unfold Out in H5.
        spliter.
        induction H16.
          assert(Bet A B X).
            eapply between_inner_transitivity.
              apply H14.
            assumption.
          assert(Bet B X Q).
            eapply between_exchange3.
              apply H17.
            assumption.
          assert(Bet B Q C \/ Bet B C Q).
            eapply l5_1.
              2:apply H18.
              auto.
            assumption.
          unfold Out.
          repeat split.
            assumption.
            assumption.
          assumption.
        assert(Bet A B X).
          eapply outer_transitivity_between.
            apply H14.
            assumption.
          auto.
        assert(Bet B X Q).
          eapply between_exchange3.
            apply H17.
          assumption.
        assert(Bet B C Q).
          eapply between_exchange4.
            apply H16.
          assumption.
        unfold Out.
        repeat split.
          assumption.
          assumption.
        right.
        assumption.
      eapply conga_trans.
        apply H15.
      assumption.
    induction H14.
      exists D.
      split.
        apply inangle1123.
          assumption.
        assumption.
      assert(CongA A B C A B A).
        eapply l11_10.
          apply conga_refl.
            apply H1.
          apply H3.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        assumption.
      eapply conga_trans.
        apply H15.
      apply conga_trivial_1.
        assumption.
      assumption.
    assert(HJ:=or_bet_out A B Q).
    induction HJ.
      assert(exists P, CongA A B C D E P).
        apply angle_construction_3.
          assumption.
          assumption.
        unfold Out in H6.
        spliter.
        assumption.
      ex_and H16 P.
      exists P.
      split.
        apply in_angle_line.
          unfold CongA in H17.
          spliter.
          assumption.
          assumption.
          assumption.
        eapply bet_conga__bet.
          apply H15.
        assumption.
      assumption.
    induction H15.
      assert(Out B A C).
        eapply out_in_angle_out.
          apply H15.
        assumption.
      apply False_ind.
      apply H14.
      unfold Out in H16.
      spliter.
      unfold Col.
      induction H18.
        right; right.
        apply between_symmetry.
        assumption.
      right; left.
      assumption.
    assert(exists P, CongA A B C D E P /\ OS D E P F).
      eapply angle_construction_1.
        assumption.
      eapply ncol_conga_ncol.
        apply H15.
      apply H0.
    ex_and H16 P.
    exists P.
    split.
      assert(exists PP, Out E P PP /\ Cong E PP B X).
        eapply segment_construction_3.
          unfold CongA in H16.
          spliter.
          auto.
        unfold Out in H5.
        spliter.
        auto.
      ex_and H18 PP.
      eapply l11_25.
        2:apply H6.
        2:apply H8.
        2:apply H18.
      repeat split.
        assumption.
        assumption.
        unfold Out in H18.
        spliter.
        assumption.
      exists PP.
      split.
        assert(CongA C B Q P E F).
          eapply (l11_22b _ _ _ A).
          split.
            apply invert_one_side.
            eapply in_angle_one_side.
              assumption.
              intro.
              apply H14.
              apply col_permutation_4.
              assumption.
            assumption.
          split.
            apply invert_one_side.
            apply H17.
          split.
            apply conga_comm.
            assumption.
          assumption.
        assert (Cong DD FF A Q).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply conga_sym.
              apply H0.
              apply l6_6.
              assumption.
              apply l6_6.
              assumption.
              apply l6_6.
              apply out_trivial.
              auto.
            apply out_trivial.
            auto.
            apply cong_commutativity.
            assumption.
          assumption.
        assert(Cong A X DD PP).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply H16.
              apply out_trivial.
              auto.
              assumption.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_symmetry.
          assumption.
        assert(Cong X Q PP FF).
          eapply cong2_conga_cong.
            eapply l11_10.
              apply H20.
              assumption.
              apply out_trivial.
              auto.
              apply l6_6.
              assumption.
            apply l6_6.
            assumption.
            apply cong_symmetry.
            apply cong_commutativity.
            assumption.
          apply cong_symmetry.
          assumption.
        eapply l4_6.
          apply H4.
        repeat split.
          assumption.
          apply cong_symmetry.
          assumption.
        assumption.
      right.
      apply out_trivial.
      unfold Out in H15.
      spliter.
      unfold Out in H18.
      spliter.
      auto.
    assumption.
Qed.

Lemma bet_in_angle_bet : forall A B C P, Bet A B P -> InAngle P A B C -> Bet A B C.
Proof.
    intros.
    unfold InAngle in H0.
    spliter.
    ex_and H3 X.
    induction H4.
      subst X.
      assumption.
    unfold Out in H4.
    spliter.
    induction H6.
      assert(Bet A X P).
        eapply between_exchange2.
          apply H.
        assumption.
      assert(Bet A P C \/ Bet A C P).
        eapply (l5_1 _ X).
          intro.
          subst X.
          assert(A = B).
            eapply between_equality.
              apply H.
            assumption.
          contradiction.
          assumption.
        assumption.
      induction H8.
        eapply between_exchange4.
          apply H.
        assumption.
      assert(Bet A B X).
        eapply between_inner_transitivity.
          apply H.
        assumption.
      eapply between_exchange4.
        apply H9.
      assumption.
    assert(Bet A B X).
      eapply outer_transitivity_between.
        apply H.
        assumption.
      auto.
    eapply between_exchange4.
      apply H7.
    assumption.
Qed.

Lemma lea_line : forall A B C P, Bet A B P -> LeA A B P A B C -> Bet A B C.
Proof.
    intros.
    unfold LeA in H0.
    ex_and H0 PP.
    assert (HH:=H0).
    unfold InAngle in H0.
    spliter.
    ex_and H4 X.
    induction H5.
      subst X.
      assumption.
    assert (Bet A B PP).
      eapply bet_conga__bet.
        apply H.
      assumption.
    eapply bet_in_angle_bet.
      apply H6.
    assumption.
Qed.


Lemma eq_conga_out : forall A B D E F, CongA A B A D E F -> Out E D F.
Proof.
    intros.
    assert(HH:=H).
    unfold CongA in H.
    spliter.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H3 D'.
    ex_and H4 F'.
    assert(Cong_3 B A' C' E D' F').
      repeat split.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H3.
          apply between_symmetry.
          apply H7.
          apply cong_right_commutativity.
          apply cong_symmetry.
          assumption.
        apply cong_right_commutativity.
        assumption.
        apply cong_right_commutativity.
        eapply l2_11.
          apply H5.
          apply between_symmetry.
          apply H9.
          apply cong_right_commutativity.
          apply cong_symmetry.
          assumption.
        apply cong_right_commutativity.
        assumption.
      assumption.
    assert(Out E D' F').
      eapply cong3_preserves_out.
        2:apply H12.
      unfold Out.
      repeat split.
        intro.
        subst A'.
        apply between_identity in H3.
        subst A.
        absurde.
        intro.
        subst C'.
        apply between_identity in H5.
        subst A.
        absurde.
      eapply l5_1.
        2:apply H3.
        auto.
      assumption.
    eapply bet2_out_out.
      assumption.
      assumption.
      apply H13.
      assumption.
    assumption.
Qed.

Lemma conga_ex_cong3 : forall A B C A' B' C',
  CongA A B C A' B' C' -> exists AA, exists CC, Out B A AA -> Out B C CC -> Cong_3 AA B CC A' B' C'.
Proof.
    intros.
    assert(B <> A /\ B <> C /\ B' <> A' /\ B' <> C').
      unfold CongA in H.
      spliter.
      repeat split; auto.
    spliter.
    assert(exists AA, Out B A AA /\ Cong B AA B' A').
      apply segment_construction_3; assumption.
    assert(exists CC, Out B C CC /\ Cong B CC B' C').
      apply segment_construction_3; assumption.
    ex_and H4 AA.
    ex_and H5 CC.
    exists AA.
    exists CC.
    intros.
    repeat split.
      apply cong_commutativity.
      assumption.
      eapply cong2_conga_cong.
        eapply l11_10.
          apply H.
          apply l6_6.
          assumption.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        auto.
        Cong.
      assumption.
    assumption.
Qed.

Lemma conga_preserves_in_angle : forall A B C I A' B' C' I',
 CongA A B C A' B' C' -> CongA A B I A' B' I' ->
 InAngle I A B C -> OS A' B' I' C' ->
 InAngle I' A' B' C'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ I <> B /\ I' <> B').
      unfold CongA in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(HH1:= or_bet_out A B C).
    induction HH1.
      assert(Bet A' B' C').
        eapply bet_conga__bet.
          apply H9.
        assumption.
      apply in_angle_line; assumption.
    induction H9.
      assert(Out B A I).
        eapply out_in_angle_out.
          apply H9.
        assumption.
      assert(Out B' A' I').
        eapply l11_21_a.
          apply H10.
        assumption.
      apply out_in_angle.
        eapply l11_21_a.
          apply H9.
        assumption.
      apply l6_6.
      assumption.
    assert(HH2:= or_bet_out A B I).
    induction HH2.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      apply False_ind.
      apply H9.
      unfold Col.
      left.
      assumption.
    induction H10.
      assert(Out B' A' I').
        eapply l11_21_a.
          apply H10.
        assumption.
      eapply col_in_angle; try assumption.
      left.
      assumption.
    (*****************************)
    assert(exists AA', Out B' A' AA' /\ Cong B' AA' B A).
      apply segment_construction_3; auto.
    assert(exists CC', Out B' C' CC' /\ Cong B' CC' B C).
      apply segment_construction_3; auto.
    ex_and H11 AA'.
    ex_and H12 CC'.
    assert(HH:=H1).
    unfold InAngle in H1.
    spliter.
    ex_and H17 J.
    induction H18.
      subst J.
      eapply in_angle_line; try assumption.
      eapply bet_conga__bet.
        apply H17.
      assumption.
    assert(B <> J).
      unfold Out in H18.
      spliter.
      auto.
    assert(~Col A B J).
      intro.
      apply H10.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ J).
        assumption.
        apply out_col.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(exists J', CongA A B J  A' B' J' /\ OS A' B' J' I').
      apply angle_construction_1.
        intro.
        apply H10.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ J).
          unfold Out in H18.
          spliter.
          auto.
          apply out_col.
          assumption.
        apply col_permutation_1.
        assumption.
      eapply ncol_conga_ncol.
        apply H10.
      assumption.
    ex_and H21 J'.
    assert(B' <> J').
      unfold CongA in H21.
      spliter.
      auto.
    assert(exists JJ', Out B' J' JJ' /\ Cong B' JJ' B J).
      apply segment_construction_3.
        assumption.
      assumption.
    ex_and H24 JJ'.
    assert(~Col A' B' J').
      intro.
      apply H20.
      eapply col_conga_col.
        apply H26.
      apply conga_sym.
      assumption.
    assert(A' <> JJ').
      intro.
      subst JJ'.
      apply H20.
      eapply col_conga_col.
        apply out_col in H24.
        apply col_permutation_2.
        apply H24.
      apply conga_sym.
      assumption.
    assert(B' <> JJ').
      unfold Out in H24.
      spliter.
      auto.
    assert(~Col A' B' JJ').
      intro.
      apply H26.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ JJ').
        assumption.
        apply col_permutation_5.
        apply out_col.
        assumption.
      apply col_permutation_1.
      assumption.
    (****************************************************************)
    assert(CongA A B C AA' B' CC').
      eapply l11_10.
        apply H.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
        apply l6_6.
        assumption.
      apply l6_6.
      assumption.
    assert(CongA A' B' J' A' B' JJ').
      eapply l11_10.
        apply conga_refl.
          apply H5.
        3: apply H24.
        auto.
        apply out_trivial.
        auto.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    assert(Out B' I' JJ' \/ TS A' B' I' JJ').
      apply conga_cop__or_out_ts.
      apply coplanar_perm_2, col_cop__cop with J'; Col; Cop.
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      apply conga_sym.
      eapply conga_trans.
        apply conga_sym.
        apply H31.
      eapply conga_trans.
        apply conga_sym.
        apply H21.
      eapply l11_10.
        apply (conga_refl A B I).
          assumption.
        assumption.
        apply out_trivial.
        auto.
        assumption.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    induction H32.
      assert(CongA J B C J' B' C').
        eapply (l11_22b _ _ _ A _ _ _ A').
        split.
          apply invert_one_side.
          apply in_angle_one_side.
            assumption.
            intro.
            apply H10.
            apply col_permutation_2.
            eapply (col_transitivity_1 _ J).
              assumption.
              apply out_col.
              assumption.
            apply col_permutation_5.
            assumption.
          eapply l11_25.
            apply HH.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
          assumption.
        split.
          eapply one_side_transitivity.
            2:apply invert_one_side.
            2:apply H2.
          apply invert_one_side.
          assumption.
        split.
          apply conga_comm.
          assumption.
        assumption.
      assert(Cong A C AA' CC').
        eapply cong2_conga_cong.
          eapply l11_10.
            apply H.
            apply out_trivial.
            auto.
            apply out_trivial.
            auto.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Cong A J AA' JJ').
        eapply cong2_conga_cong.
          eapply l11_10.
            apply H0.
            apply out_trivial.
            auto.
            assumption.
            apply l6_6.
            assumption.
          apply l6_6.
          assumption.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(CongA J' B' C' JJ' B' CC').
        eapply l11_10.
          apply conga_refl.
            4:apply H12.
          3:apply H24.
          auto.
          unfold CongA in H30.
          spliter.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        unfold CongA in H30.
        spliter.
        auto.
      assert(Cong J C JJ' CC').
        eapply (cong2_conga_cong).
          eapply conga_trans.
            apply H33.
          apply H36.
          apply cong_symmetry.
          apply cong_commutativity.
          assumption.
        apply cong_symmetry.
        assumption.
      assert(Bet AA' JJ' CC').
        eapply l4_6.
          apply H17.
        repeat split.
          assumption.
          assumption.
        assumption.
      eapply l11_25.
        2: apply H11.
        2: apply H12.
        unfold InAngle.
        repeat split; try assumption.
          unfold Out in H11.
          spliter.
          assumption.
          unfold Out in H12.
          spliter.
          assumption.
          3:apply H32.
        auto.
      exists JJ'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(OS B' A' I' JJ').
      eapply out_out_one_side.
        apply invert_one_side.
        apply one_side_symmetry.
        apply H22.
      assumption.
    apply invert_two_sides in H32.
    apply l9_9 in H32.
    contradiction.
Qed.

Lemma l11_30 : forall A B C D E F A' B' C' D' E' F',
 LeA A B C D E F ->
 CongA A B C A' B' C' ->
 CongA D E F D' E' F' ->
 LeA A' B' C' D' E' F'.
Proof.
    intros.
    assert(HH:=H).
    apply l11_29_a in H.
    ex_and H Q.
    apply l11_29_b.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B' /\ D <> E /\ F <> E /\ D' <> E' /\ F' <> E').
      unfold CongA in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(Hi:=or_bet_out A' B' C').
    induction Hi.
      prolong A' B' Q' A' B'.
      exists Q'.
      assert(B' <> Q').
        intro.
        subst Q'.
        apply cong_symmetry in H13.
        apply cong_identity in H13.
        contradiction.
      assert(A' <> Q').
        intro.
        subst Q'.
        apply between_identity in H12.
        contradiction.
      assert(CongA A' B' Q' A' B' C').
        apply conga_line; try assumption.
          auto.
      split.
        apply in_angle_line; try assumption.
        auto.
      assert(Bet A B C).
        eapply bet_conga__bet.
          apply H11.
        apply conga_sym.
        assumption.
      assert(Bet A B Q).
        eapply lea_line.
          apply H17.
        apply l11_29_b.
        exists Q.
        split.
          assumption.
        apply conga_refl.
          assumption.
        unfold CongA in H2.
        spliter.
        assumption.
      assert(Bet D E F).
        eapply bet_conga__bet.
          apply H18.
        assumption.
      assert (Bet D' E' F').
        eapply bet_conga__bet.
          apply H19.
        assumption.
      eapply conga_line; try assumption.
        auto.
    (************************)
    induction H11.
      assert(exists Q', CongA D' E' F' A' B' Q').
        eapply angle_construction_3; assumption.
      ex_and H12 Q'.
      exists Q'.
      split.
        apply col_in_angle; try assumption.
          unfold CongA in H13.
          spliter.
          assumption.
        left.
        assumption.
      apply conga_sym.
      assumption.
    assert(Hi:=or_bet_out D' E' F').
    induction Hi.
      assert(exists Q', CongA  D' E' F' A' B' Q').
        eapply angle_construction_3; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(Bet A' B' Q').
        eapply bet_conga__bet.
          apply H12.
        assumption.
      split.
        apply in_angle_line; try assumption.
        unfold CongA in H14.
        spliter.
        assumption.
      apply conga_sym.
      assumption.
    induction H12.
      assert(exists Q', CongA  D' E' F' A' B' Q').
        eapply angle_construction_3; try assumption.
      ex_and H13 Q'.
      exists Q'.
      assert(Out B' A' Q').
        eapply l11_21_a.
          apply H12.
        assumption.
      assert(CongA A B Q D' E' F').
        eapply conga_trans.
          apply H2.
        assumption.
      assert(Out B A Q).
        eapply l11_21_a.
          apply H12.
        apply conga_sym.
        assumption.
      assert(Out B A C).
        eapply out_in_angle_out.
          apply H16.
        assumption.
      assert(Out  B' A' C').
        eapply l11_21_a.
          apply H17.
        assumption.
      split.
        eapply out_in_angle.
          assumption.
        apply l6_6.
        assumption.
      apply conga_sym.
      assumption.
    assert(exists QQ, CongA D' E' F' A' B' QQ /\ OS A' B' QQ C').
      eapply angle_construction_1.
        assumption.
      assumption.
    ex_and H13 Q'.
    exists Q'.
    split.
      eapply conga_preserves_in_angle.
        3: apply H.
        eapply conga_trans.
          apply H2.
        eapply conga_trans.
          apply H1.
        assumption.
        apply H0.
      (************** etrange ****************)
      try assumption.
      apply one_side_symmetry.
      assumption.
    apply conga_sym.
    assumption.
Qed.

Lemma l11_31_1 : forall A B C D E F,
 Out B A C -> D <> E -> F <> E ->
 LeA A B C D E F.
Proof.
    intros.
    unfold LeA.
    exists D.
    split.
      apply inangle1123; assumption.
    apply l11_21_b.
      assumption.
    apply out_trivial.
    auto.
Qed.

Lemma l11_31_2 : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 Bet D E F ->
 LeA A B C D E F.
Proof.
intros; destruct (angle_construction_3 A B C D E) as [P HCongA]; auto.
exists P; split; try apply in_angle_line; unfold CongA in *; spliter; auto.
Qed.

Lemma lea_refl : forall A B C,
 A <> B -> C <> B -> LeA A B C A B C.
Proof.
    intros.
    unfold LeA.
    exists C .
    split.
      apply inangle3123; assumption.
    apply conga_refl; assumption.
Qed.

Lemma conga__lea : forall A B C D E F,
 CongA A B C D E F -> LeA A B C D E F.
Proof.
    intros.
    unfold LeA.
    exists F.
    split.
      apply inangle3123.
        apply (conga_diff45 A B C D E F); assumption.
        apply (conga_diff56 A B C D); assumption.
    assumption.
Qed.

Lemma conga__lea456123 : forall A B C D E F,
 CongA A B C D E F -> LeA D E F A B C.
Proof.
    intros; apply conga__lea, conga_sym; trivial.
Qed.

Lemma lea_out4__lea : forall A B C D E F A' C' D' F',
 LeA A B C D E F -> Out B A A' -> Out B C C' -> Out E D D' -> Out E F F' ->
 LeA A' B C' D' E F'.
Proof.
    intros A B C D E F A' C' D' F' Hl HA HC HD HF.
    apply (l11_30 A B C D E F); trivial; apply out2__conga; apply l6_6; assumption.
Qed.

Lemma lea121345 : forall A B C D E, A<>B -> C<>D -> D<>E -> LeA A B A C D E.
Proof.
  intros A B C D E HAB HCD HDE.
  apply l11_31_1; try (apply out_trivial); auto.
Qed.

Lemma inangle__lea : forall A B C P, InAngle P A B C -> LeA A B P A B C.
Proof.
  intros A B C P HIn.
  exists P; split; trivial.
  unfold InAngle in HIn; spliter.
  apply conga_refl; auto.
Qed.

Lemma in_angle_trans : forall A B C D E,
 InAngle C A B D -> InAngle D A B E -> InAngle C A B E.
Proof.
    intros.
    assert(HA1 :=H).
    assert(HA2:= H0).
    unfold InAngle in H.
    unfold InAngle in H0.
    spliter.
    ex_and H3 DD.
    ex_and H6 CC.
    induction H8; induction H7.
      subst CC.
      subst DD.
      apply in_angle_line; assumption.
      subst CC.
      assert(Bet A B E).
        eapply bet_in_angle_bet.
          apply H6.
        assumption.
      apply in_angle_line; assumption.
      subst DD.
      apply in_angle_line; assumption.
    assert(InAngle C A B DD).
      eapply l11_25.
        apply HA1.
        apply out_trivial.
        auto.
        assumption.
      apply out_trivial.
      auto.
    unfold InAngle in H9.
    spliter.
    ex_and H12 CC'.
    induction H13.
      subst CC'.
      assert(Bet A B E).
        eapply between_exchange4.
          apply H12.
        assumption.
      apply in_angle_line; assumption.
    eapply l11_25.
      4: apply l6_6.
      4:apply H13.
      2: apply out_trivial.
      3: apply out_trivial.
      unfold InAngle.
      repeat split; try assumption.
        unfold Out in H13.
        spliter.
        assumption.
      exists CC'.
      split.
        eapply between_exchange4.
          apply H12.
        assumption.
      right.
      apply out_trivial.
      unfold Out in H13.
      spliter.
      auto.
      auto.
    auto.
Qed.

Lemma lea_trans : forall A B C A1 B1 C1 A2 B2 C2,
 LeA A B C A1 B1 C1 ->
 LeA A1 B1 C1 A2 B2 C2 ->
 LeA A B C A2 B2 C2.
Proof.
    intros.
    assert(Hlea1 := H).
    assert (Hlea2 := H0).
    unfold LeA in H.
    unfold LeA in H0.
    ex_and H P1.
    ex_and H0 P2.
    assert( A <> B /\ C <> B /\ A1 <> B1 /\ C1 <> B1 /\ A2 <> B2 /\ C2 <> B2).
      unfold CongA in *.
      unfold InAngle in H0.
      spliter.
      repeat split; assumption.
    spliter.
    assert(HH1 := or_bet_out A B C).
    induction HH1.
      assert(Bet A1 B1 P1).
        eapply bet_conga__bet.
          apply H9.
        assumption.
      assert(Bet A1 B1 C1).
        eapply bet_in_angle_bet.
          apply H10.
        assumption.
      assert(Bet A2 B2 P2).
        eapply bet_conga__bet.
          apply H11.
        assumption.
      assert(Bet A2 B2 C2).
        eapply bet_in_angle_bet.
          apply H12.
        assumption.
      apply l11_31_2; assumption.
    induction H9.
      apply l11_31_1; assumption.
    assert(HH2 := or_bet_out A2 B2 C2).
    induction HH2.
      apply l11_31_2; assumption.
    induction H10.
      assert(Out B2 A2 P2).
        eapply in_angle_out.
          apply H10.
        assumption.
      assert(Out B1 A1 C1).
        eapply l11_21_a.
          apply H11.
        apply conga_sym.
        assumption.
      assert(Out B1 A1 P1).
        eapply in_angle_out.
          apply H12.
        assumption.
      assert(Out B A C).
        eapply l11_21_a.
          apply H13.
        apply conga_sym.
        assumption.
      apply l11_31_1; assumption.
    assert(exists P, CongA A B C A2 B2 P /\ OS A2 B2 P C2).
      apply angle_construction_1; assumption.
    ex_and H11 P.
    assert (OS A2 B2 P2 C2).
      apply in_angle_one_side.
        assumption.
        assert (B2 <> A2).
          auto.
        assert(P2 <> A2).
          intro.
          subst P2.
          assert(Out B1 A1 C1).
            eapply l11_21_a.
              2: apply conga_sym.
              2:apply H2.
            apply out_trivial.
            assumption.
          assert(Out B1 A1 P1).
            eapply out_in_angle_out.
              apply H14.
            assumption.
          assert(Out B A C).
            eapply l11_21_a.
              apply H15.
            apply conga_sym.
            assumption.
          apply H9.
          apply out_col in H16.
          apply col_permutation_4.
          assumption.
        assert(HH:=or_bet_out A2 B2 P2 ).
        induction HH.
          assert (Bet A2 B2 C2).
            eapply bet_in_angle_bet.
              apply H15.
            apply H0.
          intro.
          apply H10.
          unfold Col.
          left.
          assumption.
          induction H15.
            assert(Out B1 A1 C1).
              eapply l11_21_a.
                apply H15.
              apply conga_sym.
              assumption.
            assert( Out B1 A1 P1).
              eapply in_angle_out.
                apply H16.
              assumption.
            assert (Out B A C).
              eapply l11_21_a.
                apply H17.
              apply conga_sym.
              assumption.
            apply False_ind.
            apply H9.
            apply out_col in H18.
            apply col_permutation_4.
            assumption.
          intro.
          apply H15.
          apply col_permutation_4.
          assumption.
          assumption.
        unfold CongA in H2.
    assert(OS A2 B2 P P2).
      eapply one_side_transitivity.
        apply H12; eapply l11_21_a.
      apply one_side_symmetry.
      assumption.
    unfold LeA.
    exists P.
    split.
      eapply (in_angle_trans _ _ _ P2).
        eapply conga_preserves_in_angle.
          apply H2.
          2: apply H.
          eapply conga_trans.
            apply conga_sym.
            apply H1.
          assumption.
        assumption.
      assumption.
    assumption.
Qed.


Lemma in_angle_asym : forall A B C D,
 InAngle D A B C -> InAngle C A B D -> CongA A B C A B D.
Proof.
    intros.
    unfold InAngle in *.
    spliter.
    ex_and H3 CC.
    ex_and H6 DD.
    induction H7; induction H8.
      subst DD.
      subst CC.
      apply conga_line; try assumption.
        auto.
        auto.
      subst CC.
      unfold Out in H8.
      spliter.
      induction H9.
        assert(Bet A B C).
          eapply between_exchange4.
            2: apply H6.
          eapply between_inner_transitivity.
            apply H3.
          assumption.
        apply conga_line; try assumption.
          auto.
          auto.
      assert(Bet A B C).
        eapply between_exchange4.
          eapply outer_transitivity_between.
            apply H3.
            apply H9.
          auto.
        assumption.
        apply conga_line; try assumption.
          auto.
          auto.
      subst DD.
      assert(Bet A B D).
        unfold Out in H7.
        spliter.
        induction H9.
          eapply between_exchange4.
            eapply between_inner_transitivity.
              apply H6.
            apply H9.
          assumption.
        eapply between_exchange4.
          eapply outer_transitivity_between.
            apply H6.
            apply H9.
          auto.
        assumption.
        apply conga_line; try assumption.
          auto.
          auto.
    assert(exists B', Bet CC B' C /\ Bet DD B' D).
      eapply inner_pasch.
        apply between_symmetry.
        apply H3.
      apply between_symmetry.
      assumption.
    ex_and H9 X.
    assert (Out B X C).
      eapply out_bet_out_2.
        apply H7.
      assumption.
    assert(Out B X D).
      eapply out_bet_out_2.
        apply H8.
      assumption.
    assert (Out B C D).
      eapply out2_out_1.
        apply H11.
      assumption.
    eapply l11_10.
      apply conga_refl.
        4:apply H13.
      3: apply out_trivial.
      assumption.
      assumption; apply H7.
      auto.
      apply out_trivial.
      auto.
    apply out_trivial.
    auto.
Qed.

Lemma lea_asym : forall A B C D E F,
 LeA A B C D E F -> LeA D E F A B C -> CongA A B C D E F.
Proof.
    intros.
    induction (col_dec A B C).
      induction (bet_dec A B C).
        apply lea_distincts in H0; spliter.
        apply conga_line; auto.
        ex_and H P.
        apply bet_in_angle_bet with P; trivial.
        apply (bet_conga__bet A B C); assumption.
      apply not_bet_out in H2; trivial.
      apply l11_21_b; trivial.
      ex_and H0 P.
      apply (l11_21_a A B P).
        apply out_in_angle_out with C; assumption.
      apply conga_sym; assumption.
    apply l11_29_a in H.
    unfold LeA in *.
    ex_and H Q.
    ex_and H0 P.
    assert(A <> B /\ Q <> B /\ P <> B /\ D <> E /\ F <> E).
      unfold CongA in *.
      spliter.
      repeat split; assumption.
    spliter.
    assert(CongA A B Q A B P).
      eapply conga_trans.
        apply H2.
      assumption.
    assert(HH1:= or_bet_out A B Q).
    induction HH1.
      assert(Bet A B P).
        eapply bet_conga__bet.
          apply H10.
        assumption.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H11.
        assumption.
      assert(Bet D E F).
        eapply bet_conga__bet.
          apply H10.
        assumption.
      eapply conga_line; try assumption.
        unfold InAngle in H0.
        spliter.
        auto.
        auto.
    induction H10.
      assert(Out E D F).
        eapply l11_21_a.
          apply H10.
        assumption.
      assert(Out B A P).
        eapply l11_21_a.
          apply H11.
        apply H3.
      assert(Out B A C).
        eapply in_angle_out.
          apply H10.
        assumption.
      eapply l11_21_b.
        assumption.
      assumption.
    assert(HH2:= or_bet_out A B P).
    induction HH2.
      assert(Bet A B C).
        eapply bet_in_angle_bet.
          apply H11.
        assumption.
      assert(Bet D E F).
        eapply bet_conga__bet.
          apply H11.
        apply conga_sym.
        assumption.
      apply conga_line; try assumption.
        unfold InAngle in H0.
        spliter.
        auto.
        auto.
    induction H11.
      assert(Out B A Q).
        eapply l11_21_a.
          apply H11.
        apply conga_sym.
        assumption.
      assert (Out B A C).
        eapply in_angle_out.
          apply H12.
        assumption.
      assert(Out E D F).
        eapply l11_21_a.
          apply H12.
        assumption.
      apply l11_21_b.
        assumption.
      assumption.
    assert(Out B P Q \/ TS A B P Q).
      apply conga_cop__or_out_ts.
      apply coplanar_trans_1 with C; Cop; Col.
      apply conga_sym.
      assumption.
    induction H12.
      assert(InAngle C A B P).
        eapply l11_25.
          3: apply H12.
          apply H.
          apply out_trivial.
          auto.
        apply out_trivial.
        intro.
        subst C.
        unfold InAngle in H0.
        spliter.
        absurde.
      assert(CongA A B C A B P).
        apply in_angle_asym; assumption.
      eapply conga_trans.
        apply H14.
      eapply conga_trans.
        apply conga_sym.
        apply H9.
      assumption.
    assert(C <> B).
      unfold InAngle in H0.
      spliter.
      assumption.
    assert(HH:=or_bet_out A B C).
    induction HH.
      assert(Bet A B Q).
        eapply bet_in_angle_bet.
          apply H14.
        apply H.
      apply False_ind.
      apply H10.
      unfold Col.
      left.
      assumption.
    induction H14.
      assert(Out B A P).
        eapply in_angle_out.
          apply H14.
        assumption.
      apply False_ind.
      apply H11.
      apply out_col in H15.
      apply col_permutation_4.
      assumption.
    apply in_angle_one_side in H.
      apply in_angle_one_side in H0.
        assert(OS A B P Q).
          eapply one_side_transitivity.
            apply H0.
          assumption.
        apply l9_9 in H15.
          contradiction.
        assumption.
        assumption.
      intro.
      apply H11.
      apply col_permutation_4.
      assumption.
      assumption.
    intro.
    apply H14.
    apply col_permutation_4.
    assumption.
Qed.

Lemma col_lta__bet : forall A B C X Y Z, Col X Y Z -> LtA A B C X Y Z -> Bet X Y Z.
Proof.
    intros.
    destruct H0.
    assert (Hd := H0).
    apply not_out_bet.
      assumption.
    intro.
    apply H1.
    apply lea_asym.
      assumption.
    apply lea_distincts in H0.
    spliter.
    apply l11_31_1; auto.
Qed.

Lemma col_lta__out : forall A B C X Y Z, Col A B C -> LtA A B C X Y Z -> Out B A C.
Proof.
    intros.
    apply not_bet_out.
      assumption.
    intro.
    destruct H0.
    apply H2.
    apply lea_asym.
      assumption.
    apply lea_distincts in H0.
    spliter.
    apply l11_31_2; auto.
Qed.

Lemma lta_distincts : forall A B C D E F, LtA A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E /\ D <> F.
Proof.
  intros A B C D E F Hlta.
  assert (Hlea : LeA A B C D E F) by (destruct Hlta; assumption).
  apply lea_distincts in Hlea.
  spliter.
  repeat split; auto.
  intro.
  subst F.
  assert (Bet D E D) by (apply (col_lta__bet A B C); Col).
  treat_equalities; auto.
Qed.

Lemma gta_distincts : forall A B C D E F, GtA A B C D E F ->
   A<>B /\ C<>B /\ D<>E /\ F<>E /\ A <> C.
Proof.
  intros A B C D E F Hgta.
  apply lta_distincts in Hgta.
  spliter.
  repeat split; auto.
Qed.

Lemma acute_distincts : forall A B C, Acute A B C -> A<>B /\ C<>B.
Proof.
  intros A B C Hacute.
  destruct Hacute as [x [y [z [HPer Hlta]]]].
  apply lta_distincts in Hlta.
  spliter.
  split; auto.
Qed.

Lemma obtuse_distincts : forall A B C, Obtuse A B C -> A<>B /\ C<>B /\ A <> C.
Proof.
  intros A B C Hobtuse.
  destruct Hobtuse as [x [y [z [HPer Hgta]]]].
  apply gta_distincts in Hgta.
  spliter.
  split; auto.
Qed.

Lemma two_sides_in_angle : forall A B C P P',
 B <> P' ->
 TS B P A C ->
 Bet P B P' ->
 InAngle P A B C \/ InAngle P' A B C.
Proof.
    intros.
    unfold TS in H0.
    spliter.
    ex_and H3 T.
    assert(A <> B).
      intro.
      subst A.
      apply H0.
      apply col_trivial_1.
    assert(C <> B).
      intro.
      subst C.
      apply H2.
      apply col_trivial_1.
    induction (eq_dec_points B T).
      subst T.
      left.
      repeat split.
        assumption.
        assumption.
        intro.
        subst B.
        Col.
      exists B.
      split.
        assumption.
      left.
      reflexivity.
    assert(P <> B /\ T <> B).
      split.
        intro.
        subst B.
        Col.
      auto.
    spliter.
    assert(HH:= or_bet_out P B T).
    induction HH.
      right.
      unfold InAngle.
      repeat split; try assumption.
        unfold Out in H1.
        spliter.
        auto.
      exists T.
      split.
        assumption.
      right.
      unfold Out.
      repeat split.
        auto.
        auto.
      eapply l5_2.
        2:apply H10.
        auto.
      assumption.
    induction H10.
      left.
      unfold InAngle.
      repeat split; try assumption.
      auto.
      exists T.
      split.
        assumption.
      right.
      apply l6_6.
      assumption.
    apply col_permutation_3 in H3.
    contradiction.
Qed.

Lemma in_angle_reverse :
 forall A B A' C D,
  A' <> B ->
  Bet A B A' ->
  InAngle C A B D ->
  InAngle D A' B C.
Proof.
    intros.
    assert (Hd := H1).
    apply inangle_distincts in Hd.
    spliter.
    induction (col_dec B A C).
      assert(HH:=or_bet_out C B A).
      induction HH.
        assert(Bet A B D).
          eapply bet_in_angle_bet.
            apply between_symmetry.
            apply H6.
          assumption.
        assert(Out B A' C).
          repeat split; try assumption.
          eapply l5_2.
            apply H2.
            assumption.
          apply between_symmetry.
          assumption.
        assert( Out B D A').
          repeat split; try assumption.
          eapply l5_2.
            apply H2.
            assumption.
          assumption.
        apply out_in_angle.
          assumption.
        assumption.
      induction H6.
        repeat split; try assumption.
        exists B.
        split.
          unfold Out in H6.
          spliter.
          induction H8.
            eapply between_inner_transitivity.
              apply between_symmetry.
              apply H0.
            assumption.
          eapply outer_transitivity_between.
            apply between_symmetry.
            apply H0.
            assumption.
          auto.
        left.
        reflexivity.
      apply False_ind.
      apply H6.
      apply col_permutation_2.
      assumption.
    induction (col_dec B D C).
      assert(HH:=or_bet_out C B D).
      induction HH.
        assert(OS A B C D).
          apply in_angle_one_side.
            intro.
            apply H5.
            eapply (col_transitivity_1 _ D).
              auto.
              apply col_permutation_1.
              assumption.
            assumption.
            assumption.
          assumption.
        assert(TS A B C D).
          repeat split; try assumption.
            intro.
            apply H5.
            apply col_permutation_3.
            assumption.
            intro.
            apply H5.
            eapply (col_transitivity_1 _ D).
              auto.
              apply col_permutation_2.
              assumption.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          assumption.
        apply l9_9 in H9.
        contradiction.
      induction H7.
        assert(InAngle C A' B C).
          apply inangle3123; assumption.
        eapply l11_25.
          apply H8.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        apply l6_6.
        assumption.
      apply False_ind.
      apply H7.
      apply col_permutation_2.
      assumption.
    assert( HH:= H1).
    apply in_angle_two_sides in HH.
      assert(HH1:=H1).
      unfold InAngle in H1.
      spliter.
      ex_and H9 X.
      induction H10.
        subst X.
        apply col_in_angle; try assumption.
        left.
        repeat split; try assumption.
        eapply l5_2.
          apply H1.
          assumption.
        assumption.
      assert(HH0:= HH).
      unfold TS in HH.
      assert (C <> B).
        spliter.
        intro.
        subst B.
        Col.
      spliter.
      assert(OS D B C A).
        apply in_angle_one_side.
          intro.
          apply H12.
          apply col_permutation_1.
          eapply (col_transitivity_1 _ X).
            unfold Out in H10.
            spliter.
            auto.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ D).
              intro.
              subst D.
              apply between_identity in H9.
              subst X.
              ex_and H14 T.
              apply between_identity in H14.
              subst T.
              contradiction.
              apply col_permutation_2.
              assumption.
            apply col_permutation_5.
            apply bet_col.
            assumption.
          apply out_col.
          assumption.
          intro.
          apply H13.
          apply col_permutation_1.
          assumption.
        apply l11_24.
        assumption.
      assert(~Col A D B).
        intro.
        apply H12.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ X).
          unfold Out in H10.
          spliter.
          auto.
          apply col_permutation_1.
          eapply (col_transitivity_1 _ D).
            intro.
            subst D.
            apply between_identity in H9.
            subst X.
            apply H13.
            apply col_permutation_1.
            apply out_col.
            assumption.
            assumption.
          apply col_permutation_5.
          apply bet_col.
          assumption.
        apply out_col.
        assumption.
      assert(~Col A' D B).
        intro.
        apply H16.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ A').
          auto.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_2.
        assumption.
      assert(TS D B A A').
        repeat split; try assumption.
        exists B.
        split.
          apply col_trivial_3.
        assumption.
      assert(TS D B C A' ).
        eapply l9_8_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      unfold TS in H19.
      assert (~ Col C D B).
        spliter.
        assumption.
      spliter.
      ex_and H22 Y.
      repeat split; try assumption.
      exists Y.
      split.
        apply between_symmetry.
        assumption.
      right.
      apply col_permutation_1 in H22.
      unfold Col in H22.
      induction H22.
        assert(OS C B A' Y).
          apply out_one_side.
            left.
            intro.
            apply H12.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ A').
              auto.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply col_permutation_1.
            assumption.
          apply l6_6.
          apply bet_out.
            intro.
            subst Y.
            apply H13.
            apply col_permutation_5.
            apply bet_col.
            assumption.
          assumption.
        assert(TS C B Y D).
          repeat split.
            intro.
            apply H20.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ Y).
              intro.
              subst Y.
              unfold OS in H24.
              ex_and H24 C0.
              unfold TS in H26.
              spliter.
              apply H26.
              apply col_trivial_3.
              apply col_permutation_2.
              assumption.
            apply col_permutation_1.
            apply bet_col.
            assumption.
            intro.
            apply H20.
            apply col_permutation_4.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          apply between_symmetry.
          assumption.
        assert(TS C B A A').
          repeat split; try assumption.
            intro.
            apply H12.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ A').
              auto.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply col_permutation_2.
            assumption.
          exists B.
          split.
            apply col_trivial_3.
          assumption.
        assert(TS C B Y A).
          eapply l9_8_2.
            apply l9_2.
            apply H26.
          assumption.
        assert(OS C B A D).
          eapply l9_8_1.
            apply l9_2.
            apply H27.
          apply l9_2.
          assumption.
        apply l9_9 in HH0.
        contradiction.
      repeat split.
        intro.
        subst Y.
        apply H12.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ A').
          auto.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
        assumption.
      induction H22.
        left.
        assumption.
      right.
      apply between_symmetry.
      assumption.
      intro.
      apply H5.
      assumption.
    assumption.
Qed.

Lemma in_angle_trans2 : forall A B C D E, InAngle C A B D -> InAngle D A B E -> InAngle D C B E.
Proof.
  intros A B C D E HC HD.
  destruct (segment_construction E B E B) as [E' [HE1 HE2]].
  assert (Hd := HD).
  apply inangle_distincts in Hd.
  spliter; assert_diffs.
  apply l11_24, in_angle_reverse with E'; Between.
  apply l11_24, in_angle_trans with A; apply l11_24; trivial.
  apply in_angle_reverse with E; auto.
  apply l11_24; trivial.
Qed.

Lemma l11_36 : forall A B C D E F A' D',
 A <> B -> A' <> B -> D <> E -> D' <> E ->
 Bet A B A' -> Bet D E D' ->
 (LeA A B C D E F <-> LeA D' E F A' B C).
Proof.
    intros.
    split.
      intro.
      assert(HH:=H5).
      apply l11_29_a in H5.
      unfold LeA.
      ex_and H5 P.
      exists P.
      split.
        eapply (in_angle_reverse A); try assumption.
      eapply l11_13.
        apply conga_sym.
        apply H6.
        assumption.
        assumption.
        assumption.
      assumption.
    intro.
    assert(HH:=H5).
    unfold LeA in H5.
    apply l11_29_b.
    ex_and H5 P.
    exists P.
    split.
      eapply (in_angle_reverse A'); try assumption.
      apply between_symmetry.
      assumption.
    eapply l11_13.
      apply conga_sym.
      apply H6.
      apply between_symmetry.
      assumption.
      assumption.
      apply between_symmetry.
      assumption.
    assumption.
Qed.

Lemma l11_41_aux : forall A B C D,
 ~ Col A B C ->
 Bet B A D ->
 A <> D ->
 LtA A C B C A D.
Proof.
    intros.
    assert(exists M , Midpoint M A C).
      apply midpoint_existence.
    ex_and H2 M.
    double B M P.
    assert(Cong_3 A C B C A P).
      repeat split.
        apply cong_pseudo_reflexivity.
        eapply l7_13.
          apply l7_2.
          apply H3.
        apply l7_2.
        assumption.
      eapply l7_13.
        apply H3.
      apply l7_2.
      assumption.
    assert(A <> C).
      intro.
      subst C.
      apply H.
      apply col_trivial_3.
    assert(B <> C).
      intro.
      subst C.
      apply H.
      apply col_trivial_2.
    assert(C <> D).
      intro.
      subst C.
      apply H.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(A <> M).
      intro.
      subst M.
      apply is_midpoint_id in H3.
      contradiction.
    assert(CongA A C B C A P).
      apply cong3_conga; assumption.
    assert(exists X, Bet A X P /\ Bet M X D).
      eapply inner_pasch.
        apply between_symmetry.
        apply H0.
      apply midpoint_bet.
      apply l7_2.
      assumption.
    ex_and H10 X.
    split.
      unfold LeA.
      exists P.
      split.
        assert(InAngle P M A D).
          repeat split.
            auto.
            auto.
            intro.
            subst P.
            unfold CongA in H9.
            spliter.
            absurde.
          exists X.
          split.
            assumption.
          right.
          apply bet_out.
            intro.
            subst X.
            apply H.
            eapply (col_transitivity_1 _ M).
              assumption.
              eapply (col_transitivity_1 _ D).
                assumption.
                apply col_permutation_1.
                apply bet_col.
                assumption.
              apply col_permutation_1.
              apply bet_col.
              assumption.
            apply bet_col.
            apply midpoint_bet.
            assumption.
          assumption.
        eapply l11_25.
          apply H12.
          apply l6_6.
          apply bet_out.
            auto.
            auto.
          apply midpoint_bet.
          assumption.
          apply out_trivial.
          auto.
        apply out_trivial.
        unfold CongA in H9.
        spliter.
        auto.
      assumption.
    intro.
    assert(CongA C A D C A P).
      eapply conga_trans.
        apply conga_sym.
        apply H12.
      assumption.
    assert (Coplanar C A D P).
      assert_diffs.
      apply coplanar_perm_3, col_cop__cop with B; Col.
      exists M.
      right.
      left.
      split; Col.
    apply conga_cop__or_out_ts in H13; trivial.
    induction H13.
      apply H.
      assert(Col B A P).
        apply col_permutation_2.
        eapply (col_transitivity_1 _ D).
          assumption.
          apply out_col.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      assert(B <> P).
        intro.
        subst P.
        apply l7_3 in H2.
        subst M.
        apply H.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      assert(Col M B A).
        apply col_permutation_2.
        eapply (col_transitivity_1 _ P).
          assumption.
          apply col_permutation_5.
          assumption.
        apply col_permutation_5.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      eapply col_transitivity_1.
        apply H8.
        apply col_permutation_2.
        assumption.
      apply bet_col.
      apply midpoint_bet.
      assumption.
    assert(TS A C B P).
      repeat split.
        intro.
        apply H.
        apply col_permutation_4.
        assumption.
        intro.
        apply H.
        assert(Col M C P).
          apply col_permutation_2.
          eapply (col_transitivity_1 _ A).
            auto.
            apply col_permutation_3.
            assumption.
          apply col_permutation_2.
          apply bet_col.
          apply midpoint_bet.
          assumption.
        assert(Col M B C).
          eapply (col_transitivity_1 _ P).
            intro.
            subst M.
            apply l7_2 in H2.
            apply is_midpoint_id in H2.
            subst P.
            apply H.
            apply col_permutation_4.
            assumption.
            apply col_permutation_1.
            apply bet_col.
            apply midpoint_bet.
            assumption.
          apply col_permutation_5.
          assumption.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ M).
          intro.
          subst M.
          apply l7_2 in H3.
          apply is_midpoint_id in H3.
          subst C.
          absurde.
          apply col_permutation_3.
          apply bet_col.
          apply midpoint_bet.
          assumption.
        apply col_permutation_2.
        assumption.
      exists M.
      split.
        apply col_permutation_4.
        apply bet_col.
        apply midpoint_bet.
        assumption.
      apply midpoint_bet.
      assumption.
    assert(TS A C B D).
      repeat split.
        intro.
        apply H.
        apply col_permutation_4.
        assumption.
        intro.
        apply H.
        eapply (col_transitivity_1 _ D).
          assumption.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        apply col_permutation_4.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      assumption.
    assert(OS A C D P).
      unfold OS.
      exists B.
      split.
        apply l9_2.
        assumption.
      apply l9_2.
      assumption.
    apply invert_two_sides in H13.
    apply l9_9 in H13.
    contradiction.
Qed.

(** This is exterior angle theorem *)

Lemma l11_41 : forall A B C D,
  ~ Col A B C ->
  Bet B A D ->
  A <> D ->
  LtA A C B C A D /\ LtA A B C C A D.
Proof.
    intros.
    split.
      apply l11_41_aux.
        assumption.
        assumption.
      assumption.
    prolong C A E C A.
    assert(LtA A B C B A E).
      eapply l11_41_aux.
        intro.
        apply H.
        apply col_permutation_5.
        assumption.
        assumption.
        assert_diffs;auto.
    assert(CongA B A C C A B).
    {
      apply conga_left_comm.
      apply conga_refl;
      assert_diffs;auto.
    }
    assert(CongA D A C E A B)
      by (eapply l11_13 with B C;assert_diffs;auto).
    unfold LtA in *.
    spliter.
    repeat split.
      eapply l11_30 with A B C B A E;finish.
        apply conga_refl;assert_diffs;auto.
      apply conga_sym.
      apply conga_comm.
      assumption.
    intro.
    apply H7.
    eapply conga_trans.
      apply H8.
    apply conga_comm.
    assumption.
Qed.

Lemma not_conga : forall A B C A' B' C' D E F ,
 CongA A B C A' B' C' ->
 ~ CongA A B C D E F ->
 ~ CongA A' B' C' D E F.
Proof.
    intros.
    intro.
    apply H0.
    eapply conga_trans.
      apply H.
    assumption.
Qed.

Lemma not_conga_sym : forall A B C D E F,
 ~ CongA A B C D E F ->
 ~ CongA D E F A B C.
Proof.
    intros.
    intro.
    apply H.
    apply conga_sym.
    assumption.
Qed.

Lemma not_and_lta : forall A B C D E F, ~ (LtA A B C D E F /\ LtA D E F A B C).
Proof.
    intros.
    intro.
    unfold LtA in *.
    spliter.
    assert(CongA A B C D E F).
      apply lea_asym.
        assumption.
      assumption.
    contradiction.
Qed.

Lemma conga_preserves_lta : forall A B C D E F A' B' C' D' E' F',
 CongA A B C A' B' C' ->
 CongA D E F D' E' F' ->
 LtA A B C D E F ->
 LtA A' B' C' D' E' F'.
Proof.
    intros.
    unfold LtA in *.
    spliter.
    split.
      eapply l11_30.
        apply H1.
        assumption.
      assumption.
    intro.
    apply H2.
    eapply conga_trans.
      apply H.
    eapply conga_trans.
      apply H3.
    apply conga_sym.
    assumption.
Qed.

Lemma conga_preserves_gta : forall A B C D E F A' B' C' D' E' F',
 CongA A B C A' B' C' ->
 CongA D E F D' E' F' ->
 GtA A B C D E F ->
 GtA A' B' C' D' E' F'.
Proof.
    intros.
    unfold GtA in *.
    eapply conga_preserves_lta.
      apply H0.
      apply H.
    assumption.
Qed.

Lemma lta_trans : forall A B C A1 B1 C1 A2 B2 C2,
 LtA A B C A1 B1 C1 ->
 LtA A1 B1 C1 A2 B2 C2 ->
 LtA A B C A2 B2 C2.
Proof.
    intros.
    assert(HH1:= H).
    assert(HH2:= H0).
    unfold LtA in H.
    unfold LtA in H0.
    spliter.
    assert(LeA A B C A2 B2 C2).
      eapply lea_trans.
        apply H.
      assumption.
    split.
      assumption.
    intro.
    assert(LtA A2 B2 C2 A1 B1 C1).
      eapply conga_preserves_lta.
        apply H4.
        apply conga_refl.
          unfold LeA in H0.
          ex_and H0 X.
          unfold CongA in H5.
          spliter.
          assumption.
        unfold LeA in H0.
        ex_and H0 X.
        unfold CongA in H5.
        spliter.
        assumption.
      assumption.
    apply (not_and_lta A1 B1 C1 A2 B2 C2).
    split; assumption.
Qed.

Lemma gta_trans : forall A B C A1 B1 C1 A2 B2 C2,
 GtA A B C A1 B1 C1 ->
 GtA A1 B1 C1 A2 B2 C2 ->
 GtA A B C A2 B2 C2.
Proof.
    intros.
    unfold GtA in *.
    eapply lta_trans.
      apply H0.
    assumption.
Qed.

Lemma lea_left_comm : forall A B C D E F, LeA A B C D E F -> LeA C B A D E F.
Proof.
    intros.
    unfold LeA in *.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply conga_left_comm.
    assumption.
Qed.

Lemma lea_right_comm : forall A B C D E F, LeA A B C D E F -> LeA A B C F E D.
Proof.
    intros.
    apply l11_29_b.
    apply l11_29_a in H.
    ex_and H P.
    exists P.
    split.
      assumption.
    apply conga_right_comm.
    assumption.
Qed.

Lemma lea_comm : forall A B C D E F, LeA A B C D E F -> LeA C B A F E D.
Proof.
    intros.
    apply lea_left_comm.
    apply lea_right_comm.
    assumption.
Qed.

Lemma lta_left_comm : forall A B C D E F, LtA A B C D E F -> LtA C B A D E F.
Proof.
    unfold LtA.
    intros.
    spliter.
    split.
      apply lea_left_comm.
      assumption.
    intro.
    apply H0.
    apply conga_left_comm.
    assumption.
Qed.

Lemma lta_right_comm : forall A B C D E F, LtA A B C D E F -> LtA A B C F E D.
Proof.
    unfold LtA.
    intros.
    spliter.
    split.
      apply lea_right_comm.
      assumption.
    intro.
    apply H0.
    apply conga_right_comm.
    assumption.
Qed.

Lemma lta_comm : forall A B C D E F, LtA A B C D E F -> LtA C B A F E D.
Proof.
    intros.
    apply lta_left_comm.
    apply lta_right_comm.
    assumption.
Qed.

Lemma obtuse_sym : forall A B C, Obtuse A B C -> Obtuse C B A.
Proof.
    unfold Obtuse.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    unfold GtA in *.
    apply lta_right_comm.
    assumption.
Qed.

Lemma acute_sym : forall A B C, Acute A B C -> Acute C B A.
Proof.
    unfold Acute.
    intros.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split;auto using lta_left_comm.
Qed.

Lemma acute_col__out : forall A B C, Col A B C -> Acute A B C -> Out B A C.
Proof.
    intros.
    destruct H0 as [X [Y [Z []]]].
    apply col_lta__out with X Y Z; assumption.
Qed.

Lemma col_obtuse__bet : forall A B C, Col A B C -> Obtuse A B C -> Bet A B C.
Proof.
    intros.
    destruct H0 as [X [Y [Z []]]].
    apply (col_lta__bet X Y Z); assumption.
Qed.

Lemma out__acute : forall A B C, Out B A C -> Acute A B C.
Proof.
  intros A B C Hout.
  assert_diffs.
  assert(HD := perp_exists B A B).
  destruct HD as [D]; auto.
  assert_diffs.
  exists A.
  exists B.
  exists D.
  split; Perp.
  split.
  apply l11_31_1; auto.
  intro.
  assert(HNCol : ~ Col A B D) by (apply per_not_col; Perp).
  apply HNCol.
  apply col_permutation_4.
  apply out_col.
  apply (l11_21_a A B C); auto.
Qed.

Lemma bet__obtuse : forall A B C, Bet A B C -> A <> B -> B <> C -> Obtuse A B C.
Proof.
  intros A B C HBet HAB HBC.
  assert(HD := perp_exists B A B).
  destruct HD as [D]; auto.
  assert_diffs.
  exists A.
  exists B.
  exists D.
  split; Perp.
  split.
  apply l11_31_2; auto.
  intro.
  assert(HNCol : ~ Col A B D) by (apply per_not_col; Perp).
  apply HNCol.
  apply bet_col.
  apply (bet_conga__bet A B C); try (apply conga_sym); auto.
Qed.

Lemma l11_43_aux : forall A B C, A <> B -> A <> C -> (Per B A C \/ Obtuse B A C) -> Acute A B C.
Proof.
    intros.
    induction (col_dec A B C).
      induction H1.
        exfalso.
        apply (per_not_col B A C); Col.
      apply out__acute, bet_out; auto.
      apply col_obtuse__bet; Col.
    assert_diffs.
    prolong B A B' B A.
    assert(~ Col B' A C).
      intro.
      apply H2.
      eapply (col_transitivity_1 _ B').
        intro.
        subst B'.
        apply cong_symmetry in H4.
        apply cong_identity in H4.
        subst A.
        apply H2.
        apply col_trivial_1.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply col_permutation_4.
      assumption.
    apply not_col_distincts in H6.
    spliter.
    assert(LtA A C B C A B'/\ LtA A B C C A B').
      apply l11_41.
        assumption.
        assumption.
      auto.
    spliter.
    induction H1.
      unfold Acute.
      exists C.
      exists A.
      exists B.
      split.
        apply l8_2.
        assumption.
      spliter.
      unfold LtA.
      unfold LtA in H11.
      spliter.
      assert(Per B' A C).
        apply l8_2.
        eapply (per_col _ _ B).
          assumption.
          apply l8_2.
          assumption.
        apply col_permutation_4.
        apply bet_col.
        assumption.
      assert(CongA B A C B' A C).
        apply l11_16.
          assumption.
          auto.
          auto.
          assumption.
          assumption.
        auto.
      split.
        eapply l11_30.
          apply H11.
          apply conga_refl.
            assumption.
          auto.
        apply conga_comm.
        apply conga_sym.
        assumption.
      intro.
      apply H12.
      eapply conga_trans.
        apply H15.
      apply conga_comm.
      assumption.
    unfold Acute.
    unfold Obtuse in H1.
    ex_and H1 a.
    ex_and H12 b.
    ex_and H1 c.
    unfold GtA in H12.
    assert(HH1:= H12).
    unfold LtA in H12.
    spliter.
    unfold LeA in H12.
    ex_and H12 P.
    exists B.
    exists A.
    exists P.
    assert(Per B A P).
      eapply l11_17.
        apply H1.
      assumption.
    split.
      assumption.
    assert(Per P A B').
      eapply per_col.
        apply H.
        apply l8_2.
        assumption.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(CongA B A P B' A P).
      eapply l11_16.
        assumption.
        auto.
        intro.
        subst P.
        unfold CongA in H14.
        spliter.
        absurde.
        apply l8_2.
        assumption.
        assumption.
      intro.
      subst P.
      unfold CongA in H14.
      spliter.
      absurde.
    assert(LtA C A B' P A B).
      assert(B <> A).
        auto.
      assert(HH := l11_36 B A P B A C B' B' H18 H7 H18 H7 H3 H3).
      destruct HH.
      unfold LtA.
      split.
        eapply l11_30.
          apply H19.
          unfold LtA in HH1.
          spliter.
          eapply l11_30.
            apply H21.
            assumption.
          apply conga_refl.
            auto.
          auto.
          apply conga_left_comm.
          apply conga_refl.
            auto.
          assumption.
        apply conga_right_comm.
        apply conga_sym.
        assumption.
      intro.
      apply H13.
      assert(Per B' A C).
        eapply l11_17.
          apply H15.
        apply conga_comm.
        apply conga_sym.
        assumption.
      assert(Per C A B).
        eapply (per_col _ _ B').
          auto.
          apply l8_2.
          assumption.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply l11_16.
        assumption.
        unfold CongA in H14.
        spliter.
        assumption.
        unfold CongA in H14.
        spliter.
        assumption.
        apply l8_2.
        assumption.
        auto.
      auto.
    eapply lta_trans.
      apply H11.
    apply lta_right_comm.
    assumption.
Qed.

Lemma l11_43 : forall A B C, A <> B -> A <> C -> (Per B A C \/ Obtuse B A C) -> Acute A B C /\ Acute A C B.
Proof.
    intros.
    split.
      apply l11_43_aux;auto.
    apply l11_43_aux;auto.
    induction H1.
      left;finish.
    right;apply obtuse_sym;assumption.
Qed.

Lemma acute_lea_acute : forall A B C D E F, Acute D E F -> LeA A B C D E F -> Acute A B C.
Proof.
    intros.
    unfold Acute in *.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold LtA in H1.
    spliter.
    unfold LtA.
    split.
      eapply lea_trans.
        apply H0.
      assumption.
    intro.
    assert(LtA A' B' C' D E F).
      eapply conga_preserves_lta.
        apply H3.
        apply conga_refl.
          unfold LeA in H0.
          ex_and H0 X.
          unfold CongA in H4.
          spliter.
          assumption.
        apply lea_comm in H0.
        unfold LeA in H0.
        ex_and H0 X.
        unfold CongA in H4.
        spliter.
        assumption.
      split.
        assumption.
      intro.
      apply H2.
      eapply conga_trans.
        apply conga_sym.
        apply H4.
      assumption.
    apply (not_and_lta A' B' C' D E F).
    split; assumption.
Qed.

Lemma obtuse_gea_obtuse : forall A B C D E F, Obtuse D E F -> GeA A B C D E F -> Obtuse A B C.
Proof.
    intros.
    ex_and H A'.
    ex_and H1 B'.
    ex_and H C'.
    exists A'.
    exists B'.
    exists C'.
    split.
      assumption.
    assert(HH1:=H1).
    unfold GtA in H1.
    unfold LtA in H1.
    spliter.
    unfold GtA.
    unfold LtA.
    split.
      eapply lea_trans.
        apply H1.
      assumption.
    intro.
    assert(GtA A' B' C' D E F).
      eapply conga_preserves_gta.
        apply conga_sym.
        apply H3; apply H3.
        apply conga_refl.
          unfold LeA in H0.
          ex_and H0 X.
          unfold CongA in H4.
          spliter.
          assumption.
        apply lea_comm in H0.
        unfold LeA in H0.
        ex_and H0 X.
        unfold CongA in H4.
        spliter.
        assumption.
      unfold GtA.
      split.
        assumption.
      intro.
      apply H2.
      eapply conga_trans.
        apply H3.
      apply conga_sym.
      assumption.
    unfold GtA in *.
    apply (not_and_lta A' B' C' D E F).
    split; assumption.
Qed.

(** In an isosceles triangle the two base angles are equal.
    This is Euclid: Book 1, Proposition 5.
 *)

Lemma l11_44_1_a : forall A B C, A <> B -> A <> C -> Cong B A B C -> CongA B A C B C A.
Proof.
    intros.
    destruct (midpoint_existence A C) as [P HP].
    assert_diffs.
    assert(Cong_3 B C P B A P) by (repeat split;finish).
    assert(CongA B C P B A P) by (auto using cong3_conga).
    apply conga_sym.
    eapply l11_10 with B P B P;finish.
Qed.

(** This is Euclid: Book 1, Proposition 18 *)

Lemma l11_44_2_a : forall A B C, ~ Col A B C -> Lt B A B C -> LtA B C A B A C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    unfold Lt in H0.
    spliter.
    unfold Le in H0.
    ex_and H0 C'.
    assert(C <> C').
      intro.
      subst C'.
      contradiction.
    assert(C' <> A).
      intro.
      subst C'.
      apply H.
      apply col_permutation_4.
      apply bet_col.
      assumption.
    assert(C' <> B).
      intro.
      subst C'.
      apply cong_identity in H5.
      subst A.
      absurde.
    assert(InAngle C' B A C).
      repeat split.
        auto.
        auto.
        assumption.
      exists C'.
      split.
        assumption.
      right.
      apply out_trivial.
      auto.
    assert(HH:=l11_41 C' C A B).
    assert(LtA C' A C A C' B /\ LtA C' C A A C' B).
      apply HH.
        intro.
        apply H.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply H6.
          apply col_permutation_4.
          assumption.
        apply col_permutation_3.
        apply bet_col.
        assumption.
        apply between_symmetry.
        assumption.
      assumption.
    clear HH.
    spliter.
    assert(LtA B A C' B A C).
      split.
        unfold LeA.
        exists C'.
        split.
          assumption.
        apply conga_refl.
          auto.
        assumption.
      intro.
      apply conga_cop__or_out_ts in H12; Cop.
      induction H12.
        apply H.
        apply out_col in H12.
        apply bet_col in H0.
        apply col_permutation_1.
        eapply col_transitivity_1.
          apply H6.
          Col.
        Col.
      assert(OS B A C' C).
        apply out_one_side.
          right.
          intro.
          apply H.
          Col.
        apply bet_out;auto.
      apply l9_9 in H12.
      contradiction.
    assert(LtA B C A A C' B).
      eapply conga_preserves_lta.
        3: apply H11.
        eapply out_conga.
          apply conga_refl.
            apply H2.
          apply H3.
          apply l6_6.
          apply bet_out.
            auto.
          apply between_symmetry.
          assumption.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
        apply out_trivial.
        auto.
      apply conga_refl.
        auto.
      auto.
    assert(CongA B A C' B C' A).
      apply (l11_44_1_a A B C'); auto.
    apply conga_right_comm in H14.
    assert(LtA B C A B A C').
      eapply conga_preserves_lta.
        2: apply conga_sym.
        2: apply H14.
        apply conga_refl.
          assumption.
        assumption.
      assumption.
    eapply lta_trans.
      apply H15.
    assumption.
Qed.

Lemma not_lta_and_conga : forall A B C D E F, ~ (LtA A B C D E F /\ CongA A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold LtA in H.
    spliter.
    contradiction.
Qed.

Lemma not_gta_and_conga : forall A B C D E F, ~ (GtA A B C D E F /\ CongA A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold GtA in H.
    unfold LtA in H.
    spliter.
    apply conga_sym in H0.
    contradiction.
Qed.

Lemma not_lta_and_gta : forall  A B C D E F, ~ (LtA A B C D E F /\ GtA A B C D E F).
Proof.
    intros.
    intro.
    spliter.
    unfold GtA in H0.
    unfold LtA in *.
    spliter.
    apply H2.
    apply lea_asym.
      assumption.
    assumption.
Qed.

Lemma conga_sym_equiv : forall A B C A' B' C', CongA A B C A' B' C' <-> CongA A' B' C' A B C.
Proof.
    intros.
    split; apply conga_sym.
Qed.

Lemma conga_dec :
  forall A B C D E F,
   CongA A B C D E F \/ ~ CongA A B C D E F.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst;right;intro;unfold CongA in *;intuition.
    induction (eq_dec_points C B).
      subst;right;intro;unfold CongA in *;intuition.
    induction (eq_dec_points D E).
      subst;right;intro;unfold CongA in *;intuition.
    induction (eq_dec_points F E).
      subst;right;intro;unfold CongA in *;intuition.
    assert (exists A' : Tpoint, Bet B A A' /\ Cong A A' E D) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists C' : Tpoint, Bet B C C' /\ Cong C C' E F) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists D' : Tpoint, Bet E D D' /\ Cong D D' B A) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    assert (exists F' : Tpoint, Bet E F F' /\ Cong F F' B C) by (apply segment_construction).
    decompose [ex and] H3; clear H3.
    induction (cong_dec x x0 x1 x2).
      left.
      unfold CongA.
      repeat split; try assumption.
      exists x; exists x0; exists x1; exists x2.
      repeat split; assumption.
    right.
    unfold CongA.
    intro.
    decompose [and ex] H4; clear H4.
    assert (x3 = x) by (apply construction_uniqueness with B A E D; intuition).
    assert (x4 = x0) by (apply construction_uniqueness with B C E F; intuition).
    assert (x5 = x1) by (apply construction_uniqueness with E D B A; intuition).
    assert (x6 = x2) by (apply construction_uniqueness with E F B C; intuition).
    subst.
    contradiction.
Qed.

Lemma lta_not_conga : forall A B C D E F, LtA A B C D E F -> ~ CongA A B C D E F.
Proof.
    intros.
    intro.
    unfold LtA in H.
    spliter.
    contradiction.
Qed.

(** If the base angles are equal, then the triangle is isosceles *)

Lemma l11_44_1_b : forall A B C, ~ Col A B C -> CongA B A C B C A -> Cong B A B C.
Proof.
    intros.
    apply not_col_distincts in H.
    spliter.
    assert(HH:= or_lt_cong_gt B A B C).
    induction HH.
      apply l11_44_2_a in H4.
        apply lta_not_conga in H4.
          apply conga_sym in H0.
          contradiction.
      assumption.
    induction H4.
      unfold Gt in H4.
      apply l11_44_2_a in H4.
        apply lta_not_conga in H4.
          contradiction.
      intro.
      apply H.
      apply col_permutation_3.
      assumption.
    assumption.
Qed.

(** This is Euclid Book I, Proposition 19 *)

Lemma l11_44_2_b : forall A B C, LtA B A C B C A -> Lt B C B A.
Proof.
    intros.
    induction (col_dec A B C).
      assert (Hd := H).
      apply lta_distincts in Hd; spliter; clean_reap_hyps.
      apply col_lta__bet in H; Col; Le.
    apply not_col_distincts in H0.
    spliter.
    assert(HH:= or_lt_cong_gt B A B C).
    induction HH.
      apply l11_44_2_a in H4.
        assert(HH:= not_lta_and_gta B A C B C A).
        exfalso.
        apply HH.
        split; assumption.
      assumption.
    induction H4.
      unfold Gt in H4.
      assumption.
    apply l11_44_1_a in H4; auto.
    apply lta_not_conga in H; auto.
    contradiction.
Qed.

Lemma l11_44_1 : forall A B C, ~ Col A B C -> (CongA B A C B C A <-> Cong B A B C).
Proof.
    intros;assert_diffs;split;intro; auto using l11_44_1_b, l11_44_1_a.
Qed.

Lemma l11_44_2 : forall A B C, ~ Col A B C -> (LtA B A C B C A <-> Lt B C B A).
Proof.
    intros;split;intro;
    auto using l11_44_2_b, l11_44_2_a with col. 
Qed.

Lemma l11_46 : forall A B C, A <> B -> B <> C -> (Per A B C \/ Obtuse A B C) -> Lt B A A C /\ Lt B C A C.
Proof.
    intros.
    induction (col_dec A B C).
      induction H1.
        exfalso.
        apply (per_not_col A B C); auto.
      apply col_obtuse__bet in H1; auto.
      repeat split; Le.
        intro.
        apply H0, between_cong with A; Cong.
      intro.
      apply H, eq_sym, between_cong with C; finish.
    assert_diffs.
    assert(HH:= H1).
    apply l11_43 in H1; auto.
      spliter.
      split.
        apply lt_left_comm.
        apply l11_44_2_b.
        unfold Acute in H3.
        ex_and H3 A'.
        ex_and H4 B'.
        ex_and H3 C'.
        assert (Hd := H4).
        apply lta_distincts in Hd.
        spliter.
        induction HH.
         {
            eapply conga_preserves_lta with A C B A' B' C'.
              apply conga_refl;auto.
              apply l11_16;auto.
          apply lta_left_comm.
          assumption.
         }
        unfold Obtuse in H11.
        ex_and H11 A''.
        ex_and H12 B''.
        ex_and H11 C''.
        unfold GtA in H12.
        eapply lta_trans.
          apply lta_left_comm.
          apply H4.
        eapply conga_preserves_lta with A'' B'' C'' A B C.
          assert (Hd := H12).
          apply lta_distincts in Hd.
          spliter.
          apply l11_16.
            apply H11.
            assumption.
            assumption.
            assumption.
            assumption.
          assumption.
          apply conga_refl.
            assumption.
          auto.
        assumption.
      apply lt_left_comm.
      apply lt_right_comm.
      eapply l11_44_2_b.
        finish.
      unfold Acute in H1.
      ex_and H1 A'.
      ex_and H4 B'.
      ex_and H1 C'.
      assert (Hd := H4).
      apply lta_distincts in Hd.
      spliter.
      induction HH.
        eapply conga_preserves_lta.
          apply conga_refl.
            auto.
          auto.
          apply l11_16.
            apply H1.
            assumption.
            assumption.
            apply l8_2.
            assumption.
            auto.
          assumption.
        apply lta_left_comm.
        assumption.
      unfold Obtuse in H11.
      ex_and H11 A''.
      ex_and H12 B''.
      ex_and H11 C''.
      unfold GtA in H12.
      eapply lta_trans.
        apply lta_left_comm.
        apply H4.
      eapply conga_preserves_lta.
        apply lta_distincts in H12.
        spliter.
        apply l11_16.
          apply H11.
          assumption.
          assumption.
          assumption.
          assumption.
        assumption.
        apply conga_refl.
          auto.
        assumption.
      apply lta_right_comm.
      assumption.
Qed.

Lemma l11_47 : forall A B C H , Per A C B -> Perp_at H C H A B ->
 Bet A H B /\ A <> H /\ B <> H.
Proof.
    intros.
    assert(HH1:= H1).
    unfold Perp_at in H1.
    spliter.
    assert(Per C H A).
      apply H5.
        apply col_trivial_1.
      apply col_trivial_1.
    assert(Perp C H A B).
      eapply l8_14_2_1a.
      apply HH1.
    induction (col_dec A C B).
      assert(A <> H).
        intro.
        subst H.
        apply H1.
        apply sym_equal.
        eapply per_col_eq.
          apply H0.
          assumption.
        intro.
        subst B.
        assert(Perp_at C C A A C).
          apply perp_perp_in.
          assumption.
        apply H2.
        eapply l8_14_3.
          apply HH1.
        assumption.
      apply False_ind.
      apply H9.
      eapply per_col_eq.
        apply l8_2.
        apply H6.
        ColR.
       (* eapply (col_transitivity_1 _ B).
          assumption.
          apply col_permutation_1.
          assumption.
        apply col_permutation_5.
        assumption. *)
      auto.
    apply not_col_distincts in H8.
    spliter.
    assert(A <> H).
      intro.
      subst A.
      assert(Per C H B).
        apply perp_in_per.
        assumption.
      apply H1.
      eapply l8_7.
        apply l8_2.
        apply H0.
      apply l8_2.
      assumption.
    assert(Per C H B).
      eapply per_col.
        2: apply H6.
        auto.
      assumption.
    assert(H <> B).
      intro.
      subst B.
      apply H10.
      eapply l8_7.
        apply H0.
      apply l8_2.
      assumption.
    assert(Lt H A A C /\ Lt H C A C).
      apply l11_46; auto.
      left.
      apply l8_2.
      assumption.
    assert(Lt C A A B /\ Lt C B A B).
      apply l11_46; auto.
    assert(Lt H B B C /\ Lt H C B C).
      apply l11_46; auto.
      left.
      finish.
    split.
      unfold Lt in *.
      spliter.
      apply l5_12_b.
        finish.
        eapply le_transitivity.
          apply le_left_comm.
          apply H15.
        apply le_left_comm.
        assumption.
      eapply le_transitivity.
        apply H17.
      apply le_left_comm.
      assumption.
    split;auto.
Qed.


(** This is SAS congruence. *)

Lemma l11_49 : forall A B C A' B' C',
 CongA A B C A' B' C' -> Cong B A B' A' -> Cong B C B' C' ->
 Cong A C A' C' /\ (A <> C -> CongA B A C B' A' C' /\ CongA B C A B' C' A').
Proof.
    intros.
    assert(Cong A C A' C').
      eapply cong2_conga_cong.
        apply H.
        apply cong_commutativity.
        assumption.
      assumption.
    split.
      assumption.
    intro.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold CongA in H.
      spliter.
      repeat split; assumption.
    spliter.
    split.
      apply l11_3_bis.
      exists B.
      exists C.
      exists B'.
      exists C'.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        auto.
      split.
        apply out_trivial.
        intro.
        subst C'.
        apply cong_identity in H2.
        contradiction.
      repeat split; assumption.
    apply l11_3_bis.
    exists B.
    exists A.
    exists B'.
    exists A'.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      auto.
    split.
      apply out_trivial.
      intro.
      subst C'.
      apply cong_identity in H2.
      contradiction.
    repeat split.
      assumption.
      assumption.
    apply cong_commutativity.
    assumption.
Qed.

(** This is ASA congruence. *)

Lemma l11_50_1  : forall A B C A' B' C',
  ~ Col A B C -> CongA B A C B' A' C' -> CongA A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ CongA A C B A' C' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B') by (unfold CongA in *;intuition).
    spliter.
    assert(exists C'', Out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence;auto.
    ex_and H7 C''.
    assert(B' <> C'') by (unfold Out in *;intuition).
    assert(~ Col A' B' C') by (eapply ncol_conga_ncol;eauto).
    assert(~ Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ C'').
        assumption.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    spliter.
    assert(Cong A C A' C'').
      apply H16.
      assert (C''<> B') by auto.
      repeat split;try assumption.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        auto.
        unfold Out in  H7.
        spliter.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Cong_3 B A C B' A' C'').
      repeat split.
        apply cong_commutativity.
        assumption.
        apply cong_symmetry.
        assumption.
      assumption.
    assert(CongA B A C B' A' C'').
      apply cong3_conga.
        auto.
        apply not_col_distincts in H.
        spliter.
        auto.
      assumption.
    assert(CongA B' A' C' B' A' C'').
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      assumption.
    assert(C' = C'').
      assert(HCop : Coplanar B' A' C' C'') by Cop.
      assert(HH:= conga_cop__or_out_ts B' A' C' C'' HCop H20).
      induction HH.
        eapply l6_21.
          apply not_col_permutation_5.
          apply H10.
          apply H9.
          apply col_trivial_2.
          apply out_col.
          assumption.
          apply out_col in H7.
          assumption.
          apply col_trivial_2.
      assert(OS B' A' C' C'').
        apply out_one_side.
          left.
          intro.
          apply H10.
          apply col_permutation_4.
          assumption.
        apply l6_6.
        assumption.
      apply l9_9 in H21.
      contradiction.
    subst C''.
    clear H20.
    split.
      assumption.
    split.
      eapply cong2_conga_cong.
        apply H19.
        apply cong_commutativity.
        assumption.
      assumption.
    apply cong3_conga.
      apply not_col_distincts in H.
      spliter.
      assumption.
      auto.
    unfold Cong_3.
    repeat split.
      assumption.
      assumption.
    apply cong_symmetry.
    apply cong_commutativity.
    assumption.
Qed.

(** This is AAS congruence. *)

Lemma l11_50_2  : forall A B C A' B' C',
  ~ Col A B C -> CongA B C A B' C' A' -> CongA A B C A' B' C' -> Cong A B A' B' ->
  Cong A C A' C' /\ Cong B C B' C' /\ CongA C A B C' A' B'.
Proof.
    intros.
    assert(A <> B /\ C <> B /\ A' <> B'  /\ C' <> B').
      unfold CongA in H1.
      spliter.
      repeat split; assumption.
    spliter.
    assert(exists C'',  Out B' C'' C' /\ Cong B' C'' B C).
      apply l6_11_existence.
        assumption.
      auto.
    ex_and H7 C''.
    assert(B' <> C'').
      unfold Out in H7.
      spliter.
      auto.
    assert(~Col A' B' C').
      eapply ncol_conga_ncol.
        apply H.
      assumption.
    assert(~Col A' B' C'').
      intro.
      apply H10.
      apply out_col in H7.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ C'').
        assumption.
        assumption.
      apply col_permutation_1.
      assumption.
    assert(HH:=l11_4_1 A B C A' B' C' H1).
    spliter.
    assert(Cong A C A' C'').
      apply H16.
      repeat split; try assumption.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        left.
        apply between_trivial.
        auto.
        unfold Out in  H7.
        spliter.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_symmetry.
      assumption.
    assert(Cong_3 B C A B' C'' A').
      repeat split.
        apply cong_symmetry.
        assumption.
        apply cong_commutativity.
        assumption.
      apply cong_commutativity.
      assumption.
    assert(CongA B C A B' C'' A').
      apply cong3_conga.
        auto.
        apply not_col_distincts in H.
        spliter.
        assumption.
      assumption.
    assert(CongA B' C' A' B' C'' A').
      eapply conga_trans.
        apply conga_sym.
        apply H0.
      assumption.
    apply not_col_distincts in H.
    apply not_col_distincts in H10.
    spliter.
    clear H16.
    induction(eq_dec_points C' C'').
      induction (eq_dec_points C' C'').
        subst C''.
        split.
          assumption.
        split.
          apply cong_symmetry.
          assumption.
        assert(Cong_3 C A B C' A' B').
          repeat split.
            apply cong_commutativity.
            assumption.
            apply cong_commutativity.
            apply cong_symmetry.
            assumption.
          assumption.
        apply cong3_conga.
          auto.
          auto.
        assumption.
      apply False_ind.
      apply H27.
      assumption.
    assert(~Col C'' C' A').
      intro.
      apply H10.
      apply col_permutation_1.
      eapply col_transitivity_1.
        apply H16.
        apply col_permutation_4.
        assumption.
      apply col_permutation_3.
      apply out_col.
      assumption.
    apply not_col_distincts in H27.
    spliter.
    unfold Out in H7.
    spliter.
    induction H32.
      assert(HH:=l11_41 ).
      assert(HH1:=l11_41 C'' C' A' B' H27 (between_symmetry _ _ _ H32) H7).
      spliter.
      assert(CongA B' C' A' C'' C' A').
        eapply (l11_10 B' C' A' B' C' A').
          apply conga_refl.
            auto.
          assumption.
          apply out_trivial.
          assumption.
          apply out_trivial.
          auto.
          apply bet_out.
            auto.
          apply  between_symmetry.
          assumption.
        apply out_trivial.
        auto.
      assert(LtA B' C' A' A' C'' B').
        eapply conga_preserves_lta.
          apply conga_sym.
          apply H35.
          apply conga_refl.
            auto.
          auto.
        assumption.
      unfold LtA in H36.
      spliter.
      apply conga_right_comm in H20.
      contradiction.
    assert(~Col C' C'' A').
      intro.
      apply H27.
      apply col_permutation_4.
      assumption.
    assert(HH1:=l11_41 C' C'' A' B' H33 (between_symmetry _ _ _ H32) H15).
    spliter.
    assert(CongA B' C'' A' C' C'' A').
      eapply (l11_10 B' C'' A' B' C'' A').
        apply conga_refl.
          auto.
        auto.
        apply out_trivial.
        assumption.
        apply out_trivial.
        auto.
        apply bet_out.
          auto.
        apply  between_symmetry.
        assumption.
      apply out_trivial.
      auto.
    assert(LtA B' C'' A' A' C' B').
      eapply conga_preserves_lta.
        apply conga_sym.
        apply H36.
        apply conga_refl.
          auto.
        auto.
      assumption.
    unfold LtA in H37.
    spliter.
    apply conga_sym in H20.
    apply conga_right_comm in H20.
    contradiction.
Qed.

(** This is SSS congruence. *)

Lemma l11_51 : forall A B C A' B' C',
  A <> B -> A <> C -> B <> C -> Cong A B A' B' -> Cong A C A' C' -> Cong B C B' C' ->
  CongA B A C B' A' C' /\ CongA A B C A' B' C' /\ CongA B C A B' C' A'.
Proof.
    intros.
    assert(Cong_3 B A C B' A' C' /\ Cong_3 A B C A' B' C' /\ Cong_3 B C A B' C' A').
      repeat split; cong.
    spliter.
    split.
      apply cong3_conga.
        auto.
        auto.
      assumption.
    split.
      apply cong3_conga.
        assumption.
        auto.
      assumption.
    apply cong3_conga.
      assumption.
      assumption.
    assumption.
Qed.

Lemma conga_distinct : forall A B C D E F, CongA A B C D E F -> CongA A B C D E F /\ A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
    intros.
    split.
      assumption.
    unfold CongA in H.
    spliter.
    repeat split; assumption.
Qed.

(** This is SSA congruence with a restriction *)

Lemma l11_52 : forall A B C A' B' C',
  CongA A B C A' B' C' -> Cong A C A' C' -> Cong B C B' C' -> Le B C A C ->
  Cong B A B' A' /\ CongA B A C B' A' C' /\ CongA B C A B' C' A'.
Proof.
    intros.
    apply conga_distinct in H.
    spliter.
    assert(Cong B A B' A').
      induction(col_dec A B C).
        unfold Col in H7.
        induction H7.
          assert(Bet A' B' C').
            eapply bet_conga__bet.
              apply H7.
            assumption.
          apply cong_commutativity.
          eapply l4_3.
            apply H7.
            apply H8.
            assumption.
          assumption.
        induction H7.
          assert(Out B' A' C').
            eapply l11_21_a.
              apply bet_out.
                apply H4.
              apply H7.
            apply conga_left_comm.
            assumption.
          unfold Out in H8.
          spliter.
          induction H10.
            assert(Le B' C' A' C').
              eapply l5_6.
              repeat split.
                apply H2.
                assumption.
              assumption.
            assert(B'=A').
              eapply bet_le_eq.
                apply H10.
              assumption.
            subst B'.
            absurde.
          eapply l2_11.
            apply H7.
            apply H10.
            assumption.
          cong.
        assert(B = A).
          eapply bet_le_eq.
            apply between_symmetry.
            apply H7.
          assumption.
        subst B.
        absurde.
      assert(exists A'', Out B' A'' A' /\ Cong B' A'' B A).
        apply l6_11_existence.
          assumption.
        auto.
      ex_and H8 A''.
      assert(CongA A' B' C' A'' B' C').
        eapply (l11_10  A'' _ C' A'' _ C' ).
          apply conga_refl.
            unfold Out in H8.
            spliter.
            assumption.
          assumption.
          apply l6_6.
          assumption.
          apply out_trivial.
          auto.
          apply out_trivial.
          unfold Out in H8.
          spliter.
          auto.
        apply out_trivial.
        auto.
      assert(CongA A B C A'' B' C').
        eapply l11_10.
          apply H.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          assumption.
        apply out_trivial.
        auto.
      assert(Cong A'' C' A C).
        eapply cong2_conga_cong.
          apply conga_sym.
          apply H11.
          cong.
        cong.
      assert(Cong_3 A'' B' C' A B C).
        repeat split; cong.
      assert(Cong A'' C' A' C').
        eapply cong_transitivity.
          apply H12.
        assumption.
      assert(~Col A' B' C').
        eapply ncol_conga_ncol.
          apply H7.
        assumption.
      assert(~Col A'' B' C').
        intro.
        apply H15.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ A'').
          intro.
          subst A''.
          unfold Out in H8.
          spliter.
          absurde.
          permut.
        apply out_col in H8.
        permut.
      induction(eq_dec_points A'' A').
        subst A''.
        unfold Cong_3 in H13.
        spliter.
        cong.
      unfold Out in H8.
      spliter.
      induction H19.
        assert(HH:= l11_41 A'' B' C' A' H16 H19 H17).
        spliter.
        assert(Cong A' C' A'' C').
          eapply (cong_transitivity _ _ A C).
            cong.
          unfold Cong_3 in H13.
          spliter.
          cong.
        assert(~Col A'' C' A').
          intro.
          apply H15.
          eapply (col_transitivity_1 _ A'' ).
            auto.
            apply bet_col in H19.
            permut.
          permut.
        assert (HH:= l11_44_1 A'' C' A' H23 ).
        destruct HH.
        apply cong_commutativity in H22.
        apply cong_symmetry in H22.
        apply H25 in H22.
        assert(~Col B' C' A'').
          intro.
          apply H16.
          permut.
        assert(CongA B' A' C' A'' A' C').
          eapply l11_10.
            apply conga_refl.
              3:apply out_trivial.
              auto.
            3:apply out_trivial.
            intro.
            subst C'.
            apply H15.
            apply col_trivial_3.
            auto.
            intro.
            subst C'.
            apply H15.
            apply col_trivial_3.
            apply between_symmetry in H19.
            apply bet_out in H19.
              assumption.
              assumption.
            auto.
          apply out_trivial.
          intro.
          subst C'.
          apply H15.
          apply col_trivial_3.
        assert(~Col B' C' A').
          intro.
          apply H15.
          permut.
        assert(HH:=l11_44_2 B' C' A' H28).
        destruct HH.
        assert(Lt C' A'  C' B').
          apply H29.
          eapply conga_preserves_lta.
            apply conga_right_comm.
            apply conga_sym.
            apply H10.
            2:apply H21.
          eapply conga_trans.
            apply H22.
          apply conga_comm.
          apply conga_sym.
          assumption.
        assert(Lt C' A'' C' B').
          unfold Lt in H31.
          spliter.
          unfold Lt.
          split.
            eapply l5_6.
              apply H31.
              apply cong_commutativity.
              cong.
            cong.
          intro.
          apply H32.
          eapply cong_transitivity.
            apply cong_commutativity.
            apply cong_symmetry.
            apply H14.
          assumption.
        unfold Lt in H32.
        spliter.
        assert(Le C A C B).
          eapply l5_6.
          repeat split.
            apply H32.
            apply cong_commutativity.
            assumption.
          apply cong_commutativity.
          cong.
        assert(Cong C A C B).
          apply le_anti_symmetry.
            assumption.
          apply le_comm.
          assumption.
        apply False_ind.
        apply H33.
        apply cong_symmetry.
        eapply cong_transitivity.
          apply cong_commutativity.
          apply cong_symmetry.
          apply H1.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H35.
        apply cong_commutativity.
        cong.
      assert(A' <> A'').
        auto.
      assert(HH:= l11_41 A' B' C' A'' H15 H19 H20).
      spliter.
      assert(Cong A' C' A'' C').
        eapply (cong_transitivity _ _ A C).
          cong.
        unfold Cong_3 in H13.
        spliter.
        cong.
      assert(~Col A'' C' A').
        intro.
        apply H15.
        eapply (col_transitivity_1 _ A'' ).
          auto.
          apply bet_col in H19.
          permut.
        permut.
      assert (HH:= l11_44_1 A'' C' A' H24 ).
      destruct HH.
      apply cong_commutativity in H23.
      apply cong_symmetry in H23.
      apply H26 in H23.
      assert(~Col B' C' A'').
        intro.
        apply H16.
        permut.
      assert(CongA B' A'' C' A' A'' C').
        eapply l11_10.
          apply conga_refl.
            3:apply out_trivial.
            auto.
          3:apply out_trivial.
          intro.
          subst C'.
          apply H16.
          apply col_trivial_3.
          auto.
          intro.
          subst C'.
          apply H16.
          apply col_trivial_3.
          apply between_symmetry in H19.
          apply bet_out in H19.
            assumption.
            assumption.
          auto.
        apply out_trivial.
        intro.
        subst C'.
        apply H16.
        apply col_trivial_3.
      assert(~Col B' C' A'').
        intro.
        apply H16.
        permut.
      assert(HH:=l11_44_2 B' C' A'' H29).
      destruct HH.
      assert(Lt C' A''  C' B').
        apply H30.
        eapply conga_preserves_lta.
          apply conga_right_comm.
          apply conga_sym.
          apply conga_sym.
          apply H10.
          2:apply H22.
        eapply conga_trans.
          apply conga_sym.
          apply H23.
        apply conga_comm.
        apply conga_sym.
        assumption.
      assert(Lt C' A' C' B').
        unfold Lt in H32.
        spliter.
        unfold Lt.
        split.
          eapply l5_6.
            apply H32.
            apply cong_commutativity.
            cong.
          cong.
        intro.
        apply H33.
        eapply cong_transitivity.
          apply cong_commutativity.
          apply H14.
        assumption.
      unfold Lt in H33.
      spliter.
      assert(Le C A C B).
        eapply l5_6.
        repeat split.
          apply H32.
          apply cong_commutativity.
          assumption.
        apply cong_commutativity.
        cong.
      assert(Cong C A C B).
        apply le_anti_symmetry.
          assumption.
        apply le_comm.
        assumption.
      apply False_ind.
      apply H34.
      apply cong_symmetry.
      eapply cong_transitivity.
        apply cong_commutativity.
        apply cong_symmetry.
        apply H1.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply H36.
      apply cong_commutativity.
      cong.
    assert(Cong_3 A B C A' B' C').
      repeat split; cong.
    split.
      assumption.
    split.
      apply cong3_conga.
        auto.
        intro.
        subst C.
        apply le_zero in H2.
        subst B.
        absurde.
      auto with cong3.
    apply cong3_conga.
      auto.
      intro.
      subst C.
      apply le_zero in H2.
      subst B.
      absurde.
    auto with cong3.
Qed.

Lemma l11_53 : forall A B C D,
 Per D C B -> C <> D -> A <> B -> B <> C -> Bet A B C ->
 LtA C A D C B D /\ Lt B D A D.
Proof.
    intros.
    assert(A<>C) by (intro; Between).
    spliter.
    assert(~Col B A D).
      intro.
      assert(Col B C D).
        eapply (col_transitivity_1 _ A).
          auto.
          apply bet_col in H3.
          permut.
        permut.
      assert(~Col  B C D).
        apply per_not_col.
          assumption.
          assumption.
        apply l8_2.
        assumption.
      contradiction.
    assert(A <> D).
      intro.
      subst D.
      apply H5.
      apply col_trivial_2.
    assert( LtA C A D C B D).
      assert(HH:=l11_41 B A D C H5 H3 H2).
      spliter.
      assert(CongA C A D B A D).
        eapply (l11_10  C A D C _ D).
          apply conga_refl.
            auto.
          auto.
          apply out_trivial.
          auto.
          apply out_trivial.
          auto.
          apply bet_out.
            auto.
          assumption.
        apply out_trivial.
        auto.
      eapply conga_preserves_lta.
        apply conga_sym.
        apply H9.
        apply conga_right_comm.
        apply conga_refl.
          intro.
          subst D.
          apply H5.
          apply col_trivial_3.
        auto.
      assumption.
    split.
      assumption.
    unfold Per in H.
    ex_and H B'.
    unfold Midpoint in H.
    spliter.
    assert(HH:= H8).
    assert(~Col B D B').
      intro.
      apply H5.
      apply (col_transitivity_1 _ B').
        intro.
        subst B'.
        apply between_identity in H.
        contradiction.
        apply (col_transitivity_1 _ C).
          assumption.
          apply bet_col.
          assumption.
        apply bet_col in H3.
        permut.
      permut.
    destruct(l11_44_1 B D B').
      assumption.
    apply H12 in H8.
    destruct(l11_44_2 A D B').
      intro.
      apply H10.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ A).
        intro.
        subst B'.
        apply between_symmetry in H3.
        assert(B = C).
          eapply (between_equality _ _ A); assumption.
        contradiction.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ C).
          assumption.
          apply bet_col.
          assumption.
        apply bet_col in H3.
        permut.
      permut.
    assert(LtA C A D C B' D).
      eapply conga_preserves_lta.
        apply conga_refl.
          auto.
        auto.
        apply conga_sym.
        eapply l11_10.
          3: apply out_trivial.
          apply conga_sym in H8.
          apply conga_comm in H8.
          apply H8.
          apply bet_out.
            intro.
            subst B'.
            apply cong_identity in H9.
            contradiction.
          apply between_symmetry.
          assumption.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
          apply bet_out.
            2: apply H.
            auto.
        apply out_trivial.
        intro.
        subst D.
        apply H10.
        apply col_trivial_1.
      assumption.
    assert(B' <> A).
      intro.
      subst B'.
      apply between_symmetry in H3.
      assert(B=C).
        eapply between_equality.
          apply H.
        assumption.
      contradiction.
    assert (Lt D B' D A).
      apply l11_44_2_b.
      apply (conga_preserves_lta D A C D B' C).
        eapply (l11_10).
          2: apply out_trivial.
          4: apply out_trivial.
          apply conga_refl.
            auto.
          5:apply out_trivial.
          assumption.
          auto.
          apply bet_out.
            auto.
          eapply outer_transitivity_between2.
            apply H3.
            assumption.
          assumption.
          auto.
        auto.
        eapply (l11_10).
          2: apply out_trivial.
          4: apply out_trivial.
          apply conga_refl.
            intro.
            subst B'.
            apply H10.
            apply col_trivial_2.
          5:apply out_trivial.
          auto.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
          apply bet_out.
            intro.
            subst B'.
            apply cong_identity in H9.
            contradiction.
            auto.
          eapply outer_transitivity_between.
            apply between_symmetry.
            apply H.
            apply between_symmetry.
            assumption.
          auto.
          intro.
          subst B'.
          apply H10.
          apply col_trivial_2.
        auto.
      apply lta_comm.
      assumption.
    unfold Lt in H17.
    spliter.
    unfold Lt.
    split.
      eapply l5_6.
      repeat split.
        apply H17.
        cong.
      apply cong_pseudo_reflexivity.
    intro.
    apply H18.
    eapply cong_transitivity.
      apply cong_symmetry.
      apply HH.
    apply cong_commutativity.
    assumption.
Qed.

(** This is SSA congruence with an obtuse angle *)

Lemma cong2_conga_obtuse__cong_conga2 :
forall A B C A' B' C',
       Obtuse A B C ->
       CongA A B C A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A' /\ CongA B A C B' A' C' /\ CongA B C A B' C' A'.
Proof.
intros.
apply (l11_52 A B C A' B' C'); auto.
destruct (col_dec A B C).
  apply bet__le2313, col_obtuse__bet; assumption.
assert_diffs; apply l11_46; auto.
Qed.

(** This is SSA congruence with a right angle *)

Lemma cong2_per2__cong_conga2 :
forall A B C A' B' C',
       A<>B -> B<>C ->
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A' /\ CongA B A C B' A' C' /\ CongA B C A B' C' A'.
Proof.
intros.
assert_diffs.
destruct (l11_46 A B C) as [_ []]; auto using per_not_col.
apply (l11_52 A B C A' B' C');auto.
apply l11_16;auto.
intro.
subst B'.
apply H9, cong_transitivity with A' C'; Cong.
Qed.

Lemma cong2_per2__cong :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong B A B' A'.
Proof.
intros.
destruct (eq_dec_points B C).
  treat_equalities; Cong.
destruct (eq_dec_points A B).
  destruct (eq_dec_points A' B'); subst; [Cong|].
  assert_diffs.
  destruct (cong2_per2__cong_conga2 A' B' C' B B C); Cong; Perp.
apply cong2_per2__cong_conga2 with C C'; auto.
Qed.

Lemma cong2_per2__cong_3 :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A C A' C' ->
       Cong B C B' C' ->
       Cong_3 A B C A' B' C'.
Proof.
intros.
unfold Cong_3.
assert (Cong B A B' A') by
 (apply (cong2_per2__cong A B C A' B' C');auto).
repeat split;Cong.
Qed.

Lemma cong_lt_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (eq_dec_points A B).
  treat_equalities; auto.
destruct (eq_dec_points B C).
  subst C.
  apply (cong2_lt__lt B' A' C' A'); Cong.
  assert_diffs.
  apply l11_46; Perp.
destruct H2 as [[C0 []] HNCong].
assert_diffs.
assert (Per A' B' C0) by (apply per_col with C'; Col).
apply (cong2_lt__lt A' C0 A' C'); [|apply l10_12 with B' B|]; Cong.
apply lt_comm.
destruct (l11_53 C' C0 B' A'); Between.
intro; subst; auto.
Qed.

Lemma cong_le_per2__le :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Cong A B A' B' ->
       Le B C B' C' ->
       Le A C A' C'.
Proof.
intros.
destruct (cong_dec B C B' C').
  apply cong__le, l10_12 with B B'; assumption.
assert (Lt B C B' C') by (split; assumption).
apply lt__le, cong_lt_per2__lt with B B'; assumption.
Qed.

Lemma lt2_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Lt A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (eq_dec_points B C).
  subst C.
  apply lt_transitivity with A' B'; auto.
  assert_diffs.
  apply lt_comm, l11_46; Perp.
apply lt_comm in H1.
assert (HC0 := H2).
destruct HC0 as [[C0 []] HNCong].
assert (Per A' B' C0).
  assert_diffs; apply per_col with C'; Col.
apply lt_transitivity with A' C0.
  apply lt_comm, cong_lt_per2__lt with B B'; Cong; Perp.
apply cong_lt_per2__lt with B' B'; Cong.
apply (cong2_lt__lt B C B' C'); Cong.
Qed.

Lemma le_lt_per2__lt :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Le A B A' B' ->
       Lt B C B' C' ->
       Lt A C A' C'.
Proof.
intros.
destruct (cong_dec A B A' B').
  apply cong_lt_per2__lt with B B'; assumption.
assert (Lt A B A' B') by (split; assumption).
apply lt2_per2__lt with B B'; assumption.
Qed.

Lemma le2_per2__le :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Le A B A' B' ->
       Le B C B' C' ->
       Le A C A' C'.
Proof.
intros.
destruct (cong_dec B C B' C').
  apply le_comm, cong_le_per2__le with B B'; finish.
assert (Lt B C B' C') by (split; assumption).
apply le_lt_per2__lt with B B'; assumption.
Qed.

Lemma cong_lt_per2__lt_1 :
forall A B C A' B' C',
       Per A B C ->
       Per A' B' C' ->
       Lt A B A' B' ->
       Cong A C A' C' ->
       Lt B' C' B C.
Proof.
intros.
apply nle__lt.
intro.
destruct (le_lt_per2__lt C B A C' B' A'); finish.
Qed.

Lemma symmetry_preserves_conga :
 forall A B C A' B' C' M, A <> B -> C <> B ->
  Midpoint M A A' ->
  Midpoint M B B' ->
  Midpoint M C C' ->
  CongA A B C A' B' C'.
Proof.
  intros.
  assert(Cong A B A' B').
    apply (l7_13 M); Midpoint.
  assert(Cong B C B' C').
    apply (l7_13 M); Midpoint.
  assert(Cong A C A' C').
    apply (l7_13 M); Midpoint.
  apply cong3_conga; auto.
  repeat split; Cong.
Qed.

Lemma l11_57 : forall A B C A' B' C',
  OS A A' B B' -> Per B A A' -> Per B' A' A ->
  OS A A' C C' -> Per C A A' -> Per C' A' A ->
  CongA B A C B' A' C'.
Proof.
  intros A B C A' B' C' HOSB HPer1 HPer2 HOSC HPer3 HPer4.
  destruct (midpoint_existence A A') as [M HM].
  destruct (symmetric_point_construction B M) as [B'' HB''].
  destruct (symmetric_point_construction C M) as [C'' HC''].
  assert (HNColB := one_side_not_col123 A A' B B' HOSB).
  assert (HNColC := one_side_not_col123 A A' C C' HOSC).
  apply conga_trans with B'' A' C''.
    assert_diffs; apply symmetry_preserves_conga with M; auto.
  assert (~ Col B'' A A').
    assert (B <> M) by (intro; subst; apply HNColB; Col); intro; apply HNColB; ColR.
  assert (Bet B'' A' B').
  { assert (Col B' B'' A').
    { assert_diffs; apply (cop_per2__col A); auto.
        apply coplanar_perm_3, coplanar_trans_1 with B; [Col|Cop|].
        exists M; right; right; split; Col.
      apply midpoint_preserves_per with B A A' M; Midpoint.
    }
    apply col_two_sides_bet with A; Col.
    apply invert_two_sides, l9_2, l9_8_2 with B; trivial.
    repeat split; Col.
    exists M; split; [Col|Between].
  }
  assert (~ Col C'' A A').
    assert (C <> M) by (intro; subst; apply HNColC; Col); intro; apply HNColC; ColR.
  assert (Bet C'' A' C').
  { assert (Col C' C'' A').
    { assert_diffs; apply (cop_per2__col A); auto.
        apply coplanar_perm_3, coplanar_trans_1 with C; [Col|Cop|].
        exists M; right; right; split; Col.
      apply midpoint_preserves_per with C A A' M; Midpoint.
    }
    apply col_two_sides_bet with A; Col.
    apply invert_two_sides, l9_2, l9_8_2 with C; trivial.
    repeat split; Col.
    exists M; split; [Col|Between].
  }
  apply one_side_not_col124 in HOSB.
  apply one_side_not_col124 in HOSC.
  assert_diffs; apply l11_14; auto.
Qed.

Lemma cop3_orth_at__orth_at : forall A B C D E F U V X, ~ Col D E F ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar A B C F -> Orth_at X A B C U V ->
  Orth_at X D E F U V.
Proof.
  intros A B C D E F U V X HNCol HD HE HF [HNCol1 [HUV [HX1 [HX2 HX3]]]].
  repeat split; trivial.
    apply coplanar_pseudo_trans with A B C; assumption.
  assert (forall M, Coplanar A B C M -> Coplanar D E F M).
    intro; apply coplanar_pseudo_trans; Cop.
  assert (forall M, Coplanar D E F M -> Coplanar A B C M).
    intro; apply coplanar_pseudo_trans; Cop.
  intros; apply HX3; auto.
Qed.

Lemma col2_orth_at__orth_at : forall A B C P Q U V X, U <> V ->
  Col P Q U -> Col P Q V -> Orth_at X A B C P Q -> Orth_at X A B C U V.
Proof.
  intros A B C P Q U V X HUV HU HV [HNCol [HPQ [HX1 [HX2 HX3]]]].
  repeat split; trivial.
    apply (col3 P Q); auto.
  intros D W HD HW.
  apply HX3; [|apply (colx U V)]; assumption.
Qed.

Lemma col_orth_at__orth_at : forall A B C U V W X, U <> W ->
  Col U V W -> Orth_at X A B C U V -> Orth_at X A B C U W.
Proof.
  intros A B C U V W X HUW HCol HX.
  apply col2_orth_at__orth_at with U V; Col.
Qed.

Lemma orth_at_symmetry : forall A B C U V X,
  Orth_at X A B C U V -> Orth_at X A B C V U.
Proof.
  unfold Orth_at.
  intros A B C U V X HX; spliter.
  repeat split; Col.
Qed.

Lemma orth_at_distincts : forall A B C U V X, Orth_at X A B C U V ->
  A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
  unfold Orth_at; intros; spliter; assert_diffs.
  repeat split; auto.
Qed.

Lemma orth_at_chara : forall A B C P X, Orth_at X A B C X P <->
  ~ Col A B C /\ X <> P /\ Coplanar A B C X /\ (forall D, Coplanar A B C D -> Per D X P).
Proof.
  intros A B C P X; split.
  - unfold Orth_at; intro; spliter.
    repeat split; Col.
  - intro; spliter.
    repeat split; Col.
    intros; apply per_col with P; auto.
Qed.

Lemma cop3_orth__orth : forall A B C D E F U V, ~ Col D E F ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar A B C F -> Orth A B C U V ->
  Orth D E F U V.
Proof.
  intros A B C D E F U V HNCol HD HE HF [X HX].
  exists X.
  apply (cop3_orth_at__orth_at A B C); assumption.
Qed.

Lemma col2_orth__orth : forall A B C P Q U V, U <> V ->
  Col P Q U -> Col P Q V -> Orth A B C P Q -> Orth A B C U V.
Proof.
  intros A B C P Q U V HUV HU HV [X HX].
  exists X.
  apply col2_orth_at__orth_at with P Q; assumption.
Qed.

Lemma col_orth__orth : forall A B C U V W, U <> W ->
  Col U V W -> Orth A B C U V -> Orth A B C U W.
Proof.
  intros A B C U V W HUW HCol HOrth.
  apply col2_orth__orth with U V; Col.
Qed.

Lemma orth_symmetry : forall A B C U V,
  Orth A B C U V -> Orth A B C V U.
Proof.
  intros A B C U V [X HX].
  exists X.
  apply orth_at_symmetry, HX.
Qed.

Lemma orth_distincts : forall A B C U V, Orth A B C U V ->
  A <> B /\ B <> C /\ A <> C /\ U <> V.
Proof.
  intros A B C U V [X HX].
  apply orth_at_distincts with X, HX.
Qed.

Lemma col_cop_orth__orth_at : forall A B C U V X,
  Orth A B C U V -> Coplanar A B C X -> Col U V X -> Orth_at X A B C U V.
Proof.
  intros A B C U V X [Y [HNCol [HUV [HY1 [HY2 HY3]]]]] HX1 HX2.
  repeat split; trivial.
  replace X with Y; [assumption|].
  apply eq_sym, l8_8; auto.
Qed.

Lemma l11_60_aux : forall A B C D P Q, ~ Col A B C ->
  Cong A P A Q -> Cong B P B Q -> Cong C P C Q -> Coplanar A B C D ->
  Cong D P D Q.
Proof.
  intros A B C D P Q HNCol HA HB HC HCop.
  destruct (midpoint_existence P Q) as [M []].
  assert_diffs; destruct HCop as [X [|[|]]]; spliter.
  - apply l4_17 with C X; Col.
      intro; subst; apply HNCol; assumption.
    apply l4_17 with A B; auto.
  - apply l4_17 with B X; Col.
      intro; subst; apply HNCol; Col.
    apply l4_17 with A C; auto.
  - apply l4_17 with A X; Col.
      intro; subst; apply HNCol; Col.
    apply l4_17 with B C; auto.
Qed.

Lemma l11_60 : forall A B C D E P, ~ Col A B C ->
  Per A D P -> Per B D P -> Per C D P -> Coplanar A B C E ->
  Per E D P.
Proof.
  intros A B C D E P HNCol HPerA HPerB HPerC HCop.
  destruct (eq_dec_points D P).
    subst; apply l8_5.
  destruct (symmetric_point_construction P D) as [P'].
  exists P'; split; auto.
  apply (l11_60_aux A B C); [|apply per_double_cong with D..|]; assumption.
Qed.

Lemma l11_60_bis : forall A B C D P, ~ Col A B C -> D <> P ->
  Coplanar A B C D -> Per A D P -> Per B D P -> Per C D P ->
  Orth_at D A B C D P.
Proof.
  intros A B C D P HNCol HDP HD HA HB HC.
  repeat split; Col.
  intros E Q HE HQ.
  apply per_col with P; auto.
  apply (l11_60 A B C); assumption.
Qed.

Lemma l11_61 : forall A B C A' B' C',
  A <> A' -> A <> B -> A <> C ->
  Coplanar A A' B B' -> Per B A A' -> Per B' A' A ->
  Coplanar A A' C C' -> Per C A A' ->
  Per B A C -> Per B' A' C'.
Proof.
  intros A B C A' B' C'; intros.
  assert (~ Col C A A') by (assert_diffs; apply per_not_col; auto).
  destruct (l10_15 A A' A' C) as [C'' []]; Col.
  assert_diffs.
  apply l8_2, (l11_60 A' A C'');
    [apply one_side_not_col124 with C; Side|Perp..| |apply coplanar_trans_1 with C; Col; Cop].
  apply l8_2.
  revert dependent B'.
  assert (Haux : forall B', OS A A' B B' -> Per B' A' A -> Per B' A' C'').
  { intros B' HOS HPer.
    apply (l11_17 B A C); trivial.
    apply l11_57; Perp.
  }
  intro B'; intros.
  destruct (eq_dec_points B' A'); [subst; Perp|].
  assert (HNCol : ~ Col B' A' A) by (apply per_not_col; auto).
  destruct (cop__one_or_two_sides A A' B B'); Col.
    apply per_not_col; auto.
  destruct (segment_construction B' A' A' B') as [B'' []].
  assert_diffs.
  apply l8_2, per_col with B''; Col.
  apply l8_2, Haux; [|apply l8_2, per_col with B'; Perp; Col].
  exists B'; split; trivial.
  repeat split; Col.
    intro; apply HNCol; ColR.
  exists A'; split; Col; Between.
Qed.

Lemma l11_61_bis : forall A B C D E P Q,
  Orth_at D A B C D P -> Perp D E E Q -> Coplanar A B C E -> Coplanar D E P Q ->
  Orth_at E A B C E Q.
Proof.
  intros A B C D E P Q [HNCol [HDP [HD [_ HOrth]]]] HPerp HE HCop.
  assert_diffs.
  repeat split; Col.
  assert (Haux : forall M, Coplanar A B C M -> Per M E Q).
  { intros M HM.
    assert (HD' : exists D', Perp D E D' D /\ Coplanar A B C D').
    { destruct (ex_ncol_cop A B C D E) as [F []]; auto.
      destruct (ex_perp_cop D E D F) as [D' []]; auto.
      exists D'; split; auto.
      apply coplanar_pseudo_trans with D E F; trivial;
      apply coplanar_pseudo_trans with A B C; Cop.
    }
    destruct HD' as [D' []].
    assert_diffs.
    apply l8_2, (l11_61 D P D'); auto.
      apply l8_2; Col.
      Perp.
      apply coplanar_pseudo_trans with A B C; assumption.
      Perp.
      apply l8_2; Col.
  }
  intros; apply per_col with Q; Cop.
Qed.

Lemma l11_62_unicity : forall A B C D D' P,
  Coplanar A B C D -> Coplanar A B C D' ->
  (forall E, Coplanar A B C E -> Per E D P) ->
  (forall E, Coplanar A B C E -> Per E D' P) ->
  D = D'.
Proof.
  intros A B C D D' P HCop HCop' HD HD'.
  apply l8_7 with P; Perp.
Qed.

Lemma l11_62_unicity_bis : forall A B C U X Y,
  Orth_at X A B C X U -> Orth_at Y A B C Y U -> X = Y.
Proof.
  unfold Orth_at.
  intros A B C U X Y HX HY.
  spliter.
  apply l11_62_unicity with A B C U; trivial; intros; Col.
Qed.

Lemma orth_at2__eq : forall A B C U V X Y,
  Orth_at X A B C U V -> Orth_at Y A B C U V -> X = Y.
Proof.
  unfold Orth_at.
  intros A B C U V X Y HX HY.
  spliter.
  apply l11_62_unicity with A B C U; trivial; intros; Col.
Qed.

Lemma col_cop_orth_at__eq : forall A B C U V X Y,
  Orth_at X A B C U V -> Coplanar A B C Y -> Col U V Y -> X = Y.
Proof.
  intros A B C U V X Y HOrth HCop HCol.
  apply (orth_at2__eq A B C U V); [assumption|].
  apply col_cop_orth__orth_at; [exists X|..]; assumption.
Qed.

Lemma orth_at__ncop1 : forall A B C U V X, U <> X ->
  Orth_at X A B C U V -> ~ Coplanar A B C U.
Proof.
  intros A B C U V X HUX HOrth HCop.
  apply HUX, eq_sym, (col_cop_orth_at__eq A B C U V); Col.
Qed.

Lemma orth_at__ncop2 : forall A B C U V X, V <> X ->
  Orth_at X A B C U V -> ~ Coplanar A B C V.
Proof.
  intros A B C U V X HUX HOrth.
  apply orth_at__ncop1 with U X; [assumption|apply orth_at_symmetry, HOrth].
Qed.

Lemma orth_at__ncop : forall A B C P X,
  Orth_at X A B C X P -> ~ Coplanar A B C P.
Proof.
  intros A B C P X HOrth.
  assert (Hd := HOrth); apply orth_at_distincts in Hd; spliter.
  apply orth_at__ncop2 with X X; auto.
Qed.

Lemma l11_62_existence : forall A B C P, exists D,
  Coplanar A B C D /\ forall E, Coplanar A B C E -> Per E D P.
Proof.
  intros A B C P.
  destruct (cop_dec A B C P) as [|HNCop].
    exists P; split; [assumption|intros; Perp].
  assert (HNCol : ~ Col A B C) by (apply ncop__ncol with P, HNCop).
  destruct (l8_18_existence A B P) as [D0 [HCol0 HPerp0]].
    intro; apply HNCop; exists P; left; split; Col.
  assert (HCop0 : Coplanar A B C D0) by (exists D0; left; split; Col).
  assert_diffs.
  destruct (ex_perp_cop A B D0 C) as [D1 [HPerp1 HCop1]]; auto.
  destruct (perp_not_col2 A B D1 D0 HPerp1) as [HNCol1|]; [|exfalso; Col].
  assert (Haux : forall D, Col D0 D1 D -> Coplanar A B C D).
  { intros D HD.
    apply coplanar_trans_1 with D1; [Col|Cop|].
    assert_diffs; apply coplanar_perm_12, col_cop__cop with D0; Col; Cop.
  }
  destruct (diff_col_ex3 A B D0 HCol0) as [A0].
  spliter.
  assert (HCopA : Coplanar A B C A0) by (exists A0; left; split; Col).
  assert (Per P D0 A0) by (destruct (l8_16_1 A B P A0 D0); auto).
  destruct (per_dec P D0 D1) as [|HNPer].
  { exists D0.
    split; Col.
    intros E HE.
    apply l11_60 with A0 D1 D0; Perp.
      intro; apply HNCol1; ColR.
    apply coplanar_pseudo_trans with A B C; trivial.
  }
  destruct (l8_18_existence D0 D1 P) as [D []]; Col.
    intro Habs; apply HNCop, Haux, Habs.
  exists D; split; auto.
  intros E HE.
  assert (D <> D0) by (intro; subst; apply HNPer; Perp).
  assert (HPer : Per D0 D P) by (apply perp_per_1, perp_left_comm, perp_col with D1; auto).
  assert (HPer1 : Per D D0 A0).
    assert_diffs; apply l8_2, per_col with D1; auto; destruct (l8_16_1 A B D1 A0 D0); Perp.
  apply l11_60 with D0 A0 D; Perp; [apply per_not_col in HPer1; Col|..].
  { destruct (symmetric_point_construction A0 D) as [A0'].
    apply l8_2; exists A0'; split; trivial.
    destruct (symmetric_point_construction D0 D) as [D0'].
    apply l10_12 with D0 D0';
    [..|apply per_double_cong with D|apply cong_symmetry, l7_13 with D]; Perp.
    destruct (symmetric_point_construction P D) as [P'].
    apply midpoint_preserves_per with P' D0 A0 D; Midpoint.
    apply l11_60 with P D D0; Perp; [|exists P'; left; split; Col].
    intro; apply HNCop, coplanar_trans_1 with D1; Col; [Cop|].
    exists D0; right; right; split; ColR.
  }
  apply coplanar_pseudo_trans with A B C; trivial.
  apply coplanar_trans_1 with D1; Col.
    Cop.
  exists D0; right; right; split; Col.
Qed.

Lemma l11_62_existence_bis : forall A B C P, ~ Coplanar A B C P ->
  exists X, Orth_at X A B C X P.
Proof.
  intros A B C P HNCop.
  destruct (l11_62_existence A B C P) as [X [HCop HX]].
  assert (X <> P) by (intro; subst; apply (HNCop HCop)).
  exists X; repeat split; Col.
    apply ncop__ncol with P, HNCop.
  intros D Q HD HQ.
  apply per_col with P; auto.
Qed.

Lemma l11_63_aux : forall A B C D E P,
  Coplanar A B C D -> D <> E -> Orth_at E A B C E P ->
  exists Q, OS D E P Q /\ Orth A B C D Q.
Proof.
  intros A B C D E P HD HDE HOrth.
  assert (H' := HOrth).
  destruct H' as [HNCol [HEP [HE1 [_ HE2]]]].
  assert (HNCop : ~ Coplanar A B C P).
    intro; apply HEP, (col_cop_orth_at__eq A B C E P); Col.
  destruct (l10_15 D E D P) as [Q [HQ1 HQ2]]; Col.
    intro; apply HNCop, col_cop2__cop with D E; auto.
  exists Q.
  split; [assumption|].
  destruct (ex_ncol_cop A B C D E HDE) as [F [HF1 HF2]].
  destruct (ex_perp_cop D E D F) as [D' [HD'1 HD'2]]; auto.
  assert (~ Col D' D E) by (assert_diffs; apply per_not_col; Perp).
  assert (Coplanar D E F A) by (apply coplanar_pseudo_trans with A B C; Cop).
  assert (Coplanar D E F B) by (apply coplanar_pseudo_trans with A B C; Cop).
  assert (Coplanar D E F C) by (apply coplanar_pseudo_trans with A B C; Cop).
  exists D.
  apply (cop3_orth_at__orth_at D' D E);
    [assumption|apply coplanar_pseudo_trans with D E F; Cop..|].
  assert_diffs.
  apply l11_60_bis; Cop; [|Perp..].
  destruct (ex_perp_cop D E E F) as [E' [HE'1 HE'2]]; auto.
  assert_diffs.
  apply (l11_61 E E' P); Perp.
    apply coplanar_trans_1 with F; Col; Cop.
    apply os__coplanar in HQ2; Cop.
    apply l8_2, HE2; Col.
    apply HE2; Col; apply coplanar_pseudo_trans with D E F; assumption.
Qed.

Lemma l11_63_existence : forall A B C D P,
  Coplanar A B C D -> ~ Coplanar A B C P ->
  exists Q, Orth A B C D Q.
Proof.
  intros A B C D P HCop HNCop.
  destruct (l11_62_existence_bis A B C P HNCop) as [E HE].
  destruct (eq_dec_points D E).
    exists P, D; subst; assumption.
  destruct (l11_63_aux A B C D E P) as [Q []]; auto.
  exists Q; assumption.
Qed.

Lemma l8_21_3 : forall A B C D X, Coplanar A B C D -> ~ Coplanar A B C X ->
  exists P T, Orth A B C D P /\ Coplanar A B C T /\ Bet X T P.
Proof.
  intros A B C D X HD HX.
  destruct (l11_62_existence_bis A B C X HX) as [E HE].
  destruct (eq_dec_points D E).
  { subst E.
    destruct (segment_construction X D D X) as [Y []].
    exists Y, D; subst; repeat split; trivial.
    assert (D <> X) by (intro; subst; apply (HX HD)); assert_diffs.
    apply col_orth__orth with X; Col.
    exists D; assumption.
  }
  destruct (l11_63_aux A B C D E X) as [P' [HOS HP']]; auto.
  destruct HE as [HNCol [HEX [HE [_ HOrth]]]].
  assert (HOrth' : Orth_at D A B C D P') by (apply col_cop_orth__orth_at; Col).
  assert (HDP' : D <> P') by (apply orth_distincts in HP'; spliter; auto).
  assert (HNCop : ~ Coplanar A B C P').
    apply orth_at__ncop2 with D D; auto; apply col_cop_orth__orth_at; Col.
  destruct HOrth' as [_ [_ [_ [_ HOrth']]]].
  destruct (segment_construction P' D D P') as [P []].
  assert (HT : TS D E X P).
  { apply l9_8_2 with P'; [|Side].
    repeat split; [intro; apply HNCop, col_cop2__cop with D E; ColR..|exists D; split; Col].
  }
  destruct HT as [_ [_ [T []]]].
  exists P, T; repeat split; [|apply col_cop2__cop with D E; Col|assumption].
  assert_diffs.
  apply col_orth__orth with P'; Col.
Qed.

Lemma mid2_orth_at2__cong : forall A B C X Y P Q P' Q',
  Orth_at X A B C X P -> Orth_at Y A B C Y Q -> Midpoint X P P' -> Midpoint Y Q Q' ->
  Cong P Q P' Q'.
Proof.
  intros A B C X Y P Q P' Q' HX1 HY1 HX2 HY2.
  assert (HX3 := HX1).
  destruct HX3 as [HNCol [HXP [HCop1 [_ HX3]]]].
  assert (HY3 := HY1).
  destruct HY3 as [_ [HYQ [HCop2 [_ HY3]]]].
  destruct (midpoint_existence X Y) as [Z].
  destruct (symmetric_point_construction P Z) as [R].
  destruct (symmetric_point_construction P' Z) as [R'].
  assert (Coplanar A B C Z) by (apply bet_cop2__cop with X Y; Between).
  assert (Cong Z P Z P').
    apply per_double_cong with X; Col.
  apply five_segment with R R' Z Z; Between.
    apply cong_transitivity with P Z; [|apply cong_transitivity with P' Z]; Cong.
    apply cong_symmetry, l7_13 with Y; [apply symmetry_preserves_midpoint with P X P' Z|]; assumption.
    apply per_double_cong with Y; Col.
    intro; treat_equalities; auto.
Qed.

Lemma orth_at2_tsp__ts : forall A B C X Y P Q, P <> Q ->
  Orth_at P A B C P X -> Orth_at Q A B C Q Y -> TSP A B C X Y -> TS P Q X Y.
Proof.
  intros A B C X Y P Q HPQ HP HQ [HX [HY [T [HT HBet]]]].
  assert (HP1 := HP).
  apply orth_at_chara in HP1; spliter.
  assert (HQ1 := HQ).
  apply orth_at_chara in HQ1; spliter.
  repeat split.
    intro; apply HX, col_cop2__cop with P Q; Col.
    intro; apply HY, col_cop2__cop with P Q; Col.
  exists T; split; [|assumption].
  destruct (symmetric_point_construction X P) as [X'].
  destruct (symmetric_point_construction Y Q) as [Y'].
  assert (Cong T X T X') by (apply per_double_cong with P; auto).
  assert (Cong T Y T Y') by (apply per_double_cong with Q; auto).
  apply col_permutation_4, bet_col, l7_22 with X Y X' Y'; trivial.
  apply (l4_6 X T Y); repeat split; Cong.
  assert (~ Col A B C) by (apply ncop__ncol with X, HX).
  apply mid2_orth_at2__cong with A B C P Q; auto.
Qed.

Lemma orth_dec : forall A B C U V, Orth A B C U V \/ ~ Orth A B C U V.
Proof.
  intros A B C U V.
  destruct (eq_dec_points U V).
    unfold Orth, Orth_at; right; intros [X []]; spliter; auto.
  revert dependent V.
  revert U.
  assert (Haux : forall U V, U <> V -> ~ Coplanar A B C U -> Orth A B C U V \/ ~ Orth A B C U V).
  { intros U V HUV HU.
    destruct (l11_62_existence_bis A B C U HU) as [X HX].
    destruct (col_dec U V X).
      left; apply col_orth__orth with X; Col; apply orth_symmetry; exists X; apply HX.
    right; intros [Y HY].
    assert (X = Y).
    { apply l11_62_unicity_bis with A B C U; [assumption|].
      apply orth_at_symmetry, col_orth_at__orth_at with V; [destruct HY; spliter..|]; trivial.
      intro; subst Y; absurd (Coplanar A B C U); [|assumption].
      assert_diffs; apply orth_at__ncop2 with X X; auto.
    }
    subst; destruct HY; spliter; Col.
  }
  intros U V HUV.
  destruct (col_dec A B C).
    unfold Orth, Orth_at; right; intros [X []]; spliter; auto.
  destruct (cop_dec A B C U); [|auto].
  destruct (cop_dec A B C V).
  - right; intro.
    apply HUV, (orth_at2__eq A B C U V); apply col_cop_orth__orth_at; Col.
  - destruct (Haux V U) as [HOrth|HNOrth]; auto;
    [left|right; intro HOrth; apply HNOrth]; apply orth_symmetry, HOrth.
Qed.

Lemma orth_at_dec : forall A B C U V X, Orth_at X A B C U V \/ ~ Orth_at X A B C U V.
Proof.
  intros A B C U V X.
  destruct (orth_dec A B C U V) as [|HNOrth]; [|right; intro HX; apply HNOrth; exists X; apply HX].
  destruct (cop_dec A B C X); [|unfold Orth_at; right; intro; spliter; auto].
  destruct (col_dec U V X) as [HCol|]; [|unfold Orth_at; right; intro; spliter; auto].
  left; apply col_cop_orth__orth_at; assumption.
Qed.

Lemma tsp_dec : forall A B C X Y, TSP A B C X Y \/ ~ TSP A B C X Y.
Proof.
  intros A B C X Y.
  destruct (cop_dec A B C X) as [|HX].
    right; intros [Ha]; apply Ha; assumption.
  destruct (cop_dec A B C Y) as [|HY].
    right; intros [_ [Ha]]; apply Ha; assumption.
  destruct (l11_62_existence_bis A B C X HX) as [P HP].
  destruct (l11_62_existence_bis A B C Y HY) as [Q HQ].
  assert (HP1 := HP).
  apply orth_at_chara in HP1; spliter.
  assert (HQ1 := HQ).
  apply orth_at_chara in HQ1; spliter.
  destruct (eq_dec_points P Q).
  { subst Q; clear HQ; destruct (bet_dec X P Y) as [|HNBet].
      left; repeat split; trivial; exists P; split; trivial.
    right; intro HQ; apply HNBet.
    destruct HQ as [_ [_ [Q [HQ HBet]]]].
    replace P with Q; [assumption|].
    apply l8_8, (col_per2__per X Y); try (apply l8_2); Col.
    intro; treat_equalities; auto.
  }
  destruct (two_sides_dec P Q X Y) as [HT|HNTS].
    left; apply cop2_ts__tsp with P Q; assumption.
    right; intro; apply HNTS, (orth_at2_tsp__ts A B C); assumption.
Qed.

Lemma osp_dec : forall A B C X Y, OSP A B C X Y \/ ~ OSP A B C X Y.
Proof.
  intros A B C X Y.
  destruct (cop_dec A B C X) as [|HX].
    right; intros [X' [[Ha _] _]]; apply Ha; assumption.
  destruct (tsp_exists A B C X HX) as [X'].
  destruct (tsp_dec A B C Y X') as [|HNTS].
    left; exists X'; split; assumption.
    right; intro; apply HNTS; apply l9_41_2 with X; assumption.
Qed.

Lemma os_ts__inangle : forall A B C P, TS B P A C -> OS B A C P -> InAngle P A B C.
Proof.
  intros A B C P Hts Hos.
  assert(HNCol : ~ Col A B P) by (destruct Hts as []; Col).
  assert(~ Col B A C) by (apply (one_side_not_col123 _ _ _ P); auto).
  assert (HP' := symmetric_point_construction P B).
  destruct HP' as [P'].
  assert_diffs.
  assert(~ Col B A P') by (intro; apply HNCol; ColR).
  assert(HUn := two_sides_in_angle A B C P P').
  destruct HUn as [|Habs]; Between.
  exfalso.
  apply in_angle_one_side in Habs; Col.
  apply l9_9_bis in Habs.
  apply Habs.
  apply invert_two_sides; apply l9_2.
  apply (l9_8_2 _ _ P); Side.
  repeat split; Col; exists B; split; Col; Between.
Qed.

Lemma os2__inangle : forall A B C P, OS B A C P -> OS B C A P -> InAngle P A B C.
Proof.
  intros A B C P Hos1 Hos2.
  apply os_ts__inangle; auto.
  apply l9_31; Side.
Qed.

Lemma acute_conga__acute : forall A B C D E F, Acute A B C -> CongA A B C D E F -> Acute D E F.
Proof.
  intros A B C D E F Hacute HConga.
  apply (acute_lea_acute _ _ _ A B C); auto.
  apply conga__lea.
  apply conga_sym; assumption.
Qed.

Lemma acute_out2__acute : forall A B C A' C', Out B A' A -> Out B C' C -> Acute A B C ->
  Acute A' B C'.
Proof.
  intros A B C A' C' HA HC HB.
  apply (acute_conga__acute A B C).
    assumption.
  apply out2__conga; assumption.
Qed.

Lemma conga_obtuse__obtuse : forall A B C D E F, Obtuse A B C -> CongA A B C D E F -> Obtuse D E F.
Proof.
  intros A B C D E F Hobtuse HConga.
  apply (obtuse_gea_obtuse _ _ _ A B C); auto.
  apply conga__lea; assumption.
Qed.

Lemma obtuse_out2__obtuse : forall A B C A' C', Out B A' A -> Out B C' C -> Obtuse A B C ->
  Obtuse A' B C'.
Proof.
  intros A B C A' C' HA HC HB.
  apply (conga_obtuse__obtuse A B C).
    assumption.
  apply out2__conga; assumption.
Qed.

Lemma bet_lea__bet : forall A B C D E F, Bet A B C -> LeA A B C D E F -> Bet D E F.
Proof.
  intros A B C D E F HBet Hlea.
  apply (bet_conga__bet A B C); auto.
  apply lea_asym; auto.
  apply lea_distincts in Hlea.
  spliter.
  apply l11_31_2; auto.
Qed.

Lemma out_lea__out : forall A B C D E F, Out E D F -> LeA A B C D E F -> Out B A C.
Proof.
  intros A B C D E F Hout Hlea.
  apply (l11_21_a D E F); auto.
  apply lea_asym; auto.
  apply lea_distincts in Hlea.
  spliter.
  apply l11_31_1; auto.
Qed.


Lemma bet2_lta__lta : forall A B C D E F A' D',
  LtA A B C D E F -> Bet A B A' -> A' <> B -> Bet D E D' -> D' <> E ->
  LtA D' E F A' B C.
Proof.
  intros A B C D E F A' D' Hlta.
  intros.
  assert (Hd := Hlta).
  apply lta_distincts in Hd.
  unfold LtA in *.
  spliter.
  split.
  apply (l11_36 A _ _ D); auto.
  intro.
  assert(CongA A B C D E F); auto.
  apply (l11_13 A' _ _ D'); try (apply conga_sym); Between.
Qed.


Lemma lta__lea : forall A B C D E F, LtA A B C D E F -> LeA A B C D E F.
Proof.
  intros.
  destruct H.
  assumption.
Qed.

Lemma lea123456_lta__lta : forall A B C D E F G H I, LeA A B C D E F -> LtA D E F G H I ->
   LtA A B C G H I.
Proof.
  intros A B C D E F G H I Hlea Hlta.
  split.
  - apply (lea_trans _ _ _ D E F).
    assumption.
    apply lta__lea; assumption.
  - intro.
    destruct Hlta as [Hlea' HNConga].
    apply HNConga.
    apply lea_asym.
    assumption.
    apply (l11_30 A B C D E F); auto.
    apply lea_distincts in Hlea.
    spliter.
    apply conga_refl; assumption.
Qed.

Lemma lea456789_lta__lta : forall A B C D E F G H I, LtA A B C D E F -> LeA D E F G H I ->
   LtA A B C G H I.
Proof.
  intros A B C D E F G H I Hlta Hlea.
  split.
  - apply (lea_trans _ _ _ D E F).
    apply lta__lea; assumption.
    assumption.
  - intro.
    destruct Hlta as [Hlea' HNConga].
    apply HNConga.
    apply lea_asym.
    assumption.
    apply (l11_30 D E F G H I); auto.
    2: apply conga_sym; assumption.
    apply lea_distincts in Hlea.
    spliter.
    apply conga_refl; assumption.
Qed.

Lemma acute_per__lta : forall A B C D E F, Acute A B C -> D <> E -> E <> F -> Per D E F ->
   LtA A B C D E F.
Proof.
  intros A B C D E F Hacute HDE HEF HPer.
  intros.
  destruct Hacute as [G [H [I [HPer2 Hlta]]]].
  assert(Hdiff := lta_distincts A B C G H I Hlta).
  spliter.
  apply (conga_preserves_lta A B C G H I); try (apply conga_refl); auto.
  apply l11_16; auto.
Qed.

Lemma obtuse_per__lta : forall A B C D E F, Obtuse A B C -> D <> E -> E <> F -> Per D E F ->
   LtA D E F A B C.
Proof.
  intros A B C D E F Hobtuse HDE HEF HPer.
  intros.
  destruct Hobtuse as [G [H [I [HPer2 Hgta]]]].
  assert(Hdiff := gta_distincts A B C G H I Hgta).
  spliter.
  apply (conga_preserves_lta G H I A B C); try (apply conga_refl); auto.
  apply l11_16; auto.
Qed.

Lemma acute_obtuse__lta : forall A B C D E F, Acute A B C -> Obtuse D E F -> LtA A B C D E F.
Proof.
  intros A B C D E F Hacute Hobtuse.
  destruct Hacute as [G [H [I [HPer Hlta]]]].
  apply (lta_trans _ _ _ G H I); auto.
  apply lta_distincts in Hlta.
  spliter.
  apply obtuse_per__lta; auto.
Qed.

Lemma lea_in_angle : forall A B C P, LeA A B P A B C -> OS A B C P ->
   InAngle P A B C.
Proof.
    intros.
    assert(H1 := H0).
    clear H0.
    assert(H0 : CongA A B P A B P).
    { assert(~ Col A B P) by (apply (one_side_not_col123 _ _ _ C); Side).
      assert_diffs.
      apply conga_refl; auto.
    }
    unfold LeA in H.
    ex_and H T.
    eapply conga_preserves_in_angle.
      3: apply H.
      apply conga_refl.
        assert(HH0:=H0).
        unfold CongA in HH0.
        spliter.
        clear H6.
        repeat split; auto.
      intro.
      subst C.
      unfold OS in H1.
      ex_and H1 X.
      unfold TS in H1.
      spliter.
      apply H1.
      Col.
      eapply conga_trans; apply conga_sym.
        apply H2.
      apply H0.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma acute_bet__obtuse : forall A B C A', Bet A B A' -> A' <> B -> Acute A B C -> Obtuse A' B C.
Proof.
  intros A B C A' HBet HA'B Hacute.
  assert(Hd := acute_distincts A B C Hacute).
  destruct Hd.
  elim(col_dec A B C).
  { intro.
    elim(bet_dec A B C).
    - intro.
      exfalso.
      assert(Hlta : LtA A B C A B C) by (apply acute_obtuse__lta; auto; apply bet__obtuse; auto).
      destruct Hlta as [_ HNConga].
      apply HNConga.
      apply conga_refl; auto.

    - intro.
      apply bet__obtuse; auto.
      apply between_symmetry.
      apply (l6_2 A); auto.
      apply not_bet_out; auto.
  }
  intro HNCol1.
  assert(HD := l10_15 A B B C).
  destruct HD as [D []]; Col.
  assert_diffs.
  assert(HNCol2 : ~ Col C B D).
  { intro.
    assert(Hlta : LtA A B C A B C).
    2: destruct Hlta as [_ HNConga]; apply HNConga; apply conga_refl; auto.
    apply acute_per__lta; auto.
    apply (per_col _ _ D); Perp; Col.
  }
  assert(OS B A' C D) by (apply (col_one_side _ A); Side; Col).
  exists A.
  exists B.
  exists D.
  split; Perp.
  split.
  - exists D.
    split.
    2: apply conga_comm; apply l11_18_1; Perp.
    apply os2__inangle; auto.
    exists A.
    split.
    { repeat split; Col.
      intro; apply HNCol1; ColR.
      exists B; Col; Between.
    }
    apply invert_two_sides.
    apply in_angle_two_sides; Col.
    apply l11_24.
    apply lea_in_angle; try (apply conga_refl); Side.
    apply lta__lea.
    apply acute_per__lta; Perp.

  - intro.
    apply HNCol2.
    assert(HUn := conga_cop__or_out_ts A' B D C).
    destruct HUn.
      Cop.
      apply (conga_trans _ _ _ A B D); auto.
      apply l11_16; auto; apply (l8_3 A); Perp; Col.
      assert_cols; Col.
    exfalso; assert(~ TS A' B D C); auto; apply l9_9_bis; Side.
Qed.

Lemma bet_obtuse__acute : forall A B C A', Bet A B A' -> A' <> B -> Obtuse A B C -> Acute A' B C.
Proof.
  intros A B C A' HBet HA'B Hobtuse.
  assert(Hd := obtuse_distincts A B C Hobtuse).
  spliter.
  elim(col_dec A B C).
  { intro.
    elim(bet_dec A B C).
    - intro.
      apply out__acute.
      apply (l6_2 _ _ A); Between.

    - intro.
      exfalso.
      assert(Hlta : LtA A B C A B C).
      2: destruct Hlta as [_ HNConga]; apply HNConga; apply conga_refl; auto.
      apply acute_obtuse__lta; auto.
      apply out__acute.
      apply not_bet_out; auto.
  }
  intro HNCol1.
  assert(HD := l10_15 A B B C).
  destruct HD as [D []]; Col.
  assert_diffs.
  assert(HNCol2 : ~ Col C B D).
  { intro.
    assert(Hlta : LtA A B C A B C).
    2: destruct Hlta as [_ HNConga]; apply HNConga; apply conga_refl; auto.
    apply obtuse_per__lta; auto.
    apply (per_col _ _ D); Perp; Col.
  }
  assert(OS B A' C D) by (apply (col_one_side _ A); Side; Col).
  assert(~ Col A B D) by (apply per_not_col; Perp).
  exists A'.
  exists B.
  exists D.
  split.
  apply (l8_3 A); Perp; Col.
  split.
  - exists C.
    split; try (apply conga_refl); auto.
    apply os2__inangle; Side.
    exists A.
    split.
    { repeat split; auto.
      apply (one_side_not_col123 _ _ _ C); Side.
      exists B; Col; Between.
    }
    apply invert_two_sides.
    apply in_angle_two_sides; Col.
    apply l11_24.
    apply lea_in_angle; try (apply conga_refl); auto.
    apply lta__lea.
    apply obtuse_per__lta; Perp.

  - intro Habs.
    apply HNCol2.
    assert (HCop : Coplanar A' B C D) by Cop.
    assert(HUn := conga_cop__or_out_ts A' B C D HCop Habs).
    destruct HUn.
    assert_cols; Col.
    exfalso; assert(~ TS A' B C D); auto; apply l9_9_bis; Side.
Qed.


Lemma inangle_dec : forall A B C P, InAngle P A B C \/ ~ InAngle P A B C.
Proof.
  intros A B C P.
  elim(cop_dec A B C P).
  { intro HCop.
    elim(eq_dec_points A B).
      intro; subst; right; unfold InAngle; intro; spliter; auto.
    intro.
    elim(eq_dec_points C B).
      intro; subst; right; unfold InAngle; intro; spliter; auto.
    intro.
    elim(eq_dec_points P B).
      intro; subst; right; unfold InAngle; intro; spliter; auto.
    intro.
    elim(col_dec A B C).
    { intro HColB.
      elim(bet_dec A B C).
      { intro HBBet.
        left.
        repeat split; auto.
        exists B.
        split; auto.
      }
      intro HBNBet.
      elim(out_dec B A P).
      { left.
        repeat split; auto.
        exists A; Between.
      }
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      destruct HUn as [|HoutBXP].
        subst; auto.
      assert(HInter := out2_bet_out A B C X P); auto.
      destruct HInter; auto.
      apply not_bet_out; auto.
    }
    intro HNColB.
    assert(HP' := symmetric_point_construction P B).
    destruct HP' as [P'].
    assert_diffs.
    elim(two_sides_dec B P A C).
    { intro.
      assert(HUn := two_sides_in_angle A B C P P').
      destruct HUn as [HInAngle|HInAngle]; Between.
      - destruct HInAngle as [_ [_ [_ [X [HXBet HUn]]]]].
        destruct HUn as [HXB|HBout].
          left; repeat split; auto; exists X; split; auto.
        right.
        intro Habs.
        destruct Habs as [_ [_ [_ [X' [HX'Bet HUn]]]]].
        assert(Col B X' P) by (destruct HUn; subst; assert_cols; Col).
        assert(X = X') by (apply (l6_21 A C B P); Col; ColR).
        subst X'.
        assert_diffs.
        destruct HUn as [|HBout']; auto.
        assert(Col P B P' /\ ~ Bet P B P'); spliter; Between.
        apply l6_4_1.
        apply (l6_7 _ _ X); auto.
        apply l6_6; auto.
    }
    intro HNts.
    elim(col_dec B A P).
    { intro.
      elim(out_dec B A P).
      { intro.
        left.
        repeat split; auto.
        exists A; Between.
      }
      intro.
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      assert(Col B X P) by (destruct HUn; subst; assert_cols; Col).
      assert(X = A) by (apply (l6_21 A C B P); Col; ColR).
      subst X.
      destruct HUn; auto.
    }
    intro.
    elim(col_dec B C P).
    { intro.
      elim(out_dec B C P).
      { intro.
        left.
        repeat split; auto.
        exists C; Between.
      }
      intro.
      right.
      intro Habs.
      destruct Habs as [_ [_ [_ [X [HXBet HUn]]]]].
      assert(Col B X P) by (destruct HUn; subst; assert_cols; Col).
      assert(X = C) by (apply (l6_21 A C B P); Col; ColR).
      subst X.
      destruct HUn; auto.
    }
    intro.
    right.
    intro.
    apply HNts.
    apply invert_two_sides.
    apply in_angle_two_sides; auto.
  }
  intro HNCop.
  right.
  intro.
  apply HNCop; Cop.
Qed.

Lemma lea_dec : forall A B C D E F, LeA A B C D E F \/ ~ LeA A B C D E F.
Proof.
  intros A B C D E F.
  elim(eq_dec_points A B).
    intro; right; intro Hlea; apply lea_distincts in Hlea; spliter; auto.
  intro.
  elim(eq_dec_points B C).
    intro; right; intro Hlea; apply lea_distincts in Hlea; spliter; auto.
  intro.
  elim(eq_dec_points D E).
    intro; right; intro Hlea; apply lea_distincts in Hlea; spliter; auto.
  intro.
  elim(eq_dec_points E F).
    intro; right; intro Hlea; apply lea_distincts in Hlea; spliter; auto.
  intro.
  elim(col_dec A B C).
  { intro.
    elim(out_dec B A C).
      intro; left; apply l11_31_1; auto.
    intro.
    elim(bet_dec D E F).
      intro; left; apply l11_31_2; auto.
    intro HENBet.
    right.
    intro.
    apply HENBet.
    apply (bet_lea__bet A B C); auto.
    apply not_out_bet; auto.
  }
  intro HNColB.
  elim(col_dec D E F).
  { intro.
    elim(bet_dec D E F).
      intro; left; apply l11_31_2; auto.
    intro.
    right.
    intro.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro.
  assert(HP := angle_construction_1 A B C D E F).
  destruct HP as [P []]; Col.
  elim(inangle_dec D E F P).
    intro; left; exists P; auto.
  intro HNInAngle.
  right.
  intro.
  apply HNInAngle.
  apply lea_in_angle; try (apply conga_sym); Side.
  apply (l11_30 A B C D E F); auto; apply conga_refl; auto.
Qed.

Lemma gea_dec : forall A B C D E F, GeA A B C D E F \/ ~ GeA A B C D E F.
Proof.
  intros A B C D E F.
  unfold GeA.
  elim(lea_dec D E F A B C); auto.
Qed.

Lemma lta_dec : forall A B C D E F, LtA A B C D E F \/ ~ LtA A B C D E F.
Proof.
  intros A B C D E F.
  elim(conga_dec A B C D E F).
  { intro.
    right.
    unfold LtA.
    intro.
    spliter.
    auto.
  }
  intro.
  elim(lea_dec A B C D E F).
  { intro.
    left.
    split; auto.
  }
  intro.
  right.
  unfold LtA.
  intro.
  spliter.
  auto.
Qed.

Lemma gta_dec : forall A B C D E F, GtA A B C D E F \/ ~ GtA A B C D E F.
Proof.
  intros A B C D E F.
  unfold GtA.
  elim(lta_dec D E F A B C); auto.
Qed.

Lemma lea_total : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
   LeA A B C D E F \/ LeA D E F A B C.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  elim(col_dec A B C).
  { intro.
    elim(out_dec B A C).
    - intro; left; apply l11_31_1; auto.
    - intro; right; apply l11_31_2; auto; apply not_out_bet; auto.
  }
  intro.
  elim(col_dec D E F).
  { intro.
    elim(out_dec E D F).
    - intro; right; apply l11_31_1; auto.
    - intro; left; apply l11_31_2; auto; apply not_out_bet; auto.
  }
  intro.
  elim(lea_dec A B C D E F).
    intro; left; auto.
  intro HNlea.
  right.
  assert(HP := angle_construction_1 D E F A B C).
  destruct HP as [P []]; Col.
  exists P.
  split; auto.
  apply os2__inangle; Side.
  apply cop__not_two_sides_one_side; Col; Cop.
  - intro.
    apply HNlea.
    apply conga__lea.
    apply (out_conga A B P D E F); try (apply out_trivial); try (apply conga_sym); auto.
    apply (col_one_side_out _ A); Col; Side.

  - intro.
    apply HNlea.
    apply (l11_30 A B C A B P); try (apply conga_refl); try (apply conga_sym); auto.
    exists C.
    split; try (apply conga_refl); auto.
    apply os_ts__inangle; Side.
Qed.

Lemma gea_total : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
   GeA A B C D E F \/ GeA D E F A B C.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  elim(lea_total A B C D E F); auto.
Qed.

Lemma or_lta_conga_gta : forall A B C D E F,
 A <> B -> C <> B -> D <> E -> F <> E ->
 LtA A B C D E F \/ GtA A B C D E F \/ CongA A B C D E F.
Proof.
    intros.
    assert(HH:=lea_total A B C D E F).
    induction HH; auto.
      induction(conga_dec A B C D E F).
        right; right.
        assumption.
      left.
      unfold LtA.
      split; assumption.
    induction(conga_dec A B C D E F).
      right; right.
      assumption.
    right; left.
    unfold GtA.
    unfold LtA.
    split.
      assumption.
    intro.
    apply H4.
    apply conga_sym.
    assumption.
Qed.

Lemma angle_partition : forall A B C, A <> B -> B <> C ->
   Acute A B C \/ Per A B C \/ Obtuse A B C.
Proof.
  intros A B C HAB HBC.
  assert(Hl := lower_dim_ex).
  destruct Hl as [A' [B' [D']]].
  assert(~ Col A' B' D') by (unfold Col; auto).
  assert(HC' := l10_15 A' B' B' D').
  destruct HC' as [C' [HC'Right _]]; Col.
  assert_diffs.
  destruct (or_lta_conga_gta A B C A' B' C') as [|[|]]; auto.
  - left.
    exists A', B', C'.
    repeat (split; Perp).
  - right; right.
    exists A', B', C'.
    repeat (split; Perp).
  - right; left.
    apply (l11_17 A' B' C'); try (apply conga_sym); Perp.
Qed.

Lemma acute_chara : forall A B C A', Bet A B A' -> B <> A' -> (Acute A B C <-> LtA A B C A' B C).
Proof.
  intros A B C A' HBet HBA'.
  split.
  - intro Hacute.
    assert(Hdiff := acute_distincts A B C Hacute).
    spliter.
    apply acute_obtuse__lta; auto.
    apply (acute_bet__obtuse A); auto.

  - intro Hlta.
    assert (Hd := Hlta).
    apply lta_distincts in Hd.
    spliter.
    elim(angle_partition A B C); auto.
    intro Habs.
    exfalso.
    assert(Hlta1 : LtA A B C A B C);
    [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply conga_refl; auto].
    destruct Habs.
    { apply (conga_preserves_lta A B C A' B C); try (apply conga_refl); auto.
      apply conga_sym.
      apply conga_comm.
      apply l11_18_1; Perp.
    }
    apply (lta_trans _ _ _ A' B C); auto.
    apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); auto.
Qed.

Lemma obtuse_chara : forall A B C A', Bet A B A' -> B <> A' -> (Obtuse A B C <-> LtA A' B C A B C).
Proof.
  intros A B C A' HBet HBA'.
  split.
  - intro Hobtuse.
    assert(Hdiff := obtuse_distincts A B C Hobtuse).
    spliter.
    apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); auto.

  - intro Hlta.
    assert (Hd := Hlta).
    apply lta_distincts in Hd.
    spliter.
    elim(angle_partition A B C); auto.
    { intro.
      exfalso.
      assert(Hlta1 : LtA A B C A B C);
      [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply conga_refl; auto].
      apply (lta_trans _ _ _ A' B C); auto.
      apply acute_obtuse__lta; auto.
      apply (acute_bet__obtuse A); auto.
    }
    intro HUn.
    destruct HUn; auto.
    exfalso.
    assert(Hlta1 : LtA A B C A B C);
    [|destruct Hlta1 as [_ HNConga]; apply HNConga; apply conga_refl; auto].
    apply (conga_preserves_lta A' B C A B C); try (apply conga_refl); auto.
    apply conga_sym.
    apply conga_comm.
    apply l11_18_1; Between; Perp.
Qed.

Lemma conga__acute : forall A B C, CongA A B C A C B -> Acute A B C.
Proof.
  intros A B C HCongA.
  destruct (col_dec A B C).
  { apply out__acute, not_bet_out; trivial.
    intro.
    absurd (B = C).
      apply conga_distinct in HCongA; spliter; auto.
    apply between_equality with A; apply between_symmetry; trivial.
    apply (bet_conga__bet A B C); assumption.
  }
  destruct (segment_construction C B C B) as [C' []].
  apply conga_distinct in HCongA; spliter.
  assert_diffs.
  apply acute_sym, acute_chara with C'; auto.
  destruct (l11_41 B C A C'); Col.
  apply (conga_preserves_lta B C A A B C'); trivial.
    apply conga_comm, conga_sym; assumption.
    apply conga_pseudo_refl; auto.
Qed.

Lemma cong__acute : forall A B C, A <> B -> B <> C -> Cong A B A C -> Acute A B C.
Proof.
  intros A B C HAB HBC HCong.
  apply conga__acute.
  assert_diffs.
  destruct (l11_51 A B C A C B) as [_ []]; Cong.
Qed.


Lemma nlta : forall A B C, ~ LtA A B C A B C.
Proof.
  intros A B C.
  intro.
  apply (not_and_lta A B C A B C).
  split; assumption.
Qed.

Lemma lea__nlta : forall A B C D E F, LeA A B C D E F -> ~ LtA D E F A B C.
Proof.
  intros.
  intro Hlta.
  destruct Hlta as [Hlea HNConga].
  apply HNConga.
  apply lea_asym; assumption.
Qed.

Lemma lta__nlea : forall A B C D E F, LtA A B C D E F -> ~ LeA D E F A B C.
Proof.
  intros A B C D E F Hlta.
  destruct Hlta as [Hlea HNConga].
  intro.
  apply HNConga.
  apply lea_asym; assumption.
Qed.

Lemma nlta__lea : forall A B C D E F, ~ LtA A B C D E F -> A <> B -> B <> C -> D <> E -> E <> F ->
   LeA D E F A B C.
Proof.
  intros A B C D E F HNlta.
  intros.
  elim(conga_dec D E F A B C).
    apply conga__lea.
  intro.
  elim(lea_total D E F A B C); auto.
  intro.
  exfalso.
  apply HNlta.
  split; auto.
  apply not_conga_sym; assumption.
Qed.

Lemma nlea__lta : forall A B C D E F, ~ LeA A B C D E F  -> A <> B -> B <> C -> D <> E -> E <> F ->
   LtA D E F A B C.
Proof.
  intros A B C D E F HNlea.
  intros.
  split.
  - elim(lea_total D E F A B C); auto.
    intro; exfalso; auto.
  - intro.
    apply HNlea.
    apply conga__lea.
    apply conga_sym; assumption.
Qed.


(** The following lemmas express the triangle inequality only with predicates from Tarski :
AC <= AB + BC, and AC = AB + BC <-> Bet A B C
 *)

Lemma triangle_strict_inequality : forall A B C D, Bet A B D -> Cong B C B D -> ~ Bet A B C ->
   Lt A C A D.
Proof.
  intros A B C D HBet HCong HNBet.
  elim(col_dec A B C).
  { intro.
    assert(A <> B) by (intro; Between).
    assert(B <> C) by (intro; Between).
    apply not_bet_out in HNBet; Col.
    destruct HNBet as [_ [_ [HBAC|HBCA]]].
    - split.
      { apply (le_transitivity _ _ B C).
        apply le_comm; exists A; split; Between; Cong.
        apply (l5_6 D B D A); Cong; exists B; split; Between; Cong.
      }
      intro.
      assert(A = B); auto.
      apply between_symmetry in HBAC.
      apply (l7_17 C D); split; Cong.
        apply (outer_transitivity_between _ _ B); auto.
        apply (outer_transitivity_between2 _ A); auto.

    - assert(Bet A C D) by (apply (between_exchange4 _ _ B); Between).
      split.
        exists C; split; Cong.
      intro.
      assert(C = D) by (apply (between_cong A); auto).
      subst D.
      assert(B = C); auto.
      apply (between_equality _ _ A); Between.
  }
  intro HNCol.
  assert_diffs.
  assert(A <> D) by (intro; treat_equalities; auto).
  assert(~ Col A C D) by (intro; apply HNCol; ColR).
  assert_diffs.
  apply between_symmetry in HBet.
  apply l11_44_2; Col.
  assert(CongA C D A D C B).
  { apply (out_conga C D B D C B); try (apply out_trivial); auto.
    2: apply bet_out; auto.
    apply conga_comm.
    apply l11_44_1; Cong.
    intro; apply HNCol; ColR.
  }
  split.
  - apply lea_comm.
    exists B.
    repeat (split; auto).
    exists B.
    split; auto.
    right; apply out_trivial; auto.

  - intro.
    assert(Habs := conga_cop__or_out_ts D C A B).
    destruct Habs as [Hout|Hts].
      exists D; left; split; Col.
      apply (conga_trans _ _ _ C D A); auto; apply conga_sym; apply conga_comm; auto.
    apply HNCol; Col.
    assert(~ TS D C A B); auto.
    apply l9_9_bis.
    apply out_one_side; Col.
    apply l6_6; apply bet_out; auto.
Qed.

Lemma triangle_inequality : forall A B C D, Bet A B D -> Cong B C B D -> Le A C A D.
Proof.
  intros A B C D HCong HBet.
  elim(bet_dec A B C).
  - intro.
    elim(eq_dec_points A B).
      intro; subst; Le.
    intro.
    assert(C = D).
    apply (construction_uniqueness A B B D); Cong.
    subst; Le.

  - intro.
    assert(Hlt := triangle_strict_inequality A B C D).
    destruct Hlt; auto.
Qed.

Lemma triangle_strict_inequality_2 : forall A B C A' B' C',
   Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> ~ Bet A B C ->
   Lt A C A' C'.
Proof.
  intros A B C A' B' C' HBet HCongA HCongB HNBet.
  destruct (segment_construction A B B C) as [D [HBetD HCongD]].
  apply (cong2_lt__lt A C A D); Cong.
    apply (triangle_strict_inequality _ B); Cong.
  apply (l2_11 _ B _ _ B'); Cong.
  apply cong_transitivity with B C; trivial.
Qed.

Lemma triangle_inequality_2 : forall A B C A' B' C',
   Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' ->
   Le A C A' C'.
Proof.
  intros A B C A' B' C' HBet HCongA HCongB.
  destruct (segment_construction A B B C) as [D [HBetD HCongD]].
  apply (l5_6 A C A D); Cong.
    apply (triangle_inequality _ B); Cong.
  apply (l2_11 _ B _ _ B'); Cong.
  apply cong_transitivity with B C; trivial.
Qed.


(** The following lemmas express the reverse triangle inequality only with predicates from Tarski :
BC >= |AC - AB|, and BC = |AC - AB| <-> (A = B \/ A = C \/ Out A B C)
 *)

Lemma triangle_strict_reverse_inequality : forall A B C D,
  Out A B D -> Cong A C A D -> ~ Out A B C -> Lt B D B C.
Proof.
  intros A B C D HABD HCong HNout.
  elim(col_dec A B C).
  { intro.
    assert_diffs.
    apply not_out_bet in HNout; Col.
    assert(Bet D A C) by (apply (l6_2 B); auto).
    assert(C <> D) by (intro; treat_equalities; auto).
    split.
    2: intro; assert(A = B); auto; apply (l7_17 D C); split; Cong; apply l7_20_bis; auto; ColR.
    destruct HABD as [_ [_ [HABD|HADB]]].
    - apply (le_transitivity _ _ A D).
        apply le_comm; exists B; split; Between; Cong.
      apply (l5_6 C A C B); Cong.
      exists A; split; Between; Cong.

    - exists D.
      split; Cong.
      apply (outer_transitivity_between _ _ A); Between.
  }
  intro HNCol.
  assert_diffs.
  elim(eq_dec_points B D).
  { intro.
    subst.
    split; Le.
    intro; treat_equalities; auto.
  }
  intro.
  assert(HNCol2 : ~ Col B C D) by (intro; apply HNCol; ColR).
  assert(HNCol3 : ~ Col A C D) by (intro; apply HNCol; ColR).
  assert_diffs.
  apply l11_44_2; Col.
  assert(CongA A C D A D C) by (apply l11_44_1; Cong; Col).
  destruct HABD as [_ [_ [HABD|HADB]]].
  - apply between_symmetry in HABD.
    apply (conga_preserves_lta D C B D C A).
      apply conga_pseudo_refl; auto.
      apply (out_conga D C A A D C); try (apply out_trivial); try (apply conga_left_comm); auto; apply l6_6; apply bet_out; auto.
    split.
    { exists B.
      split; try (apply conga_refl); auto.
      repeat split; auto.
      exists B.
      split; auto.
      right; finish.
    }
    intro.
    assert(~ TS D C B A).
    { apply l9_9_bis.
      apply out_one_side; Col.
      apply bet_out; auto.
    }
    assert(Habs := conga_cop__or_out_ts D C B A).
    destruct Habs as [Hout|Hts]; auto.
      exists D; left; split; Col.
    apply HNCol; Col.

  - assert(HE := symmetric_point_construction B C).
    destruct HE as [E []].
    assert_diffs.
    apply (bet2_lta__lta A _ _ E); Between.
    assert (OS D C A E).
    { exists B.
        repeat split; Col.
        exists D; Col.
        intro; apply HNCol2; ColR.
        exists C; split; finish.
    }
    apply (conga_preserves_lta A C D E C D); try (apply conga_refl); auto.
    split.
    { apply lea_comm.
      exists A.
      split.
      2: apply conga_refl; auto.
      apply os2__inangle; Side.
      apply (col_one_side _ B); Col.
      apply invert_one_side.
      apply out_one_side; Col.
      apply bet_out; Between.
    }
    intro.
    assert(Habs := conga_cop__or_out_ts D C A E).
    destruct Habs as [Hout|Hts]; try (apply conga_comm); Cop.
      apply HNCol; ColR.
      assert(~ TS D C A E); try (apply l9_9_bis); auto.
Qed.

Lemma triangle_reverse_inequality : forall A B C D, Out A B D -> Cong A C A D -> Le B D B C.
Proof.
  intros A B C D HABD HCong.
  elim(out_dec A B C).
  2: apply triangle_strict_reverse_inequality; auto.
  intro.
  assert_diffs.
  assert(C = D) by (apply (l6_11_uniqueness A A C B); Cong; apply l6_6; auto).
  subst; Le.
Qed.

(** This is half of Euclid Book I, Proposition 21:
  if D is inside the triangle ABC then BAC < BDC.
 *)

Lemma os3__lta : forall A B C D, OS A B C D -> OS B C A D -> OS A C B D ->
   LtA B A C B D C.
Proof.
  intros A B C D HosC HosA HosB.
  assert(HE : InAngle D A B C) by (apply os2__inangle; Side).
  destruct HE as [_ [_ [_ [E [HEBet HUn]]]]].
  assert(HNCol : ~ Col A B C) by (apply (one_side_not_col123 _ _ _ D); auto).
  assert_ncols.
  destruct HUn as [|HBout].
    exfalso; subst; Col.
  assert(A <> E) by (intro; subst; assert_cols; Col).
  assert(C <> E) by (intro; subst; assert_cols; Col).
  assert_diffs.
  apply (lta_trans _ _ _ B E C).
  - destruct (l11_41 E A B C); auto.
      intro; apply HNCol; ColR.
    apply (conga_preserves_lta E A B B E C); try (apply conga_refl); auto.
    apply (out_conga E A B B A E); try (apply out_trivial); try (apply conga_pseudo_refl); auto.
    apply bet_out; auto.

  - assert(Out E D B).
      apply (col_one_side_out _ A); Col; apply invert_one_side; apply (col_one_side _ C); Col; Side.
    assert_diffs.
    destruct (l11_41 D E C B); auto.
      intro; apply HNCol; ColR.
      apply out2__bet; auto.
    apply (conga_preserves_lta D E C C D B); try (apply conga_pseudo_refl); auto.
    apply (out_conga D E C D E C); try (apply out_trivial); try (apply conga_refl); auto.
Qed.

(** This is Theorem 18.17 from Martin *)

Lemma bet_le__lt : forall A B C D, Bet A D B -> A <> D -> D <> B -> Le A C B C -> Lt D C B C.
Proof.
  intros A B C D HBet HAD HBD Hle.
  assert(HAB : B <> A) by (intro; treat_equalities; auto).
  apply lt_comm.
  elim(col_dec A B C).
  { intro.
    elim(bet_dec C D B).
    { intro.
      split.
      exists D; Cong.
      intro.
      apply HBD.
      apply (between_cong C); auto.
    }
    intro HNBet.
    apply not_bet_out in HNBet; try ColR.
    assert_diffs.
    assert(Bet C D A) by (apply (l6_2 B); try (apply l6_6); Between).
    assert(A <> C) by (intro; treat_equalities; auto).
    assert(Hout : Out A C B) by (apply (l6_7 _ _ D); [apply l6_6|]; apply bet_out; Between).
    assert(~ Bet A B C).
    { intro.
      apply HAB.
      apply (between_cong C); Between.
      apply le_anti_symmetry; Le.
    }
    destruct Hout as [_ [_ [HACB|]]].
    2: exfalso; auto.
    assert(B <> C) by (intro; subst; Between).
    assert(HC' := symmetric_point_construction A C).
    destruct HC' as [C'].
    assert_diffs.
    assert(Bet C C' B).
    { apply l6_13_1.
      apply (l6_2 _ _ A); Between.
      apply (l5_6 A C B C); Cong.
    }
    apply (le3456_lt__lt _ _ C A).
    2: exists C'; split;auto with cong.
    split.
    exists D; auto with cong.
    intro.
    apply HAD.
    symmetry.
    apply (between_cong C); Between.
  }
  intro HNCol.
  assert_diffs.
  apply l11_44_2.
    intro; apply HNCol; ColR.
  apply (lea123456_lta__lta _ _ _ C A B).
  - apply (l11_30 C B A C A B); try apply (conga_refl); auto.
    2: apply (out_conga C B D C B D); try apply (out_trivial); try (apply conga_refl); auto; apply bet_out; Between.
    elim (cong_dec A C B C).
      intro; apply conga__lea; apply l11_44_1; Col; Cong.
      intro; apply lta__lea; apply l11_44_2; Col; apply lt_comm; split; auto.

  - assert(~ Col D A C) by (intro; apply HNCol; ColR).
    assert_diffs.
    assert(HInter := l11_41 D A C B).
    destruct HInter; auto.
    apply (conga_preserves_lta D A C C D B); try (apply conga_refl); auto.
    apply (out_conga D A C C A D); try (apply out_trivial); try (apply conga_pseudo_refl); auto.
    apply bet_out; auto.
Qed.

Lemma t18_18_aux : forall A B C D E F,
  Cong A B D E -> Cong A C D F -> LtA F D E C A B -> ~ Col A B C -> ~ Col D E F -> Le D F D E ->
  Lt E F B C.
Proof.
  intros A B C D E F HCongAB HCongAC Hlta HNCol1 HNCol2 Hle.
  assert (Hd := Hlta).
  apply lta_distincts in Hd.
  spliter.
  assert(HG0 := angle_construction_1 C A B F D E).
  destruct HG0 as [G0 []]; Col.
  assert(~ Col F D G0) by (apply (one_side_not_col123 _ _ _ E); auto).
  assert_diffs.
  assert(HG := segment_construction_3 D G0 A B).
  destruct HG as [G []]; auto.
  assert(CongA C A B F D G) by (apply (out_conga C A B F D G0); try (apply out_trivial); auto).
  assert(OS F D G E).
  { apply (one_side_transitivity _ _ _ G0); auto.
    apply invert_one_side.
    apply out_one_side; Col.
    apply l6_6; auto.
  }
  assert(HNCol3 : ~ Col F D G) by (apply (one_side_not_col123 _ _ _ E); auto).
  clear dependent G0.

  assert_diffs.
  assert(HSAS := l11_49 C A B F D G).
  destruct HSAS as [HCongBC _]; Cong.
  apply (cong2_lt__lt F E F G); Cong.
  apply (conga_preserves_lta _ _ _ _ _ _ F D E F D G) in Hlta; try (apply conga_refl); auto.
  assert(Cong D G D E) by (apply (cong_transitivity _ _ A B); auto).
  clear dependent A.
  clear dependent B.

  assert(~ Col E F G).
  { intro.
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    assert (HSSA := l11_52 E F D G F D).
    destruct HSSA as [_[]]; Cong; Le.
    apply (out_conga G F D G F D); try (apply out_trivial); try (apply conga_refl); auto.
    apply (col_one_side_out _ D); Col.
  }
  assert(~ Col D E G).
  { intro.
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    apply (out_conga F D G F D G); try (apply out_trivial); try (apply conga_refl); auto.
    apply (col_one_side_out _ F); Col; Side.
  }
  apply l11_44_2; Col.
  assert(HInAngle : InAngle E F D G) by (apply lea_in_angle; destruct Hlta; auto).
  rename H into HFD.
  destruct HInAngle as [_ [_ [_ [H [HH HUn]]]]].
  destruct HUn.
    exfalso; subst; Col.
  assert(H <> F) by (intro; subst; assert_cols; Col).
  assert(H <> G) by (intro; subst; assert_cols; Col).
  assert(Hlt : Lt D H D E).
  { apply (cong2_lt__lt H D G D); Cong.
    apply (bet_le__lt F); auto.
    apply (l5_6 D F D E); Cong.
  }
  destruct Hlt.
  assert(H <> E) by (intro; subst; Cong).
  assert(Bet D H E) by (apply l6_13_1; Le).
  assert_diffs.
  assert(~ TS E G F D).
  { apply l9_9_bis.
    apply (one_side_transitivity _ _ _ H);
    [apply invert_one_side; apply one_side_symmetry|];
    apply out_one_side; Col;
    apply bet_out; Between.
  }
  apply (lta_trans _ _ _ D E G).
  - apply(conga_preserves_lta F G E D G E); try (apply conga_refl); auto.
      apply l11_44_1; Col.
    split.
    { apply lea_comm.
      exists F.
      split; try (apply conga_refl); auto.
      repeat split; auto.
      exists H.
      split; Between.
      right; apply bet_out; Between.
    }
    intro HConga.
    apply conga_comm in HConga.
    assert (HCop : Coplanar E G F D) by Cop.
    assert(Habs := conga_cop__or_out_ts E G F D HCop HConga).
    destruct Habs as [Hout|Hts]; assert_cols; Col.

  - apply lta_comm.
    split.
    { exists D.
      split; try (apply conga_refl); auto.
      repeat split; auto.
      exists H.
      split; Between.
      right; apply bet_out; Between.
    }
    intro HConga.
    assert (HCop : Coplanar G E D F) by Cop.
    assert(Habs := conga_cop__or_out_ts G E D F HCop HConga).
    destruct Habs as [Hout|Hts]; assert_cols; Col; Side.
Qed.

(** This is Euclid Book I, Proposition 24. *)

Lemma t18_18 : forall A B C D E F, Cong A B D E -> Cong A C D F -> LtA F D E C A B -> Lt E F B C.
Proof.
  intros A B C D E F HCongAB HCongAC Hlta.
  assert (Hd := Hlta).
  apply lta_distincts in Hd.
  spliter.
  elim(col_dec A B C).
  { intro.
    elim(bet_dec B A C).
    - intro.
      assert(HC' := segment_construction E D A C).
      destruct HC' as [C' []].
      apply (cong2_lt__lt E F E C'); Cong.
      2: apply (l2_11 _ D _ _ A); Cong.
      apply (triangle_strict_inequality _ D); auto.
      apply (cong_transitivity _ _ A C); Cong.
      intro.
      destruct Hlta as [_ HNConga].
      apply HNConga.
      apply conga_line; Between.

    - intro.
      exfalso.
      apply (nlta C A B).
      apply (lea123456_lta__lta _ _ _ F D E); auto.
      apply l11_31_1; auto.
      apply not_bet_out; Col; Between.
  }
  intro.
  elim(col_dec D E F).
  { intro.
    elim(bet_dec F D E).
    - intro.
      exfalso.
      apply (nlta F D E).
      apply (lea456789_lta__lta _ _ _ C A B); auto.
      apply l11_31_2; auto.

    - intro HNBet.
      apply not_bet_out in HNBet; Col.
      assert(HF' := segment_construction_3 A B A C).
      destruct HF' as [F' []]; auto.
      apply (cong2_lt__lt B F' B C); Cong.
      { apply (triangle_strict_reverse_inequality A); Cong.
        intro.
        destruct Hlta as [_ HNConga].
        apply HNConga.
        apply l11_21_b; auto.
        apply l6_6; auto.
      }
      apply (out_cong_cong A _ _ D); auto.
      apply l6_6; auto.
      apply (cong_transitivity _ _ A C); auto.
  }
  intro.
  elim(le_cases D F D E); intro; [|apply lt_comm; apply lta_comm in Hlta];
  apply (t18_18_aux A _ _ D); Cong; Col.
Qed.

Lemma t18_19 : forall A B C D E F, A <> B -> A <> C -> Cong A B D E -> Cong A C D F -> Lt E F B C ->
   LtA F D E C A B.
Proof.
  intros A B C D E F HAB HAC HCongAB HCongAC Hlt.
  assert_diffs.
  apply nlea__lta; auto.
  intro Hlea.
  elim(conga_dec C A B F D E).
  - intro.
    exfalso.
    destruct Hlt as [Hle HNCong].
    apply HNCong.
    assert(HSAS := l11_49 C A B F D E).
    destruct HSAS; Cong.

  - intro.
    apply (not_and_lt E F B C).
    split; auto.
    apply (t18_18 D _ _ A); Cong.
    split; auto.
Qed.

Lemma acute_trivial : forall A B, A <> B -> Acute A B A.
Proof.
    intros.
    assert(HH:= not_col_exists A B H).
    ex_and HH P.
    assert(exists C : Tpoint, Per C B A /\ Cong C B A B /\ OS A B C P).
      apply(ex_per_cong A B B P A B H H); Col; exists A.
    ex_and H1 C.
    assert_diffs.
    unfold Acute.
    exists A.
    exists B.
    exists C.
    split.
      apply l8_2.
      auto.
    unfold LtA.
    split.
      unfold LeA.
      exists A.
      split.
        apply inangle1123; auto.
      apply conga_refl; auto.
    intro.
    assert(Out B A C).
      apply(l11_21_a A B A A B C).
        apply out_trivial; auto.
      auto.
    assert(Perp C B B A).
      apply per_perp_in in H1; auto.
      apply perp_in_perp_bis in H1.
      induction H1.
        apply perp_not_eq_1 in H1.
        tauto.
      auto.
    apply perp_comm in H10.
    apply perp_not_col in H10.
    apply out_col in H8.
    Col.
Qed.

Lemma acute_not_per : forall A B C, Acute A B C -> ~ Per A B C.
Proof.
    intros.
    unfold Acute in H.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    unfold LtA in H0.
    spliter.
    intro.
    apply H1.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B').
      unfold LeA in H0.
      ex_and H0 X.
      apply conga_distinct in H3.
      spliter.
      repeat split; auto.
      unfold InAngle in H0.
      spliter; auto.
    spliter.
    apply(l11_16 A B C A' B' C'); auto.
Qed.

Lemma angle_bisector : forall A B C, A <> B -> C <> B ->
  exists P, InAngle P A B C /\ CongA P B A P B C.
Proof.
  intros A B C HAB HCB.
  elim (col_dec A B C).
  { intro HCol.
    elim (bet_dec A B C).
    - intro HBet; destruct (not_col_exists A B) as [Q HNCol]; trivial.
      destruct (l10_15 A B B Q) as [P [HPerp HOS]]; Col.
      assert_diffs; exists P; split.
        apply in_angle_line; auto.
      apply l11_18_1; Perp.
    - intro HOut; apply not_bet_out in HOut; trivial; assert_diffs.
      exists C; split.
        repeat split; auto.
       exists C; split; Between.
        right; apply out_trivial; auto.
      apply l11_21_b.
        apply l6_6; trivial.
      apply out_trivial; auto.
  }
  intro HNCol.
  assert_diffs.
  destruct (l6_11_existence B B A C) as [C0 [HOut HCong]]; auto.
  destruct (midpoint_existence A C0) as [P HP].
  exists P.
  assert_diffs.
  assert (HNCol1 : ~ Col A B C0) by (intro; apply HNCol; ColR).
  assert_diffs.
  assert (P <> B) by (intro; subst P; apply HNCol1; Col).
  split.
    apply (l11_25 P A B C0); try (apply out_trivial); auto; [|apply l6_6; trivial].
    repeat split; auto.
    exists P; split; Between.
    right; apply out_trivial; auto.
  destruct (l11_51 B P A B P C0); auto with cong.
  apply (out_conga P B A P B C0); try (apply out_trivial); auto.
Qed.

Lemma reflectl__conga : forall A B P P', A <> B -> B <> P -> ReflectL P P' A B -> CongA A B P A B P'.
Proof.
  intros A B P P' HAB HBP HRefl.
  destruct HRefl as [[A' [HMid HCol]] [HPerp|Heq]]; [|subst; apply conga_refl; auto].
  assert_diffs.
  destruct (eq_dec_points A' B).
    subst A'.
    assert_diffs.
    apply l11_16; auto; apply perp_per_1;
    [apply perp_col1 with P'|apply perp_col1 with P]; Col; Perp.
  destruct HMid as [HBet HCong].
  destruct (l11_49 B A' P B A' P') as [HCong1 [HConga1 HConga2]]; Cong.
    apply l11_16; auto;
    apply perp_per_1, perp_left_comm, perp_col with A; Col;
    [apply perp_col1 with P'|apply perp_col1 with P]; Col; Perp.
  destruct (bet_dec A' B A) as [HBBet|HBOut].
    apply l11_13 with A' A'; assumption.
  apply not_bet_out in HBOut; Col.
  apply out_conga with A' P A' P'; trivial; apply out_trivial; assert_diffs; auto.
Qed.

Lemma conga_cop_out_reflectl__out : forall A B C P T T',
  ~ Out B A C -> Coplanar A B C P -> CongA P B A P B C -> Out B A T -> ReflectL T T' B P ->
  Out B C T'.
Proof.
  intros A B C P T T' HNOut HCop HConga HOut HRefl.
  apply conga_distinct in HConga; spliter; clean.
  assert_diffs.
  assert (HConga1 : CongA P B T P B T') by (apply reflectl__conga; auto; apply is_image_spec_rev, HRefl).
  apply is_image_is_image_spec in HRefl; auto.
  apply conga_distinct in HConga1; spliter; clean.
  destruct (conga_cop__or_out_ts P B C T'); trivial.
  - apply coplanar_trans_1 with T; [..|Cop].
    { intro.
      apply HNOut.
      assert (HCol : Col A B P) by ColR.
      destruct (bet_dec A B P) as [HBet|HOut1].
        apply l6_2 with P; auto.
        apply (bet_conga__bet A B P); [|apply conga_comm]; assumption.
      apply not_bet_out in HOut1; trivial.
      apply l6_7 with P; trivial.
      apply (l11_21_a P B A); [apply l6_6|]; assumption.
    }
    apply coplanar_perm_19, col_cop__cop with A; Col; Cop.
  - apply conga_trans with P B A.
    apply conga_sym; assumption.
    apply l6_6 in HOut; apply out_conga with P T P T'; try (apply out_trivial); auto.
  - exfalso.
    apply (l9_9_bis P B C T'); trivial.
    exists A; split; apply l9_2.
      destruct (conga_cop__or_out_ts P B A C); Cop; contradiction.
    apply out_two_sides_two_sides with T B; Col.
    apply invert_two_sides, l10_14; auto.
    intro; subst T'.
    apply HNOut.
    assert (Col T B P) by (apply l10_8, HRefl).
    assert (Col P B A) by ColR.
    assert (Col P B C) by (apply (col_conga_col P B A); assumption).
    apply not_bet_out; try ColR.
    intro HBet.
    apply (per_not_col P B A); auto.
    apply l11_18_2 with C; assumption.
Qed.

Lemma col_conga_cop_reflectl__col : forall A B C P T T',
  ~ Out B A C -> Coplanar A B C P -> CongA P B A P B C -> Col B A T -> ReflectL T T' B P ->
  Col B C T'.
Proof.
  intros A B C P T T' HNOut HCop HConga HCol HRefl.
  destruct (eq_dec_points B T).
    subst; assert (T = T'); subst; Col.
    apply (l10_6_uniqueness_spec T P T); trivial; apply col__refl; Col.
  destruct (out_dec B A T).
    apply out_col, conga_cop_out_reflectl__out with A P T; assumption.
  destruct (segment_construction A B A B) as [A' [HA'1 HA'2]].
  destruct (segment_construction C B C B) as [C' [HC'1 HC'2]].
  assert (Out B C' T'); try ColR.
  apply conga_distinct in HConga; spliter; assert_diffs.
  apply conga_cop_out_reflectl__out with A' P T; trivial.
  - intro; apply HNOut.
    apply l6_2 with A'; auto.
    apply between_symmetry, l6_2 with C'; try (apply l6_6); Between.
  - destruct (col_dec A B C).
      exists C'; left; split; ColR.
    apply coplanar_pseudo_trans with A B C; Cop.
  - apply conga_comm, l11_13 with A C; auto; apply conga_comm; assumption.
  - apply l6_2 with A; try (apply between_symmetry); auto.
    apply not_out_bet; Col.
Qed.

Lemma conga2_cop2__col : forall A B C P P', ~ Out B A C ->
  CongA P B A P B C -> CongA P' B A P' B C ->
  Coplanar A B P P' -> Coplanar B C P P' ->
  Col B P P'.
Proof.
  intros A B C P P' HNOut HP HP' HCopA HCopC.
  apply conga_distinct in HP; apply conga_distinct in HP'; spliter; clean.
  destruct (l6_11_existence B B A C) as [C' [HC'1 HC'2]]; auto.
  destruct (l11_49 P B A P B C'); Cong.
    apply out_conga with P A P C; try (apply out_trivial); try (apply l6_6); auto.
  destruct (l11_49 P' B A P' B C'); Cong.
    apply out_conga with P' A P' C; try (apply out_trivial); try (apply l6_6); auto.
  apply cong3_cop2__col with A C'; Cong.
    Cop.
    apply coplanar_perm_12, col_cop__cop with C; Col; Cop.
  intro; subst; auto.
Qed.

Lemma conga2_cop2__col_1 : forall A B C P P', ~ Col A B C ->
  CongA P B A P B C -> CongA P' B A P' B C ->
  Coplanar A B C P -> Coplanar A B C P' ->
  Col B P P'.
Proof.
  intros A B C P P' HNCol HP HP' HCop HCop'.
  apply conga2_cop2__col with A C; trivial; [|apply coplanar_pseudo_trans with A B C; Cop..].
  intro; apply HNCol; Col.
Qed.

Lemma col_conga__conga : forall A B C P P', CongA P B A P B C -> Col B P P' -> B <> P' ->
  CongA P' B A P' B C.
Proof.
  intros A B C P P' HConga HCol HBP'.
  destruct (bet_dec P B P') as [HBet|HNBet].
    apply l11_13 with P P; auto.
  apply not_bet_out in HNBet; Col.
  apply conga_distinct in HConga; spliter.
  apply out_conga with P A P C; try (apply out_trivial); auto.
Qed.

Lemma cop_inangle__ex_col_inangle : forall A B C P Q,
  ~ Out B A C -> InAngle P A B C -> Coplanar A B C Q ->
  exists R, InAngle R A B C /\ P <> R /\ Col P Q R.
Proof.
  intros A B C P Q HNOut HIn HCop.
  assert (h := inangle_distincts A B C P HIn); spliter.
  assert (A <> C) by (intro; subst; apply HNOut, out_trivial; auto).
  destruct (eq_dec_points P Q).
  { subst Q.
    destruct (eq_dec_points A P).
      subst P; exists C; split; Col.
      apply inangle3123; auto.
    exists A; split; Col; apply inangle1123; auto.
  }
  destruct (col_dec B P Q) as [HCol|HNCol1].
  { destruct (segment_construction B P B P) as [R [HR1 HR2]].
    exists R.
    assert_diffs; split; [|split; ColR].
    apply l11_25 with P A C; try (apply out_trivial); auto.
    apply l6_6, bet_out; auto.
  }
  assert_diffs.
  destruct (col_dec A B C) as [HCol|HNCol2].
    exists Q; split; Col.
    apply in_angle_line; auto.
    apply not_out_bet; assumption.
  destruct (col_dec B C P) as [HCol|HNCol3].
  - assert (HNCol3 : ~ Col B A P) by (intro; apply HNCol2; ColR).
    destruct (cop_not_par_same_side B P Q P P A) as [Q0 [HCol1 HOS]]; Col.
      apply coplanar_perm_16, col_cop__cop with C; Cop.
    assert (Hd := os_distincts B P A Q0 HOS); spliter; clean.
    destruct (one_side_dec B A P Q0).
    { assert (HIn' : InAngle Q0 A B P) by (apply os2__inangle; assumption).
      exists Q0; split; Col.
      apply in_angle_trans with P; trivial.
    }
    assert (HR : exists R, Bet P R Q0 /\ Col P Q R /\ Col B A R).
    { destruct (col_dec B A Q0).
        exists Q0; split; Between; Col.
      assert_diffs.
      destruct (cop__not_one_side_two_sides B A P Q0) as [_ [_ [R [HCol' HBet]]]]; Col; Cop.
      exists R; split; trivial; split; ColR.
    }
    destruct HR as [R [HR1 [HR2 HR3]]].
    assert (P <> R) by (intro; subst; apply HNCol3, HR3).
    exists R; split; auto.
    apply out321__inangle; auto.
    apply col_one_side_out with P; trivial.
    apply one_side_transitivity with Q0; trivial.
    apply one_side_not_col124 in HOS.
    apply invert_one_side, out_one_side; Col.
    apply l6_6, bet_out; auto.
  - destruct (cop_not_par_same_side B P Q P P C) as [Q0 [HCol1 HOS]]; Col.
      apply coplanar_perm_3, coplanar_trans_1 with A; Cop.
    assert (Hd := os_distincts B P C Q0 HOS); spliter; clean.
    destruct (one_side_dec B C P Q0).
    { assert (HIn' : InAngle Q0 C B P) by (apply os2__inangle; assumption).
      exists Q0; split; Col.
      apply l11_24, in_angle_trans with P; trivial.
      apply l11_24, HIn.
    }
    assert (HR : exists R, Bet P R Q0 /\ Col P Q R /\ Col B C R).
    { destruct (col_dec B C Q0).
        exists Q0; split; Between; Col.
      assert_diffs.
      destruct (cop__not_one_side_two_sides B C P Q0) as [_ [_ [R [HCol' HBet]]]]; Col; Cop.
      exists R; split; trivial; split; ColR.
    }
    destruct HR as [R [HR1 [HR2 HR3]]].
    assert (P <> R) by (intro; subst; apply HNCol3, HR3).
    exists R; split; auto.
    apply l11_24, out321__inangle; auto.
    apply col_one_side_out with P; trivial.
    apply one_side_transitivity with Q0; trivial.
    apply one_side_not_col124 in HOS.
    apply invert_one_side, out_one_side; Col.
    apply l6_6, bet_out; auto.
Qed.

Lemma col_inangle2__out : forall A B C P Q,
  ~ Bet A B C -> InAngle P A B C -> InAngle Q A B C -> Col B P Q ->
  Out B P Q.
Proof.
  intros A B C P Q HNBet HP HQ HCol.
  assert (Hd := inangle_distincts A B C P HP);
  assert (Hd' := inangle_distincts A B C Q HQ);
  spliter; clean.
  destruct (col_dec A B C).
    assert (Out B A C) by (apply not_bet_out; assumption).
    apply l6_7 with A; [apply l6_6|]; apply out_in_angle_out with C; auto.
  destruct (col_dec B A P) as [HCol1|HNCol1].
    apply l6_7 with A; [apply l6_6|]; apply col_in_angle_out with C; ColR.
  apply col_one_side_out with A; trivial.
  apply one_side_transitivity with C; [|apply one_side_symmetry];
    apply invert_one_side, in_angle_one_side; Col.
  intro; apply HNCol1; ColR.
Qed.

Lemma inangle2__lea : forall A B C P Q, InAngle P A B C -> InAngle Q A B C ->
  LeA P B Q A B C.
Proof.
  intros A B C P Q HP HQ.
  assert (HP' := l11_24 P A B C HP).
  assert (HQ' := l11_24 Q A B C HQ).
  assert (Hd := inangle_distincts A B C P HP);
  assert (Hd' := inangle_distincts A B C Q HQ);
  spliter; clean.
  destruct (col_dec A B C) as [HCol|HNCol].
  { destruct (bet_dec A B C).
      apply l11_31_2; auto.
    apply l11_31_1; auto.
    assert (Out B A C) by (apply not_bet_out; assumption).
    apply l6_7 with A; [apply l6_6|]; apply out_in_angle_out with C; auto.
  }
  destruct (col_dec B P Q) as [HCol1|HNCol1].
    apply l11_31_1; auto; apply col_inangle2__out with A C; auto.
    intro; apply HNCol; Col.
  destruct (col_dec B A P) as [HCol2|HNCol2].
  { assert (Out B A P) by (apply col_in_angle_out with C; auto; intro; apply HNCol; Col).
    exists Q; split; trivial.
    apply out_conga with A Q A Q; try (apply out_trivial); auto.
    apply conga_refl; auto.
  }
  destruct (col_dec B C P) as [HCol3|HNCol3].
  { assert (Out B C P).
      apply col_in_angle_out with A; auto; intro; apply HNCol; Col.
    apply lea_right_comm.
    exists Q; split; trivial.
    apply out_conga with C Q C Q; try (apply out_trivial); auto.
    apply conga_refl; auto.
  }
  destruct (col_dec B A Q) as [HCol4|HNCol4].
  { assert (Out B A Q) by (apply col_in_angle_out with C; auto; intro; apply HNCol; Col).
    apply lea_left_comm.
    exists P; split; trivial.
    apply out_conga with A P A P; try (apply out_trivial); auto.
    apply conga_refl; auto.
  }
  destruct (col_dec B C Q) as [HCol5|HNCol5].
  { assert (Out B C Q).
      apply col_in_angle_out with A; auto; intro; apply HNCol; Col.
    apply lea_comm.
    exists P; split; trivial.
    apply out_conga with C P C P; try (apply out_trivial); auto.
    apply conga_refl; auto.
  }
  destruct (cop__one_or_two_sides B P A Q) as [HOS|HTS]; Col.
    apply coplanar_perm_2, coplanar_trans_1 with C; Cop; Col.
  - apply lea_trans with P B C; [|apply lea_comm]; apply inangle__lea; trivial.
    apply os2__inangle; apply invert_one_side.
      exists A; split; Side; apply in_angle_two_sides; Col.
    apply one_side_transitivity with A; [|apply one_side_symmetry];
    apply in_angle_one_side; Col.
  - apply lea_trans with A B P; [apply lea_right_comm|]; apply inangle__lea; trivial.
    apply os2__inangle; trivial.
    apply invert_one_side, one_side_transitivity with C; [|apply one_side_symmetry];
    apply in_angle_one_side; Col.
Qed.

Lemma conga_inangle_per__acute : forall A B C P,
  Per A B C -> InAngle P A B C -> CongA P B A P B C ->
  Acute A B P.
Proof.
  intros A B C P HPer HP1 HP2.
  assert (Hd := inangle_distincts A B C P HP1); spliter; clean.
  assert (HNCol : ~ Col A B C) by (apply per_not_col; auto).
  exists A, B, C; split; trivial.
  split.
    apply inangle__lea, HP1.
  intro Habs.
  assert (Per A B P) by (apply l11_17 with A B C, conga_sym; trivial).
  apply HNCol, col_permutation_1, cop_per2__col with P; Cop.
  apply l11_17 with A B P; trivial.
  apply conga_comm, HP2.
Qed.

Lemma conga_inangle2_per__acute : forall A B C P Q, Per A B C ->
  InAngle P A B C -> CongA P B A P B C -> InAngle Q A B C ->
  Acute P B Q.
Proof.
  intros A B C P Q HPer HP1 HP2 HQ.
  assert (HP' := l11_24 P A B C HP1).
  assert (HQ' := l11_24 Q A B C HQ).
  assert (Hd := inangle_distincts A B C P HP1);
  assert (Hd' := inangle_distincts A B C Q HQ);
  spliter; clean.
  assert (HNCol : ~ Col A B C) by (apply per_not_col; auto).
  assert (HAcute : Acute A B P) by (apply conga_inangle_per__acute with C; assumption).
  assert (HNCol1 : ~ Col P B A).
    intro.
    assert (Col P B C) by (apply (col_conga_col P B A); assumption).
    apply HNCol; ColR.
  assert (HNCol2 : ~ Col P B C) by (apply (ncol_conga_ncol P B A); assumption).
  assert (~ Bet A B C) by (intro; apply HNCol; Col).
  destruct (col_dec B A Q).
    assert (Out B A Q) by (apply col_in_angle_out with C; Col).
    apply (acute_conga__acute A B P); trivial.
    apply out_conga with A P P A; try (apply out_trivial); auto.
    apply conga_pseudo_refl; auto.
  destruct (col_dec B C Q).
    assert (Out B C Q) by (apply col_in_angle_out with A; Between; Col).
    apply (acute_conga__acute A B P); trivial.
    apply out_conga with A P P C; try (apply out_trivial); auto.
    apply conga_left_comm, HP2.
  destruct (col_dec B P Q).
    apply out__acute, col_inangle2__out with A C; assumption.
  destruct (cop__one_or_two_sides B P A Q) as [HOS|HTS]; Col.
    apply coplanar_perm_2, coplanar_trans_1 with C; Cop; Col.
  - apply acute_lea_acute with P B C.
      apply (acute_conga__acute A B P); try (apply conga_left_comm); assumption.
    exists Q; split; [|apply conga_refl; auto].
    apply os2__inangle; apply invert_one_side.
      exists A; split; Side; apply in_angle_two_sides; Col.
    apply one_side_transitivity with A; [|apply one_side_symmetry];
    apply in_angle_one_side; Col.
  - apply acute_lea_acute with A B P; trivial.
    apply lea_comm.
    exists Q; split; [|apply conga_pseudo_refl; auto].
    apply os2__inangle; trivial.
    apply invert_one_side, one_side_transitivity with C; [|apply one_side_symmetry];
    apply in_angle_one_side; Col.
Qed.

Lemma lta_os__ts : forall A O B P, ~ Col A O P -> LtA A O P A O B -> OS O A B P ->
  TS O P A B.
Proof.
intros.
unfold LtA in *.
spliter.
unfold LeA in *.
ex_and H0 P'.
assert(~Col A O B).
{
  unfold OS in H1.
  ex_and H1 R.
  unfold TS in H1.
  spliter; Col.
}
unfold TS.
repeat split; Col.
intro.
induction H5.
assert(TS O A B P).
{
  repeat split; Col.
  exists O.
  split; Col.
}
apply l9_9 in H6.
contradiction.
apply H2.
assert_diffs.
apply(out_conga A O B A O B A P A B);
try(apply out_trivial; auto).
apply conga_refl; auto.
repeat split; auto.
induction H5.
right; Between.
left; auto.
Between.
unfold InAngle in *.
spliter.
ex_and H7 T.
exists T.
split; auto.
induction H8.
treat_equalities; Col.
assert(HCop : Coplanar A O P P').
{
  apply coplanar_trans_1 with B; Col.
    Cop.
  exists T.
  left.
  split; Col.
}
assert(HH:= conga_cop__or_out_ts A O P P' HCop H3).
induction HH.
assert(Out O P T) by (apply (l6_7) with P'; finish).
Col.
exfalso.
assert(A <> T).
{
  intro.
  treat_equalities.
  unfold TS in H9.
  spliter.
  apply H9.
  Col.
}
assert(OS O A T P').
{
  apply out_one_side.
  left.
  intro.
  apply H4.
  ColR.
  auto.
}
assert(OS A O B T).
{
  apply out_one_side.
  left; Col.
  repeat split; auto.
  intro.
  treat_equalities.
  apply H4; Col.
}
assert(OS O A B P').
{
  apply (one_side_transitivity _ _ _  T); finish.
}
assert(TS O A B P) by (apply(l9_8_2 _ _ P');finish).
apply l9_9 in H14.
contradiction.
Qed.

Lemma conga_os__out : forall O A B C, CongA A O B A O C -> OS O A B C -> Out O B C.
Proof.
intros.
assert(HH:= conga_cop__or_out_ts A O B C).
induction HH; Cop.
apply invert_two_sides in H1.
apply l9_9 in H1.
contradiction.
Qed.


Lemma ex_suppa : forall A B C, A <> B -> B <> C -> exists D E F, SuppA A B C D E F.
Proof.
intros.
destruct (segment_construction A B A B) as [A' []].
exists C, B, A'.
split; auto.
exists A'.
split; trivial.
assert_diffs.
apply conga_refl; auto.
Qed.

Lemma suppa_distincts : forall A B C D E F, SuppA A B C D E F ->
  A <> B /\ B <> C /\ D <> E /\ E <> F.
Proof.
unfold SuppA.
intros; spliter.
ex_and H0 A'.
apply conga_distinct in H1; spliter.
repeat split; auto.
Qed.

Lemma suppa_right_comm : forall A B C D E F, SuppA A B C D E F -> SuppA A B C F E D.
Proof.
unfold SuppA.
intros; spliter.
split; auto.
ex_and H0 A'.
exists A'.
split; auto.
apply conga_left_comm, H1.
Qed.

Lemma suppa_left_comm : forall A B C D E F, SuppA A B C D E F -> SuppA C B A D E F.
Proof.
unfold SuppA.
intros; spliter.
ex_and H0 A'.
apply conga_distinct in H1.
spliter.
split; auto.
destruct (segment_construction C B C B) as [C' []].
exists C'.
split; auto.
apply conga_trans with C B A'; trivial.
assert_diffs.
apply conga_left_comm, l11_14; Between.
Qed.

Lemma suppa_comm : forall A B C D E F, SuppA A B C D E F -> SuppA C B A F E D.
Proof.
intros.
apply suppa_left_comm, suppa_right_comm, H.
Qed.

Lemma suppa_sym : forall A B C D E F, SuppA A B C D E F -> SuppA D E F A B C.
Proof.
unfold SuppA.
intros; spliter.
ex_and H0 A'.
apply conga_distinct in H1; spliter.
split; auto.
destruct (segment_construction D E D E) as [D' []].
exists D'.
split; auto.
assert_diffs.
apply conga_right_comm, l11_13 with A' D; Between.
apply conga_sym, conga_right_comm, H1.
Qed.

Lemma conga2_suppa__suppa : forall A B C D E F A' B' C' D' E' F',
  CongA A B C A' B' C' -> CongA D E F D' E' F' -> SuppA A B C D E F ->
  SuppA A' B' C' D' E' F'.
Proof.
intros.
assert (SuppA A B C D' E' F').
{
  unfold SuppA in *; spliter.
  split; auto.
  ex_and H2 A0.
  exists A0.
  split; trivial.
  apply conga_trans with D E F; [apply conga_sym|]; assumption.
}
apply suppa_sym.
apply suppa_sym in H2.
unfold SuppA in H2; spliter.
split; auto.
ex_and H3 D0.
exists D0.
split; trivial.
apply conga_trans with A B C; [apply conga_sym|]; assumption.
Qed.

Lemma suppa2__conga456 : forall A B C D E F D' E' F',
  SuppA A B C D E F -> SuppA A B C D' E' F' -> CongA D E F D' E' F'.
Proof.
unfold SuppA.
intros; spliter.
ex_and H2 A'.
ex_and H1 A''.
apply conga_trans with C B A'; trivial.
apply conga_trans with C B A''; [|apply conga_sym, H4].
apply conga_distinct in H3.
apply conga_distinct in H4.
spliter.
apply out2__conga.
  apply out_trivial; auto.
  apply l6_2 with A; Between.
Qed.

Lemma suppa2__conga123 : forall A B C D E F A' B' C',
  SuppA A B C D E F -> SuppA A' B' C' D E F -> CongA A B C A' B' C'.
Proof.
intros.
apply (suppa2__conga456 D E F); apply suppa_sym; assumption.
Qed.

Lemma bet_out__suppa : forall A B C D E F, A <> B -> B <> C ->
  Bet A B C -> Out E D F -> SuppA A B C D E F.
Proof.
intros.
split; auto.
exists C.
split; auto.
apply l11_21_b; trivial.
apply out_trivial; auto.
Qed.

Lemma bet_suppa__out : forall A B C D E F,
  Bet A B C -> SuppA A B C D E F -> Out E D F.
Proof.
intros.
assert (Hd := H0).
apply suppa_distincts in Hd; spliter.
apply (l11_21_a C B C).
  apply out_trivial; auto.
apply (suppa2__conga456 A B C); trivial.
split; auto.
exists C.
split; trivial.
apply conga_refl; auto.
Qed.

Lemma out_suppa__bet : forall A B C D E F,
  Out B A C -> SuppA A B C D E F -> Bet D E F.
Proof.
intros.
destruct (segment_construction A B A B) as [B' []].
apply (bet_conga__bet A B B'); trivial.
apply (suppa2__conga456 A B C); trivial.
assert_diffs.
apply suppa_sym, bet_out__suppa; auto.
Qed.

Lemma per_suppa__per : forall A B C D E F,
  Per A B C -> SuppA A B C D E F -> Per D E F.
Proof.
unfold SuppA.
intros; spliter.
ex_and H1 A'.
apply (l11_17 C B A'); [|apply conga_sym, H2].
apply conga_distinct in H2; spliter.
apply per_col with A; Perp; Col.
Qed.

Lemma per2__suppa : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
  Per A B C -> Per D E F -> SuppA A B C D E F.
Proof.
intros.
destruct (ex_suppa A B C) as [D' [E' [F']]]; auto.
apply (conga2_suppa__suppa A B C D' E' F'); try apply conga_refl; auto.
assert (Hd := H5).
apply suppa_distincts in Hd; spliter.
apply l11_16; auto.
apply (per_suppa__per A B C); assumption.
Qed.

Lemma suppa__per : forall A B C, SuppA A B C A B C -> Per A B C.
Proof.
unfold SuppA.
intros; spliter.
ex_and H0 A'.
apply l8_2, l11_18_2 with A'; trivial.
apply conga_left_comm, H1.
Qed.

Lemma acute_suppa__obtuse : forall A B C D E F,
  Acute A B C -> SuppA A B C D E F -> Obtuse D E F.
Proof.
unfold SuppA.
intros; spliter.
ex_and H1 A'.
apply (conga_obtuse__obtuse C B A'); [|apply conga_sym, H2].
apply conga_distinct in H2; spliter.
apply obtuse_sym, (acute_bet__obtuse A); auto.
Qed.

Lemma obtuse_suppa__acute : forall A B C D E F,
  Obtuse A B C -> SuppA A B C D E F -> Acute D E F.
Proof.
unfold SuppA.
intros; spliter.
ex_and H1 A'.
apply (acute_conga__acute C B A'); [|apply conga_sym, H2].
apply conga_distinct in H2; spliter.
apply acute_sym, (bet_obtuse__acute A); auto.
Qed.

Lemma lea_suppa2__lea : forall A B C D E F A' B' C' D' E' F',
  SuppA A B C A' B' C' -> SuppA D E F D' E' F' -> LeA A B C D E F ->
  LeA D' E' F' A' B' C'.
Proof.
unfold SuppA.
intros; spliter.
ex_and H3 A0.
ex_and H2 D0.
apply (l11_30 F E D0 C B A0); [|apply conga_sym; assumption..].
apply conga_distinct in H4.
apply conga_distinct in H5.
spliter.
apply lea_comm, l11_36 with D A; Between.
Qed.

Lemma lta_suppa2__lta : forall A B C D E F A' B' C' D' E' F',
  SuppA A B C A' B' C' -> SuppA D E F D' E' F' -> LtA A B C D E F ->
  LtA D' E' F' A' B' C'.
Proof.
unfold SuppA.
intros; spliter.
ex_and H3 A0.
ex_and H2 D0.
apply (conga_preserves_lta F E D0 C B A0); [apply conga_sym; assumption..|].
apply conga_distinct in H4.
apply conga_distinct in H5.
spliter.
apply lta_comm, bet2_lta__lta with A D; Between.
Qed.

Lemma suppa_dec : forall A B C D E F, SuppA A B C D E F \/ ~ SuppA A B C D E F.
Proof.
intros.
induction (eq_dec_points A B).
  right; intros []; auto.
induction (eq_dec_points B C).
  right; intro Habs; apply suppa_distincts in Habs; spliter; auto.
destruct (ex_suppa A B C) as [D' [E' [F']]]; auto.
induction (conga_dec D' E' F' D E F).
  left; apply (conga2_suppa__suppa A B C D' E' F'); try apply conga_refl; auto.
  right; intro; apply H2, (suppa2__conga456 A B C); assumption.
Qed.

End T11_2.

Ltac not_exist_hyp4 A B C D E F G H := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H].

Ltac not_exist_hyp5 A B C D E F G H I J := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H | not_exist_hyp_comm I J].

Ltac not_exist_hyp6 A B C D E F G H I J K L := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H | not_exist_hyp_comm I J | not_exist_hyp_comm K L].

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D (swap_diff B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H (swap_diff B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H (swap_diff C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_at ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= conga_diff1 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= conga_diff2 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= conga_diff45 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= conga_diff56 A B C A' B' C' H);clean_reap_hyps

      | H:(InAngle ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := inangle_distincts A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:LeA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lea_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:LtA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lta_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Acute ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := acute_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Obtuse ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := obtuse_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:SuppA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(Orth_at ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps
 end.

Hint Resolve conga_refl conga_sym cong3_conga conga_pseudo_refl conga_trivial_1
             conga_right_comm conga_left_comm conga_comm : conga.

Ltac CongA := auto with conga.

Hint Resolve l11_31_1 l11_31_2 lta__lea lea_comm lea_right_comm lea_left_comm
             lea_asym lea121345 inangle__lea conga__lea conga__lea456123 lea_refl
             acute_per__lta obtuse_per__lta acute_obtuse__lta : lea.

Ltac Lea := auto with lea.


Section T11_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma acute_one_side_aux : forall P A O B, 
 OS O A P B -> Acute A O P -> Perp O A B O ->
 OS O B A P.
Proof.
intros P A O B HOS.
intros.
unfold Acute in H.
ex_and H A'.
ex_and H1 B'.
ex_and H C'.

assert(Per A O B).
{
  apply perp_perp_in in H0.
  apply perp_in_comm in H0.
  apply perp_in_per in H0.
  assumption.
}
assert(CongA A' B' C' A O B).
{
  assert_diffs.
  apply l11_16; auto.
}
assert(LtA A O P A O B).
{
  apply(conga_preserves_lta A O P A' B' C' A O P A O B); auto.
  assert_diffs.
  apply conga_refl; auto.
}

assert(~Col P O B).
{
  intro.
  assert(Per A O P).
  {
    assert_diffs.
    apply (per_col A O B P); Col.
  }
  unfold LtA in H4.
  spliter.
  apply H7.
  assert_diffs.
  apply(l11_16); auto.
}

assert(NC:~Col A O P).
{
  unfold OS in HOS.
  ex_and HOS R.
  unfold TS in H6.
  spliter.
  Col.
}

assert(TS O B A P \/ OS O B A P).
{
  apply(cop__one_or_two_sides O B A P); Cop.
  apply perp_not_col in H0; Col.
}
induction H6.
unfold TS in H6.
spliter.
ex_and H8 T.

assert(O <> T).
{
  intro.
  treat_equalities.
  assert(LeA A O B A O P).
  {
    assert_diffs.
    apply(l11_31_2 A O B A O P); auto.
  }
  assert(~LtA A O P A O B).
  {
    apply lea__nlta.
    assumption.
  }
  contradiction.
}

assert(InAngle T A O P).
{
  unfold InAngle.
  assert_diffs.
  repeat split; auto.
  exists T.
  split; auto.
  right.
  finish.
}


assert(OS O A T P).
{
  apply invert_one_side.
  apply out_one_side.
  right; Col.
  assert_diffs.
  repeat split; auto.
  apply perp_not_col in H0.
  intro;  treat_equalities.
  apply H0; Col.
}

assert(OS O A T B).
{
  apply (one_side_transitivity _ _ _ P); auto.
}

destruct(l9_19 O A T B O); Col.
apply H14 in H13.
spliter.
assert(InAngle B A O P).
{
  assert_diffs.
  apply(l11_25 T A O P A P B H11); auto;
  try(apply out_trivial; auto).
  apply l6_6; auto.
}

apply inangle__lea in H17.

apply lea__nlta in H17.
contradiction.
assumption.
Qed.

Lemma acute_one_side_aux0 : forall P A O B, Col A O P -> Acute A O P -> Perp O A B O -> OS O B A P.

Proof.
intros.
assert(LtA A O P A O B).
{
  assert_diffs.
  apply(acute_per__lta A O P A O B H0); auto.
  apply perp_perp_in in H1.
  apply perp_in_comm in H1.
  apply perp_in_per in H1.
  assumption.
}

assert(Out O A P).
{
  assert_diffs.
  induction H.
  assert(LeA A O B A O P).
  {
    apply l11_31_2; auto.
  }
  apply lea__nlta in H3.
  contradiction.
  repeat split; auto.
  induction H.
  right; Between.
  left; Between.
}

apply(out_one_side O B A P); auto.
left.
apply perp_not_col in H1.
Col.
Qed.

Lemma acute_cop_perp__one_side :
  forall P A O B, Acute A O P -> Perp O A B O -> Coplanar A B O P -> OS O B A P.

Proof.
intros.
induction(col_dec A O P).
apply(acute_one_side_aux0); auto.
assert(~Col A O B).
{
  apply perp_not_col in H0.
  Col.
}
assert(TS O A P B \/ OS O A P B).
{
  apply(cop__one_or_two_sides O A P B); Col.
  Cop.
}

induction H4.
assert(HC:=symmetric_point_construction B O).
ex_and HC Bs.
unfold Midpoint in *.
spliter.
assert(TS O A Bs B).
{
  repeat split; Col.
  intro.
  apply H3.
  ColR.
  exists O.
  split; Between.
}
assert(OS O A P Bs).
{
  apply(l9_8_1 _ _ _ _ B); auto.
}
assert(Perp O A Bs O ).
{
  apply perp_sym.
  apply perp_comm.
  apply (perp_col _ B); Perp.
  intro.
  treat_equalities.
  apply H3; Col.
  Col.
}
assert(OS O Bs A P).
{
  apply(acute_one_side_aux P A O Bs); auto.
}
apply(col_one_side _ Bs); Col.
intro.
treat_equalities.
apply H3; Col.

apply(acute_one_side_aux P A O B); auto.
Qed.

End T11_3.

Section T11_2D.

Context `{T2D:Tarski_2D}.

Lemma conga__or_out_ts : forall A B C C',
 CongA A B C A B C' -> Out B C C' \/ TS A B C C'.
Proof.
  intros A B C C'.
  apply conga_cop__or_out_ts, all_coplanar.
Qed.

Lemma conga_out_reflectl__out : forall A B C P T T',
  ~ Out B A C -> CongA P B A P B C -> Out B A T -> ReflectL T T' B P -> Out B C T'.
Proof.
  intros A B C P T T' H.
  assert (H1 := all_coplanar A B C P).
  apply conga_cop_out_reflectl__out; assumption.
Qed.

Lemma col_conga_reflectl__col : forall A B C P T T',
  ~ Out B A C -> CongA P B A P B C -> Col B A T -> ReflectL T T' B P -> Col B C T'.
Proof.
  intros A B C P T T' H.
  assert (H1 := all_coplanar A B C P).
  apply col_conga_cop_reflectl__col; assumption.
Qed.

Lemma conga2__col : forall A B C P P',
  ~ Out B A C -> CongA P B A P B C -> CongA P' B A P' B C -> Col B P P'.
Proof.
  intros A B C P P' H H1 H2.
  assert (H3 := all_coplanar A B P P').
  assert (H4 := all_coplanar B C P P').
  apply conga2_cop2__col with A C; assumption.
Qed.

Lemma inangle__ex_col_inangle : forall A B C P Q, ~ Out B A C -> InAngle P A B C ->
  exists R, InAngle R A B C /\ P <> R /\ Col P Q R.
Proof.
  intros.
  apply cop_inangle__ex_col_inangle; [assumption..|].
  apply all_coplanar.
Qed.

Lemma acute_perp__one_side : forall P A O B, Acute A O P -> Perp O A B O -> OS O B A P.
Proof.
  intros.
  apply acute_cop_perp__one_side; [assumption..|].
  apply all_coplanar.
Qed.

End T11_2D.