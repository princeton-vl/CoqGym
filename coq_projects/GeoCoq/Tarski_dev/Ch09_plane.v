Require Export GeoCoq.Tarski_dev.Ch08_orthogonality.
Require Export GeoCoq.Tarski_dev.Annexes.coplanar.

Ltac clean_reap_hyps :=
  clean_duplicated_hyps;
  repeat
  match goal with
   | H:(Midpoint ?A ?B ?C), H2 : Midpoint ?A ?C ?B |- _ => clear H2
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
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp ?A ?B ?C ?D), H2 : Perp ?B ?A ?D ?C |- _ => clear H2
   | H:(?A<>?B), H2 : (?B<>?A) |- _ => clear H2
   | H:(Per ?A ?D ?C), H2 : (Per ?C ?D ?A) |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?A ?B ?D ?C |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?C ?D ?A ?B |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?C ?D ?B ?A |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?D ?C ?B ?A |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?D ?C ?A ?B |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?B ?A ?C ?D |- _ => clear H2
   | H:(Perp_at ?X ?A ?B ?C ?D), H2 : Perp_at ?X ?B ?A ?D ?C |- _ => clear H2
end.

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
   | H:(Per ?X1 ?X2 ?X2)     |- _ => clear H
   | H:(Per ?X1 ?X1 ?X2)     |- _ => clear H
   | H:(Midpoint ?X1 ?X1 ?X1) |- _ => clear H
end.

Ltac clean := clean_trivial_hyps;clean_reap_hyps.

Section T9.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ts_distincts : forall A B P Q, TS A B P Q ->
  A <> B /\ A <> P /\ A <> Q /\ B <> P /\ B <> Q /\ P <> Q.
Proof.
  intros A B P Q HTS.
  destruct HTS as [HNCol1 [HNCol2 [T [HCol HBet]]]].
  assert_diffs.
  repeat split; auto.
  intro; treat_equalities; auto.
Qed.

Lemma l9_2 : forall A B P Q, TS A B P Q -> TS A B Q P.
Proof.
    unfold TS.
    intros.
    spliter.
    repeat split; try Col.
    destruct H1 as [T [HCol1 HCol2]].
    exists T; Col; Between.
Qed.

Lemma invert_two_sides : forall A B P Q,
 TS A B P Q -> TS B A P Q.
Proof with finish.
    unfold TS.
    intros.
    spliter.
    repeat split...
    ex_and H1 T.
    exists T;split...
Qed.


Lemma l9_3 : forall P Q A C M R B,
 TS P Q A C -> Col M P Q ->
 Midpoint M A C -> Col R P Q ->
 Out R A B -> TS P Q B C.
Proof with finish.
    intros.
    unfold TS in *.
    assert (~ Col A P Q).
      spliter.
      assumption.
    spliter.
    clear H.
    assert (P <> Q).
      intro.
      subst Q.
      Col.
    ex_and H6 T.
    show_distinct A C.
      intuition.
    assert (T = M).
      assert_bets.
      assert_cols.
      eapply l6_21 with P Q A C...
    subst T.
    repeat split...
      induction(eq_dec_points C M).
        subst M.
        intuition.
      intro.
      clear H0.
      assert (B <> R).
        intro.
        subst B.
        unfold Out in H3.
        spliter.
        absurde.
      assert (Col P R B) by ColR.
      assert (Col P R A).
        induction (eq_dec_points P B).
          subst B.
          assert_cols...
        apply col_permutation_2.
        eapply col_transitivity_2.
          apply H0.
          assert_cols...
        Col.
      induction (eq_dec_points P R).
        subst R.
        apply H4.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ B).
          assert_diffs;intuition.
          apply col_permutation_4.
          assumption.
        assert_cols...
      assert (Col P B A ).
        eapply col_transitivity_1.
          apply H13.
          assumption.
        assumption.
      induction (eq_dec_points P B).
        subst B.
        apply H4.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ R).
          apply H0.
          apply col_permutation_4.
          assumption.
        unfold Out in H3.
        spliter.
        unfold Col.
        induction H16.
          right; left.
          assumption.
        right;right.
        Between.
      apply H4.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H15.
        Col.
      assumption.
    induction H3.
    spliter.
    induction H10.
      double B M B'.
      double R M R'.
      assert (Bet B' C R').
        eapply l7_15.
          apply H11.
          apply H1.
          apply H12.
        Between.
      assert (exists X, Bet M X R' /\ Bet C X B).
        eapply inner_pasch.
          (* assert_bets.
          Between.
          *)
          apply midpoint_bet.
          apply H11.
        apply between_symmetry.
        assumption.
      ex_and H14 X.
      exists X.
      split.
        assert (Col P M R ).
          eapply col_transitivity_1.
            apply H.
            Col.
          Col.
        assert (Col Q M R).
          eapply (col_transitivity_1 _ P).
            auto.
            Col.
          Col.
        induction (eq_dec_points M X).
          subst X.
          assumption.
        show_distinct M R'.
          intuition.
        assert (M <> R).
          intro.
          subst R.
          eapply (symmetric_point_uniqueness) in H12.
            apply H19.
            apply H12.
          apply l7_3_2.
        apply col_permutation_2.
        ColR.
      Between.
    assert (exists X, Bet B X C /\ Bet M X R).
      eapply inner_pasch.
        apply H10.
      Between.
    ex_and H11 X.
    exists X.
    induction (eq_dec_points M R).
      subst R.
      apply between_identity in H12.
      subst X.
      split; assumption.
    induction (eq_dec_points R X).
      subst X.
      split; assumption.
    split.
      induction (eq_dec_points X M).
        subst X.
        assumption.
      assert (Col P M R ).
        eapply col_transitivity_1.
          apply H.
          Col.
        Col.
      assert (Col X P Q).
        apply col_permutation_2.
        ColR.
      assumption.
    assumption.
Qed.

(*
Lemma sym_sym : forall A C A', Midpoint C A A' -> ReflectP A' A C.
Proof.
    intros.
    apply l7_2.
    assumption.
Qed.
*)

Lemma mid_preserves_col : forall A B C M A' B' C',
  Col A B C ->
  Midpoint M A A' ->
  Midpoint M B B' ->
  Midpoint M C C' ->
  Col A' B' C'.
Proof.
    intros.
    induction H.
      assert (Bet A' B' C').
        eapply l7_15 with A B C M;auto.
      assert_cols;Col.
    induction H.
      assert (Bet B' C' A').
        eapply l7_15 with B C A M;auto.
      assert_cols;Col.
    assert (Bet C' A' B').
      eapply l7_15 with C A B M;auto.
    assert_cols;Col.
Qed.

Lemma per_mid_per : forall A B X Y M,
   A <> B -> Per X A B ->
   Midpoint M A B -> Midpoint M X Y ->
   Cong A X B Y /\ Per Y B A.
Proof.
    intros.
    assert (Cong A X B Y).
      eapply l7_13.
        apply l7_2.
        apply H1.
      apply l7_2.
      assumption.
    split.
      assumption.
    unfold Per in H0.
    ex_and H0 B'.
    double A B A'.
    assert (Cong B X A Y).
      eapply l7_13.
        apply H1.
      apply l7_2.
      assumption.
    assert (OFSC B A B' X A B A' Y).
      unfold OFSC.
      repeat split.
        apply midpoint_bet.
        assumption.
        apply midpoint_bet.
        assumption.
        apply cong_pseudo_reflexivity.
        unfold Midpoint in *.
        spliter.
        eapply cong_transitivity.
          apply cong_symmetry.
          apply H8.
        apply cong_left_commutativity.
        assumption.
        assumption.
      assumption.
    unfold Per.
    exists A'.
    split.
      assumption.
    assert (Cong B' X A' Y).
      eapply five_segment_with_def.
        apply H7.
      intro.
      apply H.
      subst B.
      reflexivity.
    eapply cong_transitivity.
      apply cong_commutativity.
      apply cong_symmetry.
      apply H6.
    eapply cong_transitivity.
      apply H4.
    apply cong_commutativity.
    assumption.
Qed.


Lemma sym_preserve_diff : forall A B M A' B',
 A <> B -> Midpoint M A A' -> Midpoint M B B' -> A'<> B'.
Proof.
    intros.
    intro.
    subst B'.
    assert (A = B).
      eapply l7_9.
        apply H0.
      assumption.
    contradiction.
Qed.


Lemma l9_4_1_aux : forall P Q A C R S M,
 Le S C R A ->
 TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> Midpoint M R S ->
 (forall U C',Midpoint M U C' -> (Out R U A <-> Out S C C')).
Proof.
    intros.
    induction (eq_dec_points R S).
      subst S.
      apply l7_3 in H5.
      subst R.
      unfold TS in H0.
      assert (~ Col A P Q).
        spliter.
        assumption.
      spliter.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H8 T.
      induction (eq_dec_points M T).
        subst T.
        split.
          intro.
          unfold Out in *.
          spliter.
          repeat split.
            intro.
            subst C.
            apply perp_distinct in H4.
            spliter.
            absurde.
            intro.
            subst C'.
            apply l7_2 in H6.
            eapply (symmetric_point_uniqueness _ _ M) in H6.
              apply H10.
              apply sym_equal.
              apply H6.
            apply l7_3_2.
          induction H12.
            assert (Bet U M C).
              eapply between_exchange3.
                apply between_symmetry.
                apply H12.
              assumption.
            unfold Midpoint in H13.
            spliter.
            eapply l5_2.
              apply H10.
              assumption.
            apply midpoint_bet.
            assumption.
          assert (Bet U M C).
            eapply outer_transitivity_between2.
              apply between_symmetry.
              apply H12.
              assumption.
            assumption.
          eapply l5_2.
            apply H10.
            assumption.
          unfold Midpoint in H6.
          spliter.
          assumption.
        intro.
        unfold Out in *.
        spliter.
        repeat split.
          intro.
          subst U.
          eapply is_midpoint_id in H6.
          subst C'.
          apply H11.
          reflexivity.
          intro.
          subst A.
          apply perp_distinct in H2.
          spliter.
          apply H13.
          reflexivity.
        unfold Midpoint in H6.
        spliter.
        assert (Bet A M C').
          induction H12.
            eapply outer_transitivity_between.
              apply H9.
              assumption.
            intro.
            apply H10.
            subst C.
            reflexivity.
          eapply between_inner_transitivity.
            apply H9.
          assumption.
        eapply l5_2.
          apply H11.
          apply between_symmetry.
          assumption.
        apply between_symmetry.
        assumption.
      assert (Perp M T A M) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H11.
      apply perp_in_comm in H11.
      eapply perp_in_per in H11.
      assert (Perp M T C M) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H12.
      apply perp_in_comm in H12.
      eapply perp_in_per in H12.
      assert (M = T).
        apply (l8_6 C M T A).
          3:Between.
          apply l8_2;auto.
        apply l8_2;auto.
      subst T.
      split.
        intro.
        unfold Out in *.
        spliter.
        repeat split.
          intro.
          subst C.
          apply perp_distinct in H4.
          spliter.
          absurde.
          intro.
          subst C'.
          intuition.
        intuition.
      intuition.
    (*   R <> S  *)
    unfold Le in H.
    ex_and H D.
    assert (C <> S).
      intro.
      subst S.
      apply perp_distinct in H4.
      spliter.
      absurde.
    assert (R <> D).
      intro.
      subst D.
      apply cong_identity in H8.
      apply H9.
      subst S.
      reflexivity.
    assert (Perp R S A R).
      eapply perp_col2.
        apply H2.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert(exists M, Midpoint M S R /\ Midpoint M C D).
      unfold TS in H0.
      assert (~ Col A P Q).
        spliter.
        assumption.
      spliter.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H14 T.
      eapply (l8_24 S R C A D T).
        apply perp_sym.
        apply perp_left_comm.
        eapply perp_col2.
          apply H4.
          assumption.
          apply col_permutation_1.
          assumption.
          apply col_permutation_1.
          assumption.
        apply perp_right_comm.
        apply perp_sym.
        assumption.
        eapply col3.
          apply H0.
          apply col_permutation_1.
          assumption.
          apply col_permutation_1.
          assumption.
        apply col_permutation_1.
        assumption.
        apply between_symmetry.
        assumption.
        assumption.
      assumption.
    ex_and H12 M'.
    apply l7_2 in H12.
    assert (M = M').
      eapply l7_17.
        apply H5.
      apply H12.
    subst M'.
    split.
      intro.
      unfold Out in H14.
      spliter.
      unfold Out.
      repeat split.
        assumption.
        eapply sym_preserve_diff.
          2:apply H6.
          apply H14.
        assumption.
      induction H16.
        assert(Bet R U D \/ Bet R D U).
          eapply l5_3.
            apply H16.
          assumption.
        induction H17.
          right.
          eapply l7_15.
            apply H5.
            apply H6.
            apply l7_2.
            apply H13.
          assumption.
        left.
        eapply l7_15.
          apply H5.
          apply l7_2.
          apply H13.
          apply H6.
        assumption.
      left.
      eapply l7_15.
        apply H5.
        apply l7_2.
        apply H13.
        apply H6.
      eapply between_exchange4.
        apply H.
      apply H16.
    unfold Out.
    intros.
    spliter.
    repeat split.
      eapply sym_preserve_diff.
        apply H15.
        apply l7_2.
        apply H6.
      apply l7_2.
      assumption.
      intro.
      subst R.
      apply perp_distinct in H11.
      spliter.
      absurde.
    induction H16.
      eapply l5_1.
        apply H10.
        eapply l7_15.
          apply l7_2.
          apply H12.
          apply H13.
          apply l7_2.
          apply H6.
        assumption.
      assumption.
    left.
    eapply between_exchange4.
      eapply l7_15.
        apply l7_2.
        apply H12.
        apply l7_2.
        apply H6.
        apply H13.
      assumption.
    assumption.
Qed.

Lemma per_col_eq : forall A B C, Per A B C -> Col A B C -> B <> C -> A = B.
Proof.
    intros.
    unfold Per in H.
    ex_and H C'.
    assert_bets.
    assert_cols.
    assert (Col A C C') by ColR.
    assert (C = C' \/ Midpoint A C C') by (eapply l7_20;Col).
    induction H6.
      treat_equalities.
      intuition.
    eapply l7_17;eauto.
Qed.


Lemma l9_4_1 : forall P Q A C R S M,
 TS P Q A C -> Col R P Q ->
 Perp P Q A R -> Col S P Q ->
 Perp P Q C S -> Midpoint M R S ->
 (forall U C',Midpoint M U C' -> (Out R U A <-> Out S C C')).
Proof.
    intros.
    assert (Le S C R A \/ Le R A S C).
      apply le_cases.
    induction H6.
      apply (l9_4_1_aux P Q A C R S M); assumption.
    assert((Out R A U <-> Out S C' C) -> (Out R U A <-> Out S C C')).
      intro.
      induction H7.
      split.
        intro.
        eapply l6_6.
        apply H7.
        apply l6_6.
        assumption.
      intro.
      apply l6_6.
      apply H8.
      apply l6_6.
      assumption.
    apply H7.
    assert((Out S C' C <-> Out R A U) -> (Out R A U <-> Out S C' C)).
      intro.
      induction H8.
      split.
        intro.
        apply H9.
        assumption.
      intro.
      apply H8.
      assumption.
    apply H8.
    eapply (l9_4_1_aux).
      assumption.
      apply l9_2.
      apply H.
      assumption.
      assumption.
      assumption.
      assumption.
      apply l7_2.
      apply H4.
    apply l7_2.
    assumption.
Qed.

Lemma mid_two_sides : forall A B M X Y,
 Midpoint M A B -> ~ Col A B X -> Midpoint M X Y ->
 TS A B X Y.
Proof.
    intros A B M X Y HM1 HNCol HM2.
    repeat split; Col.
      assert_diffs.
      assert (X<>Y) by (intro; treat_equalities; assert_cols; Col).
      intro Col; apply HNCol; ColR.
    exists M; split; Col; Between.
Qed.

Lemma col_preserves_two_sides : forall A B C D X Y,
 C <> D -> Col A B C -> Col A B D ->
 TS A B X Y ->
 TS C D X Y.
Proof.
    intros A B C D X Y.
    assert (H := A).
    intros.
    unfold TS in *.
    assert (~ Col X A B).
      spliter.
      assumption.
    clear H.
    assert (A <> B).
      intro.
      subst B.
      Col.
    spliter.
    repeat split.
      intro.
      apply H4.
      apply col_permutation_2.
      apply (colx C D); Col.
      intro.
      apply H5.
      apply col_permutation_2.
      apply (colx C D); Col.
    ex_and H6 T.
    exists T.
    split.
      eapply col3.
        apply H.
        apply col_permutation_1.
        assumption.
        assumption.
      assumption.
    assumption.
Qed.


Lemma out_out_two_sides : forall A B X Y U V I,
  A <> B ->
  TS A B X Y ->
  Col I A B -> Col I X Y ->
  Out I X U -> Out I Y V ->
  TS A B U V.
Proof.
    intros.
    unfold TS in *.
    assert (~ Col X A B).
      spliter.
      assumption.
    spliter.
    repeat split.
      intro.
      apply H5.
      unfold Out in H3.
      spliter.
      induction H10.
      ColR.
      ColR.
      intro.
      apply H6.
      unfold Out in H4.
      spliter.
      induction H10.
      ColR.
      ColR.
    ex_and H7 T.
    assert (I = T).
     {
      apply l6_21 with A B X Y; Col.
      intro; treat_equalities; Col.
      }
    subst I.
    exists T.
    split.
      assumption.
    unfold Out in *.
    spliter.
    induction H12; induction H10;
    eauto using outer_transitivity_between2, between_symmetry, between_inner_transitivity, between_exchange3, outer_transitivity_between.
Qed.

Lemma l9_4_2_aux : forall P Q A C R S U V, Le S C R A -> TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> Out R U A -> Out S V C -> TS P Q U V.
Proof.
    intros.
    induction (eq_dec_points R S).
      subst S.
      assert (TT:= H0).
      unfold TS in H0.
      assert (~ Col A P Q).
        spliter.
        assumption.
      spliter.
      clear H0.
      assert (P <> Q).
        intro.
        subst Q.
        Col.
      ex_and H9 T.
      induction (eq_dec_points R T).
        subst T.
        clear H9 H3.
        apply (out_out_two_sides P Q A C U V R); auto using l6_6, bet_col with col.
      assert (Perp R T A R) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H12.
      apply perp_in_comm in H12.
      eapply perp_in_per in H12.
      assert (Perp R T C R) by (eapply perp_col2  with P Q;Col).
      apply perp_perp_in in H13.
      apply perp_in_comm in H13.
      eapply perp_in_per in H13.
      assert (R = T).
        apply (l8_6 C R T A).
          3:Between.
          apply l8_2;auto.
        apply l8_2;auto.
      subst.
      intuition.
    (********* R <> S ***************)
    assert(P <> Q).
      apply perp_distinct in H4.
      spliter.
      assumption.
    assert (TS R S A C).
      eapply (col_preserves_two_sides P Q).
        apply H7.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
      assumption.
    eapply (col_preserves_two_sides R S).
      assumption.
      eapply col_permutation_1.
      eapply col_transitivity_1.
        apply H8.
        apply col_permutation_1.
        assumption.
      apply col_permutation_1.
      assumption.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ P).
        auto.
        apply col_permutation_3.
        assumption.
      apply col_permutation_3.
      assumption.
    assert (Perp R S A R).
      eapply perp_col2.
        apply H2.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert (Perp R S C S).
      eapply perp_col2.
        apply H4.
        assumption.
        apply col_permutation_1.
        assumption.
        apply col_permutation_1.
        assumption.
    assert (HH9:=H9).
    unfold TS in HH9.
    assert (~ Col A R S).
      spliter.
      assumption.
    spliter.
    ex_and H15 T.
    unfold Le in H.
    ex_and H C'.
    assert (exists M, Midpoint M S R /\ Midpoint M C C').
      eapply (l8_24 S R C A C' T).
        apply perp_sym.
        apply perp_left_comm.
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        assumption.
        apply col_permutation_3.
        assumption.
        apply between_symmetry.
        assumption.
        assumption.
      assumption.
    ex_and H18 M.
    double U M U'.
    assert (R <> U).
      intro.
      subst U.
      unfold Out in H5.
      spliter.
      absurde.
    assert (TS R S U U').
      eapply mid_two_sides.
        apply l7_2.
        apply H18.
        intro.
        apply H13.
        eapply col_permutation_2.
        eapply col_transitivity_1.
          apply H21.
          apply col_permutation_5.
          assumption.
        induction H5.
        spliter.
        induction H24.
          unfold Col.
          left.
          assumption.
        unfold Col.
        right; left.
        apply between_symmetry.
        assumption.
      assumption.
    apply l9_2.
    eapply l9_3.
      apply l9_2.
      apply H22.
      unfold Col.
      right; right.
      apply midpoint_bet.
      apply H18.
      apply l7_2.
      assumption.
      apply col_trivial_3.
    assert (forall X Y, Midpoint M X Y -> (Out R X A <-> Out S C Y)).
      eapply l9_4_1.
        apply H9.
        apply col_trivial_1.
        assumption.
        apply col_trivial_3.
        assumption.
      apply l7_2.
      assumption.
    assert (Out R U A <-> Out S C U').
      eapply H23.
      assumption.
    destruct H24.
    eapply l6_7.
      apply l6_6.
      apply H24.
      assumption.
    apply l6_6.
    assumption.
Qed.


Lemma l9_4_2 : forall P Q A C R S U V,
TS P Q A C -> Col R P Q -> Perp P Q A R -> Col S P Q ->
Perp P Q C S -> Out R U A -> Out S V C -> TS P Q U V.
Proof.
    intros.
    assert(Le S C R A \/ Le R A S C) by (apply le_cases).
    induction H6.
      eapply l9_4_2_aux with A C R S;assumption.
    apply l9_2.
    apply l9_2 in H.
    eapply l9_4_2_aux with C A S R;auto.
Qed.

Lemma l9_5 : forall P Q A C R B,
 TS P Q A C -> Col R P Q -> Out R A B -> TS P Q B C.
Proof.
    intros.
    assert (P <> Q).
      unfold TS in H.
      spliter.
      intro.
      subst Q.
      Col.
    assert(exists A0, Col P Q A0 /\ Perp P Q A A0).
      eapply l8_18_existence.
      intro.
      unfold TS in H.
      spliter.
      apply H.
      apply col_permutation_2.
      assumption.
    assert(exists C0, Col P Q C0 /\ Perp P Q C C0).
      eapply l8_18_existence.
      unfold TS in H.
      spliter.
      intro.
      apply H4.
      apply col_permutation_2.
      assumption.
    assert(exists B0, Col P Q B0 /\ Perp P Q B B0).
      eapply l8_18_existence.
      assert (HH1:=H1).
      unfold Out in HH1.
      unfold TS in H.
      spliter.
      intro.
      assert (Col P B R).
        eapply col_transitivity_1.
          apply H2.
          assumption.
        apply col_permutation_1.
        assumption.
      assert (R <> B).
        intro.
        subst B.
        absurde.
      assert(Col R P A ).
        eapply col_transitivity_1.
          apply H12.
          eapply col_permutation_3.
          assumption.
        apply col_permutation_5.
        apply out_col.
        assumption.
      apply H.
      ColR.
    ex_and H3 A'.
    ex_and H4 C'.
    ex_and H5 B'.
    assert (exists M, Midpoint M A' C').
      apply midpoint_existence.
    ex_and H9 M.
    double A M D.
    assert (Out C' D C <-> Out A' A A).
      eapply l9_4_1.
        apply l9_2.
        apply H.
        apply col_permutation_2.
        assumption.
        assumption.
        apply col_permutation_2.
        assumption.
        assumption.
        apply l7_2.
        apply H10.
      apply l7_2.
      assumption.
    destruct H11.
    assert (Out C' D C).
      apply H12.
      unfold Out.
      repeat split.
        intro.
        subst A'.
        apply perp_distinct in H6.
        spliter.
        absurde.
        intro.
        subst A'.
        apply perp_distinct in H6.
        spliter.
        absurde.
      left.
      apply between_trivial.
    assert (TS P Q A D).
      eapply l9_4_2.
        apply H.
        apply col_permutation_2.
        apply H3.
        assumption.
        apply col_permutation_2.
        apply H4.
        apply H7.
        unfold Out.
        repeat split.
          intro.
          subst A'.
          apply perp_distinct in H6.
          spliter.
          absurde.
          intro.
          subst A'.
          apply perp_distinct in H6.
          spliter.
          absurde.
        left.
        apply between_trivial.
      assumption.
    assert (TS P Q B D).
      eapply l9_3.
        apply H14.
        2:apply H9.
        2: apply H0.
        2:assumption.
      induction (eq_dec_points A' C').
        subst C'.
        apply l7_3 in H10.
        subst A'.
        apply col_permutation_2.
        assumption.
      ColR.
    try assumption.
    eapply l9_4_2.
      apply H15.
      2: apply H8.
      apply col_permutation_2.
      assumption.
      apply col_permutation_2.
      apply H4.
      apply perp_sym.
      apply perp_left_comm.
      eapply perp_col.
        intro.
        subst D.
        unfold Out in H13.
        spliter.
        absurde.
        apply perp_sym.
        apply perp_right_comm.
        apply H7.
      apply col_permutation_5.
      apply out_col.
      assumption.
      eapply out_trivial.
      intro.
      subst B.
      apply perp_distinct in H8.
      spliter.
      absurde.
    apply l6_6.
    assumption.
Qed.

(** This lemma used to be an axiom in previous versions of Tarski's axiom system.
    It is a been shown to a theorem by Gupta in his Phd 1965. *)
(** This corresponds to l9_6 in Tarski's book. *)

Lemma outer_pasch : forall A B C P Q,
 Bet A C P -> Bet B Q C -> exists X, Bet A X B /\ Bet P Q X.
Proof.
    intros.
    induction(col_dec P Q C).
      induction(bet_dec P Q C).
        exists A.
        split.
          Between.
        eapply between_exchange4 with C;Between.
      assert (Out Q P C) by (apply l6_4_2;auto).
      exists B.
      split.
        Between.
      unfold Out in H3.
      spliter.
      induction H5.
        apply between_exchange3 with C;Between.
      apply outer_transitivity_between2 with C;Between.
    induction (eq_dec_points B Q).
      subst Q;exists B;Between.
    show_distinct A P.
      intuition.
    show_distinct P Q.
      intuition.
    show_distinct P B.
      intuition.
    assert(TS P Q C B).
      unfold TS.
      repeat split.
        Col.
        assert_cols.
        intro;apply H1; ColR.
      exists Q; split;Col;Between.
    assert_diffs.
    assert (TS P Q A B) by (apply l9_5 with C P;unfold Out;intuition).
    unfold TS in H8.
    spliter.
    ex_and H11 X.
    exists X.
    split.
      assumption.
    assert (exists T, Bet X T P /\ Bet C T B) by (apply inner_pasch with A;Between).
    ex_and H14 T.
    show_distinct B C.
      intuition.
    assert (T = Q).
      apply l6_21 with X P B C; assert_cols;Col.
      intro.
      apply H10.
      eapply col_permutation_2.
      eapply col_transitivity_1 with X.
        2:Col.
        intro.
        treat_equalities.
        apply H10.
        ColR.
      Col.
    subst T;Between.
Qed.

Lemma os_distincts : forall A B X Y, OS A B X Y ->
  A <> B /\ A <> X /\ A <> Y /\ B <> X /\ B <> Y.
Proof.
  intros A B P Q HOS.
  destruct HOS as [Z [HTS1 HTS2]].
  apply ts_distincts in HTS1.
  apply ts_distincts in HTS2.
  spliter.
  repeat split; auto.
Qed.

Lemma invert_one_side : forall A B P Q,
 OS A B P Q -> OS B A P Q.
Proof.
    unfold OS.
    intros.
    ex_and H T.
    exists T.
    split; apply invert_two_sides; assumption.
Qed.

Lemma l9_8_1 : forall P Q A B C, TS P Q A C -> TS P Q B C -> OS P Q A B.
Proof.
    intros.
    unfold OS.
    exists C.
    split; assumption.
Qed.

Lemma not_two_sides_id : forall A P Q, ~ TS P Q A A.
Proof.
    intros.
    intro.
    unfold TS in H.
    spliter.
    ex_and H1 T.
    apply between_identity in H2.
    subst T.
    apply H0.
    apply H1.
Qed.

Lemma l9_8_2 : forall P Q A B C,
 TS P Q A C ->
 OS P Q A B ->
 TS P Q B C.
Proof.
    intros.
    unfold OS in H0.
    ex_and H0 D.
    assert (HH:= H).
    assert (HH0:=H0).
    assert (HH1:=H1).
    unfold TS in HH1.
    assert (P <> Q).
      intro.
      subst Q.
      spliter.
      Col.
    spliter.
    unfold TS in HH0.
    assert (P <> Q).
      intro.
      subst Q.
      spliter.
      Col.
    spliter.
    unfold TS in HH.
    assert (P <> Q).
      intro.
      subst Q.
      spliter.
      Col.
    spliter.
    ex_and H13 T.
    ex_and H9 X.
    ex_and H5 Y.
    assert (exists M , Bet Y M A /\ Bet X M B).
      eapply inner_pasch.
        apply H16.
      apply H15.
    ex_and H17 M.
    assert (A <> D).
      intro.
      subst D.
      apply not_two_sides_id in H0.
      assumption.
    assert (B <> D).
      intro.
      subst D.
      apply not_two_sides_id in H1.
      assumption.
    induction (col_dec A B D).
      induction (eq_dec_points M Y).
        subst M.
        assert (X = Y).
          apply l6_21 with P Q A D; assert_cols; Col; ColR.
        subst Y.
        eapply l9_5.
          apply H.
          apply H9.
        unfold Out.
        repeat split.
          intro.
          subst X.
          apply H11.
          assumption.
          intro.
          subst X.
          apply H3.
          assumption.
        unfold Col in H21.
        induction H21.
          right.
          eapply between_exchange3.
            apply between_symmetry.
            apply H16.
          apply between_symmetry.
          assumption.
        induction H21.
          assert (Bet D B A \/ Bet D A B).
            eapply (l5_1 _ X).
              intro.
              subst X.
              apply H4.
              assumption.
              apply between_symmetry.
              assumption.
            apply between_symmetry.
            assumption.
          induction H22.
            assert (D = B).
              eapply between_equality.
                apply H22.
              apply H21.
            subst D.
            absurde.
          assert (D = A).
            eapply between_equality.
              apply H22.
            apply between_symmetry.
            assumption.
          subst D.
          absurde.
        eapply (l5_2 D).
          intro.
          subst X.
          apply H8.
          assumption.
          apply between_symmetry.
          assumption.
        apply between_symmetry.
        assumption.
      induction (eq_dec_points M X).
        subst M.
        assert (X = Y).
          apply l6_21 with P Q A D; assert_cols; Col; ColR.
        subst Y.
        absurde.
      eapply (l9_5 _ _ M _ X).
        eapply l9_5.
          apply H.
          apply H5.
        unfold Out.
        repeat split.
          intro.
          subst Y.
          apply between_identity in H17.
          subst M.
          absurde.
          assumption.
        right.
        assumption.
        assumption.
      unfold Out.
      assert (Out Y M  A).
        unfold Out.
        repeat split.
          assumption.
          intro.
          subst Y.
          apply H11.
          assumption.
        left.
        assumption.
      repeat split.
        assumption.
        intro.
        subst X.
        apply between_identity in H18.
        subst M.
        absurde.
      left.
      apply H18.
    eapply (l9_5 _ _ M).
      eapply l9_5.
        apply H.
        apply H5.
      unfold Out.
      repeat split.
        intro.
        subst Y.
        apply H7.
        assumption.
        intro.
        subst Y.
        assert(Col B D X).
          eapply (col_transitivity_1 _ M).
            intro.
            subst M.
            apply H3.
            assumption.
            unfold Col.
            left.
            assumption.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        apply H21.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ X).
          intro.
          subst X.
          apply H4.
          assumption.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        apply col_permutation_1.
        assumption.
      right.
      assumption.
      apply H9.
    unfold Out.
    repeat split.
      intro.
      subst X.
      assert (Col A D Y).
        eapply (col_transitivity_1 _ M).
          intro.
          subst M.
          apply H7.
          assumption.
          unfold Col.
          left.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      apply H21.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ Y).
        intro.
        subst Y.
        apply H4.
        assumption.
        apply col_permutation_1.
        assumption.
      unfold Col.
      left.
      apply between_symmetry.
      assumption.
      intro.
      subst X.
      apply H3.
      assumption.
    left.
    assumption.
Qed.

Lemma l9_9 : forall P Q A B, TS P Q A B -> ~ OS P Q A B.
Proof.
    intros.
    intro.
    apply (l9_8_2 P Q A B B ) in H.
      apply not_two_sides_id in H.
      assumption.
    assumption.
Qed.

Lemma l9_9_bis : forall P Q A B, OS P Q A B -> ~ TS P Q A B.
Proof.
    intros.
    intro.
    unfold OS in H.
    ex_and H C.
    assert (OS P Q A B).
      eapply l9_8_1.
        apply H.
      assumption.
    assert (~ OS P Q A B).
      apply l9_9.
      assumption.
    contradiction.
Qed.

Lemma one_side_chara : forall P Q A B,
 OS P Q A B -> (forall X, Col X P Q -> ~ Bet A X B).
Proof.
    intros.
    assert(~ Col A P Q).
      destruct H as [R [[] _]]; assumption.
    assert(~ Col B P Q).
      destruct H as [R [_ []]]; assumption.
    apply l9_9_bis in H.
    intro.
    apply H.
    unfold TS.
    repeat split.
      assumption.
      assumption.
    exists X.
    intuition.
Qed.

Lemma l9_10 : forall P Q A,
 ~ Col A P Q -> exists C, TS P Q A C.
Proof.
    intros.
    double A P A'.
    exists A'.
    unfold TS.
    repeat split.
      assumption.
      intro.
      apply H.
      eapply col_permutation_2.
      eapply (col_transitivity_1 _ A').
        intro.
        subst A'.
        apply l7_2 in H0.
        eapply is_midpoint_id in H0.
        subst A.
        apply H.
        assumption.
        apply col_permutation_4.
        assumption.
      unfold Col.
      right; right.
      apply midpoint_bet.
      assumption.
    exists P.
    split.
      apply col_trivial_1.
    apply midpoint_bet.
    assumption.
Qed.



Lemma one_side_reflexivity : forall P Q A,
 ~ Col A P Q -> OS P Q A A.
Proof.
    intros.
    unfold OS.
    double A P C.
    exists C.
    assert (TS P Q A C).
      repeat split.
        assumption.
        intro.
        apply H.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ C).
          intro.
          subst C.
          apply l7_2 in H0.
          apply is_midpoint_id in H0.
          subst A.
          apply H.
          assumption.
          apply col_permutation_4.
          assumption.
        unfold Col.
        right; right.
        apply midpoint_bet.
        assumption.
      exists P.
      split.
        apply col_trivial_1.
      apply midpoint_bet.
      assumption.
    split; assumption.
Qed.


Lemma one_side_symmetry : forall P Q A B,
 OS P Q A B -> OS P Q B A.
Proof.
    unfold OS.
    intros.
    ex_and H C.
    exists C.
    split; assumption.
Qed.

Lemma one_side_transitivity : forall P Q A B C,
OS P Q A B -> OS P Q B C -> OS P Q A C.
Proof.
    intros.
    unfold OS in *.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    split.
      assumption.
    apply l9_2.
    eapply l9_8_2.
      apply l9_2.
      apply H2.
    eapply l9_8_1.
      apply l9_2.
      apply H0.
    apply l9_2.
    assumption.
Qed.

Lemma col_eq : forall A B X Y,
  A <> X -> Col A X Y -> Col B X Y ->
 ~ Col A X B ->
 X = Y.
Proof.
    intros.
    apply eq_sym.
    apply l6_21 with A X B X; assert_diffs; Col.
Qed.

Lemma l9_17 : forall A B C P Q, OS P Q A C -> Bet A B C -> OS P Q A B.
Proof.
    intros.
    induction (eq_dec_points A C).
      subst C.
      apply between_identity in H0.
      subst B.
      assumption.
    assert( HH:= H).
    unfold OS in H.
    ex_and H D.
    assert(HH1:=H).
    unfold TS in H2.
    assert (P <> Q).
      intro.
      subst Q.
      spliter.
      Col.
    spliter.
    unfold TS in H.
    assert (P <> Q).
      intro.
      subst Q.
      spliter.
      Col.
    spliter.
    ex_and H8 X.
    ex_and H5 Y.
    assert (exists T,  Bet B T D /\ Bet X T Y).
      eapply l3_17.
        apply H9.
        apply H10.
      assumption.
    ex_and H11 T.
    unfold OS.
    exists D.
    split.
      assumption.
    unfold TS.
    repeat split.
      apply l9_9_bis in HH.
      intro.
      apply HH.
      unfold TS.
      repeat split.
        assumption.
        assumption.
      exists B.
      split.
        assumption.
      assumption.
      unfold TS in HH1.
      spliter.
      assumption.
    exists T.
    induction (col_dec A C D).
      assert (X = Y).
        apply l6_21 with P Q A D; Col.
          intro.
          subst D.
          assert (OS P Q A A).
            apply one_side_reflexivity.
            assumption.
          apply l9_9_bis in H14.
          contradiction.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ C).
            intro.
            subst D.
            apply between_identity in H10.
            subst Y.
            apply H4.
            assumption.
            assert_cols; Col.
            Col.
      subst Y.
      apply between_identity in H12.
      subst X.
      split.
        assumption.
      assumption.
    split.
      assert (X <> Y).
        intro.
        subst Y.
        apply between_identity in H12.
        subst X.
        apply H13.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ T).
          intro.
          subst D.
          contradiction.
          unfold Col.
          left.
          apply between_symmetry.
          assumption.
        unfold Col.
        left.
        apply between_symmetry.
        assumption.
      apply col_permutation_2.
      apply (colx X Y); Col.
    assumption.
Qed.

Lemma l9_18 : forall X Y A B P,
 Col X Y P -> Col A B P -> (TS X Y A B <-> (Bet A P B /\ ~Col X Y A /\ ~Col X Y B)).
Proof.
    intros.
    split.
      intros.
      unfold TS in H1.
      spliter.
      assert (X <> Y).
        intro.
        subst Y.
        spliter.
        Col.
      ex_and H3 T.
      assert (P=T).
        apply l6_21 with X Y A B; Col.
        intro.
        subst B.
        apply between_identity in H5.
        subst A.
        contradiction.
      subst T.
      repeat split; Col.
    intro.
    unfold TS.
    spliter.
    repeat split; Col.
    exists P.
    split.
      apply col_permutation_2.
      assumption.
    assumption.
Qed.

Lemma l9_19 : forall X Y A B P ,
 Col X Y P -> Col A B P -> (OS X Y A B <-> (Out P A B /\ ~Col X Y A)).
Proof.
    intros.
    split.
      intro.
      assert (HH2:=H1).
      unfold OS in H1.
      ex_and H1 D.
      unfold TS in H2.
      assert (~ Col B X Y).
        spliter.
        assumption.
      spliter.
      clear H3.
      assert (X <> Y).
        intro.
        subst Y.
        spliter.
        Col.
      unfold TS in H1.
      spliter.
      ex_and H5 M.
      ex_and H7 N.
      split.
        unfold Out.
        repeat split.
          intro.
          subst P.
          apply H1.
          apply col_permutation_2.
          assumption.
          intro.
          subst P.
          apply H2.
          apply col_permutation_2.
          assumption.
        unfold Col in H0.
        induction H0.
          right.
          apply between_symmetry.
          assumption.
        induction H0.
          apply False_ind.
          assert (TS X Y A B).
            unfold TS.
            repeat split.
              assumption.
              assumption.
            exists P.
            split.
              apply col_permutation_2.
              assumption.
            apply between_symmetry.
            assumption.
          apply l9_9_bis in HH2.
          contradiction.
        left.
        assumption.
      intro.
      apply H1.
      Col.
    intros.
    spliter.
    assert (exists D, TS X Y A D).
      apply l9_10.
      intro.
      apply H2.
      apply col_permutation_1.
      assumption.
    ex_elim H3 D.
    unfold OS.
    exists D.
    split.
      assumption.
    eapply l9_5.
      apply H4.
      apply col_permutation_2.
      apply H.
    assumption.
Qed.

Lemma one_side_not_col123 :
 forall A B X Y,
  OS A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold OS in H.
    ex_and H C.
    unfold TS in *.
    spliter.
    intro.
    apply H.
    apply col_permutation_2.
    assumption.
Qed.

Lemma one_side_not_col124 :
 forall A B X Y,
  OS A B X Y ->
  ~ Col A B Y.
Proof.
  intros A B X Y HOS.
  apply one_side_not_col123 with X.
  apply one_side_symmetry, HOS.
Qed.

Lemma col_two_sides : forall A B C P Q,
 Col A B C -> A <> C -> TS A B P Q ->
 TS A C P Q.
Proof.
    intros.
    unfold TS in *.
    spliter.
    ex_and H3 T.
    repeat split.
      intro.
      apply H1.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        apply col_permutation_5.
        assumption.
      apply col_permutation_1.
      assumption.
      intro.
      apply H2.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        apply col_permutation_5.
        assumption.
      apply col_permutation_1.
      assumption.
    exists T.
    split.
      apply col_permutation_2.
      apply col_transitivity_1 with B.
        intro.
        subst B.
        Col.
        assumption.
      apply col_permutation_1.
      assumption.
    assumption.
Qed.

Lemma col_one_side : forall A B C P Q,
  Col A B C -> A <> C -> OS A B P Q -> OS A C P Q.
Proof.
    unfold OS.
    intros.
    ex_and H1 T.
    exists T.
    split; eapply (col_two_sides _ B); assumption.
Qed.

Lemma out_out_one_side :
 forall A B X Y Z,
  OS A B X Y ->
  Out A Y Z ->
  OS A B X Z.
Proof.
    intros.
    assert (A <> B).
      unfold OS in H.
      ex_and H C.
      unfold TS in H.
      spliter.
      intro.
      subst B.
      Col.
    prolong Y A Y' A Y.
    assert(OS A B Y Z).
      unfold OS.
      exists Y'.
      split.
        unfold TS.
        repeat split.
          apply one_side_symmetry in H.
          eapply one_side_not_col123 in H.
          intro.
          apply H.
          apply col_permutation_1.
          assumption.
          intro.
          apply one_side_symmetry in H.
          eapply one_side_not_col123 in H.
          apply H.
          assert(Col A B Y).
            eapply (col_transitivity_1 _ Y').
              intro.
              subst Y'.
              apply cong_symmetry in H3.
              apply cong_identity in H3.
              subst Y.
              unfold Out in H0.
              spliter.
              absurde.
              apply col_permutation_4.
              assumption.
            unfold Col.
            right; right.
            assumption.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        assumption.
      unfold TS.
      repeat split.
        intro.
        apply one_side_symmetry in H.
        eapply one_side_not_col123 in H.
        apply H.
        eapply (col_transitivity_1 _ Z).
          intro.
          subst Z.
          unfold Out in H0.
          spliter.
          absurde.
          apply col_permutation_4.
          assumption.
        apply out_col in H0.
        apply col_permutation_5.
        assumption.
        apply one_side_symmetry in H.
        eapply one_side_not_col123 in H.
        intro.
        apply H.
        eapply (col_transitivity_1 _ Y').
          intro.
          subst Y'.
          apply cong_symmetry in H3.
          apply cong_identity in H3.
          subst Y.
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
      unfold Out in H0.
      spliter.
      induction H5.
        apply between_symmetry.
        eapply outer_transitivity_between.
          apply between_symmetry.
          apply H2.
          assumption.
        auto.
      apply between_symmetry.
      eapply between_inner_transitivity.
        apply between_symmetry.
        apply H2; spliter.
      assumption.
    eapply one_side_transitivity.
      apply H.
    apply H4.
Qed.

Lemma out_one_side : forall A B X Y, (~ Col A B X \/ ~ Col A B Y) -> Out A X Y -> OS A B X Y.
Proof.
    intros.
    induction H.
      assert(~ Col X A B).
        intro.
        apply H.
        apply col_permutation_1.
        assumption.
      assert(HH:=one_side_reflexivity A B X H1).
      eapply (out_out_one_side _ _ _ _ _ HH H0).
    assert(~ Col Y A B).
      intro.
      apply H.
      apply col_permutation_1.
      assumption.
    assert(HH:=one_side_reflexivity A B Y H1).
    apply one_side_symmetry.
    eapply (out_out_one_side _ _ _ _ _ HH).
    apply l6_6.
    assumption.
Qed.

Lemma bet_ts__ts : forall A B X Y Z, TS A B X Y -> Bet X Y Z -> TS A B X Z.
Proof.
  intros A B X Y Z [HNCol1 [HNCol2 [T [HT1 HT2]]]] HBet.
  repeat split; trivial.
    intro; assert (Z = T); [apply (l6_21 A B X Y); Col; intro|]; treat_equalities; auto.
  exists T; split; eBetween.
Qed.

Lemma bet_ts__os : forall A B X Y Z, TS A B X Y -> Bet X Y Z -> OS A B Y Z.
Proof.
  intros A B X Y Z HTS HBet.
  exists X; split; apply l9_2; trivial.
  apply bet_ts__ts with Y; assumption.
Qed.

Lemma l9_31 :
 forall A X Y Z,
  OS A X Y Z ->
  OS A Z Y X ->
  TS A Y X Z.
Proof.
    intros.
    assert(A <> X /\ A <> Z /\ ~ Col Y A X  /\ ~ Col Z A X /\ ~Col Y A Z).
      unfold OS in *.
      ex_and H C.
      ex_and H0 D.
      unfold TS in *.
      spliter.
      split.
        intro.
        subst X.
        Col.
      split.
        intro.
        subst Z.
        Col.
      repeat split; assumption.
    spliter.
    prolong Z A Z' Z A.
    assert(Z' <> A).
      intro.
      subst Z'.
      apply cong_symmetry in H7.
      apply cong_identity in H7.
      subst Z.
      absurde.
    assert(TS A X Y Z').
      eapply (l9_8_2 _ _ Z).
        unfold TS.
        repeat split.
          assumption.
          intro.
          apply H4.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ Z').
            auto.
            apply col_permutation_4.
            assumption.
          apply col_permutation_1.
          apply bet_col.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        assumption.
      apply one_side_symmetry.
      assumption.
    unfold TS in H9.
    assert (~ Col Y A X).
      spliter.
      assumption.
    spliter.
    ex_and H12 T.
    assert(T <> A).
      intro.
      subst T.
      apply H5.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ Z').
        auto.
        apply col_permutation_1.
        apply bet_col.
        assumption.
      apply col_permutation_1.
      apply bet_col.
      assumption.
    assert(OS Y A Z' T).
      eapply out_one_side.
        left.
        intro.
        apply H5.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ Z').
          auto.
          apply bet_col in H6.
          apply col_permutation_1.
          assumption.
        apply col_permutation_1.
        assumption.
      apply l6_6.
      apply bet_out.
        intro.
        subst T.
        contradiction.
      assumption.
    unfold Col in H12.
    induction H12.
      assert(OS Z' Z Y T).
        apply out_one_side.
          left.
          intro.
          apply H5.
          eapply col_permutation_1.
          eapply (col_transitivity_1 _ Z').
            intro.
            subst Z'.
            apply between_identity in H6.
            subst Z.
            apply H4.
            apply col_trivial_1.
            apply col_permutation_4.
            assumption.
          apply bet_col in H6.
          apply col_permutation_5.
          assumption.
        apply l6_6.
        apply bet_out.
          intro.
          subst T.
          apply H11.
          apply bet_col.
          assumption.
        apply between_symmetry.
        assumption.
      assert(OS A Z Y T).
        apply invert_one_side.
        eapply (col_one_side _ Z').
          apply bet_col in H6.
          apply col_permutation_5.
          assumption.
          auto.
        apply invert_one_side.
        assumption.
      assert(TS A Z X T).
        repeat split.
          intro.
          apply H11.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ Z).
            assumption.
            apply col_permutation_1.
            assumption.
          apply bet_col in H6.
          apply col_permutation_4.
          assumption.
          unfold OS in H17.
          ex_and H17 C.
          unfold TS in H18.
          spliter.
          assumption.
        exists A.
        split.
          apply col_trivial_1.
        apply between_symmetry.
        assumption.
      assert(TS A Z Y X).
        eapply l9_8_2.
          eapply l9_2.
          apply H18.
        apply one_side_symmetry.
        assumption.
      apply l9_9 in H19.
      contradiction.
    assert(OS A Z T X).
      apply out_one_side.
        right.
        intro.
        apply H4.
        apply col_permutation_4.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply between_symmetry.
      assumption.
    assert(TS A Y Z' Z).
      repeat split.
        unfold OS in H5.
        ex_and H15 C.
        unfold TS in H15.
        spliter.
        intro.
        apply H15.
        apply col_permutation_5.
        assumption.
        intro.
        apply H5.
        apply col_permutation_3.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      apply between_symmetry.
      assumption.
    assert(OS A Y T X).
      apply out_one_side.
        left.
        unfold OS in H15.
        ex_and H15 C.
        unfold TS in H18.
        spliter.
        intro.
        apply H18.
        apply col_permutation_3.
        assumption.
      repeat split.
        assumption.
        auto.
      induction H12.
        right.
        assumption.
      left.
      apply between_symmetry.
      assumption.
    apply invert_one_side in H15.
    assert (OS A Y Z' X).
      eapply one_side_transitivity.
        apply H15.
      assumption.
    eapply l9_8_2.
      apply H17.
    assumption.
Qed.

Lemma col123__nos : forall A B P Q, Col P Q A -> ~ OS P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (~ Col P Q A) by (apply (one_side_not_col123 P Q A B); auto).
  auto.
Qed.

Lemma col124__nos : forall A B P Q, Col P Q B -> ~ OS P Q A B.
Proof.
  intros A B P Q HCol.
  intro HOne.
  assert (HN : ~ OS P Q B A) by (apply col123__nos; auto).
  apply HN; apply one_side_symmetry; auto.
Qed.

Lemma col2_os__os : forall A B C D X Y, C <> D -> Col A B C ->
   Col A B D -> OS A B X Y -> OS C D X Y.
Proof.
  intros A B C D X Y HCD HColC HColD Hos.
  destruct Hos as [Z [Hts1 Hts2]].
  exists Z.
  split; apply (col_preserves_two_sides A B); auto.
Qed.

Lemma os_out_os : forall A B C D C' P , Col A B P -> OS A B C D -> Out P C C' -> OS A B C' D.
Proof.
    intros.
    assert(A <> B /\ ~ Col C A B).
      unfold OS in H0.
      ex_and H0 T.
      unfold TS in H0.
      spliter.
      split.
        intro.
        subst B.
        Col.
      assumption.
    spliter.
    prolong C P T C P.
    assert(P <> T).
      intro.
      subst T.
      treat_equalities.
      Col.
    assert(TS A B C T).
      unfold TS.
      repeat split; Col.
        intro.
        apply H3.
        assert_cols. ColR.
      exists P.
      split; Col.
    assert(TS A B T C').
      apply bet_col in H4.
      eapply (out_out_two_sides _ _ T C _ _ P); Col.
        apply l9_2.
        assumption.
      apply out_trivial.
      auto.
    assert(OS A B C C').
      eapply l9_8_1.
        apply H7.
      apply l9_2.
      assumption.
    eauto using one_side_transitivity, one_side_symmetry.
Qed.

Lemma ts_ts_os : forall A B C D, TS A B C D -> TS C D A B -> OS A C B D.
Proof.
    intros.
    unfold TS in *.
    spliter.
    ex_and H4 T1.
    ex_and H2 T.
    assert(T1 = T).
      assert_cols.
      apply (l6_21 C D A B); Col.
      intro.
      subst B.
      Col.
    subst T1.

assert(OS A C T B).
apply(out_one_side A C T B).
right.
intro.
Col.
unfold Out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst B.
Col.
left.
assumption.

assert(OS C A T D).
apply(out_one_side C A T D).
right.
intro.
apply H0.
Col.
unfold Out.
repeat split.
intro.
subst T.
contradiction.
intro.
subst D.
Col.
left.
assumption.
apply invert_one_side in H8.
apply (one_side_transitivity A C B T).
apply one_side_symmetry.
assumption.
assumption.
Qed.

Lemma two_sides_not_col :
 forall A B X Y,
  TS A B X Y ->
  ~ Col A B X.
Proof.
    intros.
    unfold TS in H.
    spliter.
    intro.
    apply H.
    apply col_permutation_2.
    assumption.
Qed.

Lemma col_one_side_out : forall A B X Y,
 Col A X Y ->
 OS A B X Y ->
 Out A X Y.
Proof.
    intros.
    assert(X <> A /\ Y <> A).
      unfold OS in H0.
      ex_and H0 Z.
      unfold TS in *.
      spliter.
      ex_and H5 T0.
      ex_and H3 T1.
      split.
        intro.
        subst X.
        Col.
      intro.
      subst Y.
      Col.
    spliter.
    unfold Col in H.
    induction H.
      unfold Out.
      repeat split; try assumption.
      left.
      assumption.
    induction H.
      unfold Out.
      repeat split; try assumption.
      right.
      apply between_symmetry.
      assumption.
    assert(TS A B X Y).
      unfold TS.
      assert(HH0 := H0).
      unfold OS in H0.
      ex_and H0 Z.
      unfold TS in *.
      spliter.
      repeat split.
        assumption.
        assumption.
      exists A.
      split.
        apply col_trivial_1.
      apply between_symmetry.
      assumption.
    eapply l9_9 in H3.
    contradiction.
Qed.

Lemma col_two_sides_bet :
 forall A B X Y,
 Col A X Y ->
 TS A B X Y ->
 Bet X A Y.
Proof.
    intros.
    unfold Col in H.
    induction H.
      unfold TS in H0.
      spliter.
      ex_and H2 T.
      apply False_ind.
      apply H1.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ T).
        intro.
        subst T.
        assert(A = X).
          eapply between_equality.
            apply H.
          assumption.
        subst X.
        apply H0.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ X).
        intro.
        subst Y.
        apply between_identity in H3.
        subst X.
        contradiction.
        apply bet_col in H.
        apply col_permutation_3.
        assumption.
      apply col_permutation_2.
      apply bet_col.
      assumption.
    induction H.
      unfold TS in H0.
      spliter.
      ex_and H2 T.
      assert(Col Y A T).
        eapply (col_transitivity_1 _ X).
          intro.
          subst Y.
          apply between_identity in H3.
          subst X.
          contradiction.
          apply col_permutation_4.
          apply bet_col.
          assumption.
        apply col_permutation_2.
        apply bet_col.
        assumption.
      apply False_ind.
      apply H1.
      apply col_permutation_2.
      eapply (col_transitivity_1 _ T).
        intro.
        subst T.
        assert(A = Y).
          eapply between_equality.
            apply between_symmetry.
            apply H.
          apply between_symmetry.
          assumption.
        subst Y.
        apply H1.
        apply col_trivial_1.
        apply col_permutation_4.
        assumption.
      apply col_permutation_1.
      assumption.
    apply between_symmetry.
    assumption.
Qed.

Lemma os_ts1324__os : forall A X Y Z,
  OS A X Y Z ->
  TS A Y X Z ->
  OS A Z X Y.
Proof.
  intros A X Y Z Hos Hts.
  destruct Hts as [HNColXY [HNColYZ [P [HColP HPBet]]]].
  apply (one_side_transitivity _ _ _ P).
  - apply invert_one_side.
    apply one_side_symmetry.
    apply one_side_symmetry in Hos.
    apply one_side_not_col123 in Hos.
    apply out_one_side; Col.
    apply bet_out; Between; intro; subst Z; Col.

  - apply out_one_side.
    right; Col.
    apply (col_one_side_out _ X); Col.
    apply one_side_symmetry in Hos.
    apply (one_side_transitivity _ _ _ Z); auto.
    apply invert_one_side.
    apply one_side_not_col123 in Hos.
    apply out_one_side; Col.
    apply bet_out; auto; intro; subst X; Col.
Qed.

Lemma ts2__ex_bet2 : forall A B C D, TS A C B D -> TS B D A C ->
  exists X, Bet A X C /\ Bet B X D.
Proof.
  intros A B C D HTS HTS'.
  destruct HTS as [HNCol [HNCol1 [X [HCol HBet]]]].
  exists X; split; trivial.
  apply col_two_sides_bet with B; trivial.
  assert_diffs.
  apply invert_two_sides, col_two_sides with D; Col.
  intro; subst X; auto.
Qed.

Lemma ts2__inangle : forall A B C P, TS A C B P -> TS B P A C ->
  InAngle P A B C.
Proof.
  intros A B C P HTS1 HTS2.
  destruct (ts2__ex_bet2 A B C P) as [X [HBet1 HBet2]]; trivial.
  apply ts_distincts in HTS2; spliter.
  repeat split; auto.
  exists X; split; trivial.
  right; apply bet_out; auto.
  intro; subst X.
  apply (two_sides_not_col A C B P HTS1); Col.
Qed.

Lemma out_one_side_1 :
 forall A B C D X,
 ~ Col A B C -> Col A B X -> Out X C D ->
 OS A B C D.
Proof.
    intros.
    induction (eq_dec_points C D).
      subst D.
      apply one_side_reflexivity.
      intro.
      apply H.
      Col.
    prolong C X C' C X.
    exists C'.
    assert(TS A B C C').
      unfold TS.
      repeat split.
        intro.
        apply H.
        Col.
        intro.
        assert(C'=X).
          eapply (l6_21 A B C D).
            assumption.
            assumption.
            Col.
            assumption.
            apply out_col in H1.
            eapply (col_transitivity_1 _ X).
              intro.
              treat_equalities.
              Col5.
              Col.
            Col.
            Col.
        treat_equalities.
        unfold Out in H1.
        tauto.
      exists X.
      split; Col.
    assert(TS A B D C').
      eapply (l9_5 _ _ _ _ X).
        apply H5.
        Col.
      assumption.
    split; assumption.
Qed.

Lemma out_two_sides_two_sides :
 forall A B X Y P PX,
  A <> PX ->
  Col A B PX ->
  Out PX X P ->
  TS A B P Y ->
  TS A B X Y.
Proof.
    intros.
    assert(OS A B P X).
      eapply (col_one_side _ PX).
        Col.
        unfold TS in H2.
        spliter.
        auto.
        intro.
        subst B.
        Col.
      apply invert_one_side.
      apply out_one_side.
        left.
        intro.
        unfold TS in H2.
        spliter.
        apply H2.
        ColR.
      apply l6_6.
      assumption.
    eapply l9_8_2.
      apply H2.
    assumption.
Qed.

Lemma l8_21_bis : forall A B C X Y, X <> Y -> ~ Col C A B -> exists P : Tpoint,
  Cong A P X Y /\ Perp A B P A /\ TS A B C P.
Proof.
intros.
assert (A <> B) by (intro; subst; Col).
assert(HH:= l8_21 A B C H1).
ex_and HH P.
ex_and H2 T.

assert(TS A B C P).
unfold TS.
repeat split; auto.
intro.
apply perp_not_col in H2.
apply H2.
Col.
exists T.
split; Col.
assert(P <> A).
apply perp_distinct in H2.
tauto.

assert(HH:= segment_construction_2 P A X Y H6).
ex_and HH P'.
exists P'.

assert(Perp A B P' A).
apply perp_sym.
apply perp_left_comm.
apply (perp_col _ P).
intro.
subst P'.
apply cong_symmetry in H8.
apply cong_identity in H8.
contradiction.
Perp.
induction H7.

apply bet_col in H7.
Col.
apply bet_col in H7.
Col.

repeat split;auto.
apply perp_not_col in H9.
intro.
apply H9.
Col.

assert(OS A B P P').
apply out_one_side.
left.
apply perp_not_col in H2.
assumption.
repeat split; auto.
apply perp_distinct in H9.
tauto.
assert(TS A B C P').
apply l9_2.
apply(l9_8_2 A B P P' C); auto.
apply l9_2.
assumption.
unfold TS in H11.
spliter.
ex_and H13 T'.
exists T'.
split; auto.
Qed.

Lemma ts__ncol : forall A B X Y, TS A B X Y -> ~Col A X Y \/ ~Col B X Y.
Proof.
intros.
unfold TS in H.
spliter.
ex_and H1 T.

assert(X <> Y).
intro.
treat_equalities.
contradiction.
induction(eq_dec_points A T).
treat_equalities.
right.
intro.
apply H.
ColR.
left.
intro.
apply H.
ColR.
Qed.

Lemma one_or_two_sides_aux : forall A B C D X,
 ~ Col C A B -> ~ Col D A B -> Col A C X -> Col B D X ->
 TS A B C D \/ OS A B C D.
Proof.
    intros.
    assert_diffs.
    assert (A <> X) by (intro; subst; Col).
    assert (B <> X) by (intro; subst; Col).
    assert (~ Col X A B) by (intro; apply H; ColR).
    destruct H1 as [|[|]]; destruct H2 as [|[|]].
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply bet_out; auto.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply bet_out; auto.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_8_2 with X.
        repeat split; Col.
        exists B; split; Col.
      apply out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply l6_6, bet_out; Between.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - right.
      apply one_side_transitivity with X.
        apply out_one_side; Col.
        apply l6_6, bet_out; Between.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_8_2 with X.
        repeat split; Col.
        exists B; split; Col.
      apply out_one_side; Col.
      apply bet_out; Between.
    - left.
      apply l9_2, l9_8_2 with X.
        repeat split; Col.
        exists A; split; Col.
      apply invert_one_side, out_one_side; Col.
      apply l6_6, bet_out; auto.
    - left.
      apply l9_2, l9_8_2 with X.
        repeat split; Col.
        exists A; split; Col.
      apply invert_one_side, out_one_side; Col.
      apply bet_out; Between.
    - right.
      exists X; repeat split; Col.
        exists A; split; finish.
      exists B; split; finish.
Qed.

Lemma cop__one_or_two_sides :
 forall A B C D, Coplanar A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  TS A B C D \/ OS A B C D.
Proof.
    intros.
    ex_and H X.
    induction H2; spliter.
      destruct (or_bet_out C X D) as [|[|]].
        left; repeat split; auto; exists X; split; Col.
        right; apply out_one_side_1 with X; Col.
      exfalso; Col.
    induction H; spliter.
      apply one_or_two_sides_aux with X; assumption.
    induction (one_or_two_sides_aux A B D C X H1 H0 H H2).
      left; apply l9_2; assumption.
    right; apply one_side_symmetry; assumption.
Qed.

Lemma os__coplanar : forall A B C D, OS A B C D -> Coplanar A B C D.
Proof.
  intros A B C D HOS.
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D, HOS).
  destruct (segment_construction C B B C) as [C'[]].
  assert (HT : TS A B D C').
  { apply l9_8_2 with C; [|assumption].
    split; [|split].
      Col.
      intro; apply HNCol; ColR.
      exists B; split; Col.
  }
  destruct HT as [HNCol1 [HNCol2 [T []]]].
  assert (C' <> T) by (intro; treat_equalities; auto).
  destruct (col_dec T B C) as [|HNCol3].
    exists B; left; split; ColR.
  destruct (bet_dec T B A) as [|HOut].
  - apply coplanar_perm_18, ts__coplanar.
    apply l9_8_2 with T.
      repeat split; Col; exists B; split; Col.
    apply out_one_side_1 with C'; Col.
    apply bet_out; Between.
  - apply coplanar_perm_19, ts__coplanar, l9_31; [|apply one_side_symmetry, invert_one_side, HOS].
    apply one_side_transitivity with T.
      apply out_one_side_1 with C'; [intro; apply HNCol3; ColR|Col|apply l6_6, bet_out; Between].
      apply out_one_side; Col; apply not_bet_out; Col.
Qed.

Lemma coplanar_trans_1 : forall P Q R A B,
  ~ Col P Q R -> Coplanar P Q R A -> Coplanar P Q R B -> Coplanar Q R A B.
Proof.
  intros P Q R A B HNCol HCop1 HCop2.
  destruct (col_dec Q R A).
    exists A; left; split; Col.
  destruct (col_dec Q R B).
    exists B; left; split; Col.
  destruct (col_dec Q A B).
    exists Q; left; split; Col.
  assert (HDij : TS Q R A B \/ OS Q R A B).
  { assert (HA : TS Q R P A \/ OS Q R P A) by (apply cop__one_or_two_sides; Col; Cop).
    assert (HB : TS Q R P B \/ OS Q R P B) by (apply cop__one_or_two_sides; Col; Cop).
    destruct HA; destruct HB.
    - right; apply l9_8_1 with P; apply l9_2; assumption.
    - left; apply l9_2, l9_8_2 with P; assumption.
    - left; apply l9_8_2 with P; assumption.
    - right; apply one_side_transitivity with P; [apply one_side_symmetry|]; assumption.
  }
  destruct HDij; [apply ts__coplanar|apply os__coplanar]; assumption.
Qed.

Lemma coplanar_pseudo_trans : forall A B C D P Q R,
  ~ Col P Q R ->
  Coplanar P Q R A ->
  Coplanar P Q R B ->
  Coplanar P Q R C ->
  Coplanar P Q R D ->
  Coplanar A B C D.
Proof.
intros A B C D P Q R HNC HCop1 HCop2 HCop3 HCop4.
elim (col_dec R A B); intro HRAB.

  {
  elim (col_dec R C D); intro HRCD.

    {
    exists R; Col5.
    }

    {
    elim (col_dec Q R C); intro HQRC.

      {
      assert (HQRD : ~ Col Q R D) by (intro; assert_diffs; apply HRCD; ColR).
      assert (HCop5 := coplanar_trans_1 P Q R D A HNC HCop4 HCop1).
      assert (HCop6 := coplanar_trans_1 P Q R D B HNC HCop4 HCop2).
      assert (HCop7 := coplanar_trans_1 P Q R D C HNC HCop4 HCop3).
      assert (HCop8 := coplanar_trans_1 Q R D C A HQRD HCop7 HCop5).
      assert (HCop9 := coplanar_trans_1 Q R D C B HQRD HCop7 HCop6).
      assert (HRDC : ~ Col R D C) by Col.
      assert (HCop := coplanar_trans_1 R D C A B HRDC HCop8 HCop9).
      Cop.
      }

      {
      assert (HCop5 := coplanar_trans_1 P Q R C A HNC HCop3 HCop1).
      assert (HCop6 := coplanar_trans_1 P Q R C B HNC HCop3 HCop2).
      assert (HCop7 := coplanar_trans_1 P Q R C D HNC HCop3 HCop4).
      assert (HCop8 := coplanar_trans_1 Q R C D A HQRC HCop7 HCop5).
      assert (HCop9 := coplanar_trans_1 Q R C D B HQRC HCop7 HCop6).
      assert (HCop := coplanar_trans_1 R C D A B HRCD HCop8 HCop9).
      Cop.
      }
    }
  }

  {
  elim (col_dec Q R A); intro HQRA.

    {
    assert (HQRB : ~ Col Q R B) by (intro; assert_diffs; apply HRAB; ColR).
    assert (HCop5 := coplanar_trans_1 P Q R B A HNC HCop2 HCop1).
    assert (HCop6 := coplanar_trans_1 P Q R B C HNC HCop2 HCop3).
    assert (HCop7 := coplanar_trans_1 P Q R B D HNC HCop2 HCop4).
    assert (HCop8 := coplanar_trans_1 Q R B A C HQRB HCop5 HCop6).
    assert (HCop9 := coplanar_trans_1 Q R B A D HQRB HCop5 HCop7).
    assert (HRBA : ~ Col R B A) by Col.
    assert (HCop := coplanar_trans_1 R B A C D HRBA HCop8 HCop9).
    Cop.
    }

    {
    assert (HCop5 := coplanar_trans_1 P Q R A B HNC HCop1 HCop2).
    assert (HCop6 := coplanar_trans_1 P Q R A C HNC HCop1 HCop3).
    assert (HCop7 := coplanar_trans_1 P Q R A D HNC HCop1 HCop4).
    assert (HCop8 := coplanar_trans_1 Q R A B C HQRA HCop5 HCop6).
    assert (HCop9 := coplanar_trans_1 Q R A B D HQRA HCop5 HCop7).
    assert (HCop := coplanar_trans_1 R A B C D HRAB HCop8 HCop9).
    Cop.
    }
  }
Qed.

Lemma col_cop__cop : forall A B C D E, Coplanar A B C D -> C <> D -> Col C D E -> Coplanar A B C E.
Proof.
  intros A B C D E HCop HCD HCol.
  destruct (col_dec D A C).
    assert (Col A C E) by (apply l6_16_1 with D; Col); Cop.
  apply coplanar_perm_2, coplanar_trans_1 with D; Cop.
Qed.

Lemma bet_cop__cop : forall A B C D E, Coplanar A B C E -> Bet C D E -> Coplanar A B C D.
Proof.
  intros A B C D E HCop HBet.
  destruct (eq_dec_points C E).
    treat_equalities; apply HCop.
  apply col_cop__cop with E; Col.
Qed.

Lemma col2_cop__cop : forall A B C D E F, Coplanar A B C D -> C <> D -> Col C D E -> Col C D F ->
  Coplanar A B E F.
Proof.
  intros A B C D E F HCop HCD HE HF.
  destruct (col_dec C D A).
    exists A; left; split; Col; apply (col3 C D); assumption.
  apply coplanar_pseudo_trans with C D A; Cop.
Qed.

Lemma l9_30 : forall A B C D E F P X Y Z,
  ~ Coplanar A B C P -> ~ Col D E F -> Coplanar D E F P ->
  Coplanar A B C X -> Coplanar A B C Y -> Coplanar A B C Z ->
  Coplanar D E F X -> Coplanar D E F Y -> Coplanar D E F Z ->
  Col X Y Z.
Proof.
  intros A B C D E F P X Y Z HNCop HNCol HP HX1 HY1 HZ1 HX2 HY2 HZ2.
  destruct (col_dec X Y Z); [assumption|].
  assert (~ Col A B C) by (apply ncop__ncol with P, HNCop).
  exfalso.
  apply HNCop.
  apply coplanar_pseudo_trans with X Y Z; [assumption|apply coplanar_pseudo_trans with A B C; Cop..|].
  apply coplanar_pseudo_trans with D E F; assumption.
Qed.

Lemma cop_per2__col : forall A X Y Z,
  Coplanar A X Y Z ->  A <> Z -> Per X Z A -> Per Y Z A -> Col X Y Z.
Proof.
intros A X Y Z HC HAZ HPer1 HPer2.
destruct HPer1 as [B' [HMid1 HCong1]]; destruct HPer2 as [B [HMid2 HCong2]]; treat_equalities.
elim (eq_dec_points X Y); intro HXY; treat_equalities; Col.
elim (eq_dec_points X Z); intro HXZ; treat_equalities; Col.
elim (eq_dec_points Y Z); intro HYZ; treat_equalities; Col.
destruct HC as [I HC].
elim HC; clear HC; intro HC; try (elim HC; clear HC);
try (intros HCol1 HCol2); try (intro H; destruct H as [HCol1 HCol2]).

  {
  elim (eq_dec_points X I); intro HXI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with Y Z; unfold Midpoint in *; spliter; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A X B I).
      {
      apply l5_6 with A X A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A X HLe); destruct H as [X' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A X' B X).
      {
      apply five_segment with I I X X'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply cong_transitivity with B X; Cong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply construction_uniqueness with I X X A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction B I I X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong A X' B X).
      {
      apply five_segment with X X' I I; Cong; Between.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; Cong.
      apply cong_transitivity with B X; Cong.
      }
    assert (H : A = B) by (apply construction_uniqueness with X I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction I B A X); destruct H as [X' [HBet HCong4]].
    assert (HCong5 : Cong X B X' A).
      {
      apply five_segment with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : X = X'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply cong_transitivity with B X; Cong.
      apply l2_11 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I X; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (eq_dec_points Y I); intro HYI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Z; unfold Midpoint in *; spliter; Cong).
  elim HCol1; clear HCol1; intro HCol1; try (elim HCol1; clear HCol1; intro HCol1).

    {
    assert (HLe : Le A Y B I).
      {
      apply l5_6 with A Y A I; Cong.
      apply l6_13_2; Col.
      split; try (intro; treat_equalities; Col).
      split; try (intro; treat_equalities; Col); Col.
      }
    assert (H := le_bet B I A Y HLe); destruct H as [Y' [HBet HCong4]]; clear HLe.
    assert (HCong5 : Cong A Y' B Y).
      {
      apply five_segment with I I Y Y'; Cong; Between.
      apply l4_3 with A B; Cong; Between.
      apply l4_3 with B A; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply cong_transitivity with B Y; Cong.
      apply l4_3 with A B; Cong; Between.
      }
    assert (H : A = B) by (apply construction_uniqueness with I Y Y A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction B I I Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong A Y' B Y).
      {
      apply five_segment with Y Y' I I; Cong; Between.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col; Cong.
      apply cong_transitivity with B Y; Cong.
      }
    assert (H : A = B) by (apply construction_uniqueness with Y I I A; Cong; Between);
    treat_equalities; intuition.
    }

    {
    assert (H := segment_construction I B A Y); destruct H as [Y' [HBet HCong4]].
    assert (HCong5 : Cong Y B Y' A).
      {
      apply five_segment with I I A B; Cong; intro; treat_equalities; Col.
      }
    assert (H : Y = Y'); treat_equalities.
      {
      apply l4_18 with A I; try (intro; treat_equalities); Col.
        apply cong_transitivity with B Y; Cong.
      apply l2_11 with A B; Cong.
      }
    assert (H : A = B) by (apply between_cong_2 with I Y; Col).
    treat_equalities; intuition.
    }
  }

  {
  elim (eq_dec_points Z I); intro HZI; treat_equalities; Col.
  assert (HCong3 : Cong I A I B) by (apply l4_17 with X Y; unfold Midpoint in *; spliter; Cong).
  assert (H := l7_20 I A B). elim H; clear H; try intro H;
  treat_equalities; assert_diffs; assert_cols; try ColR; Cong; intuition.
  }
Qed.

Lemma cop_perp2__col : forall X Y Z A B,
 Coplanar A B Y Z -> Perp X Y A B -> Perp X Z A B -> Col X Y Z.
Proof.
    intros.
    induction(col_dec A B X).
      induction(eq_dec_points X A).
        subst A.
        assert(X <> B).
          apply perp_distinct in H0.
          spliter.
          assumption.
        apply perp_right_comm in H0.
        apply perp_perp_in in H0.
        apply perp_in_comm in H0.
        apply perp_in_per in H0.
        apply perp_right_comm in H1.
        apply perp_perp_in in H1.
        apply perp_in_comm in H1.
        apply perp_in_per in H1.
        apply col_permutation_2.
        apply cop_per2__col with B.
          Cop.
          auto.
          assumption.
          assumption.
      assert(Perp A X X Y ).
        eapply perp_col.
          auto.
          apply perp_sym.
          apply H0.
        assumption.
      assert(Perp A X X Z).
        eapply perp_col.
          auto.
          apply perp_sym.
          apply H1.
        assumption.
      apply col_permutation_2.
      apply cop_per2__col with A.
        assert_diffs; apply coplanar_perm_12, col_cop__cop with B; Cop.
        auto.
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        assumption.
      apply perp_in_per.
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      assumption.
    assert(HH0:=H0).
    assert(HH1:=H1).
    unfold Perp in H0.
    unfold Perp in H1.
    ex_and H0 Y0.
    ex_and H1 Z0.
    assert(HH2:=H0).
    assert(HH3:=H3).
    apply perp_in_col in H0.
    apply perp_in_col in H3.
    spliter.
    assert(Perp X Y0 A B).
      eapply perp_col.
        intro.
        subst Y0.
        contradiction.
        apply HH0.
      assumption.
    assert(Perp X Z0 A B).
      eapply perp_col.
        intro.
        subst Z0.
        contradiction.
        apply HH1.
      assumption.
    assert(Y0 = Z0).
      eapply l8_18_uniqueness.
        apply H2.
        assumption.
        apply perp_sym.
        assumption.
        assumption.
      apply perp_sym.
      assumption.
    subst Z0.
    apply (col_transitivity_1 _ Y0).
      intro.
      subst Y0.
      contradiction.
      Col.
    Col.
Qed.

Lemma two_sides_dec : forall A B C D, TS A B C D \/ ~ TS A B C D.
Proof.
    intros.
    destruct (col_dec C A B).
      right; intros []; contradiction.
    destruct (col_dec D A B) as [|HNCol].
      right; intros [HN []]; contradiction.
    destruct (l8_18_existence A B C) as [C0 [HCol1 HPerp1]]; Col.
    destruct (l8_18_existence A B D) as [D0 [HCol2 HPerp2]]; Col.
    assert_diffs.
    destruct (midpoint_existence C0 D0) as [M].
    assert (Col M A B).
      destruct (eq_dec_points C0 D0); [treat_equalities; Col|ColR].
    destruct (l6_11_existence D0 C0 C D) as [D' []]; auto.
    destruct (bet_dec C M D') as [|HNBet].
    { left; apply l9_2, l9_5 with D' D0; Col.
      repeat split; auto.
        intro; apply HNCol; ColR.
      exists M; split; Between.
    }
    right; intro HTS.
    apply HNBet.
    assert (HTS1 : TS A B D' C).
      apply l9_5 with D D0; [apply l9_2|Col|apply l6_6]; assumption.
    destruct (eq_dec_points C0 D0).
    { treat_equalities.
      assert (Col M C D) by (apply cop_perp2__col with A B; Perp; Cop).
      destruct (distinct A B M); auto.
      - apply col_two_sides_bet with A.
          ColR.
        apply invert_two_sides, col_two_sides with B; Col; apply l9_2, HTS1.
      - apply col_two_sides_bet with B.
          ColR.
        apply invert_two_sides, col_two_sides with A; Col.
        apply l9_2, invert_two_sides, HTS1.
    }
    destruct HTS1 as [HNCol' [_ [M' []]]].
    destruct (l8_22 C0 D0 C D' M') as [_ []]; Between; Cong; Col.
      apply perp_per_1, perp_col2 with A B; auto.
      assert_diffs; apply per_col with D; Col; apply perp_per_1, perp_col2 with A B; auto.
      ColR.
    replace M with M'; Between.
    apply (l7_17 C0 D0); assumption.
Qed.

Lemma cop__not_two_sides_one_side :
 forall A B C D,
  Coplanar A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  ~ TS A B C D ->
  OS A B C D.
Proof.
    intros.
    induction (cop__one_or_two_sides A B C D); auto.
    contradiction.
Qed.

Lemma cop__not_one_side_two_sides :
 forall A B C D,
  Coplanar A B C D ->
  ~ Col C A B ->
  ~ Col D A B ->
  ~ OS A B C D ->
  TS A B C D.
Proof.
    intros.
    induction (cop__one_or_two_sides A B C D); auto.
    contradiction.
Qed.

Lemma one_side_dec : forall A B C D,
 OS A B C D \/ ~ OS A B C D.
Proof.
  intros A B C D.
  destruct (col_dec A B D).
    right; intro Habs; apply (one_side_not_col124 A B C D); assumption.
  destruct (l9_10 A B D) as [D']; Col.
  destruct (two_sides_dec A B C D') as [|HNTS].
    left; apply l9_8_1 with D'; assumption.
  right; intro.
  apply HNTS, l9_8_2 with D.
    assumption.
  apply one_side_symmetry; assumption.
Qed.

Lemma cop_dec : forall A B C D,
 Coplanar A B C D \/ ~ Coplanar A B C D.
Proof.
  intros A B C D.
  destruct (col_dec C A B).
    left; exists C; left; split; Col.
  destruct (col_dec D A B).
    left; exists D; left; split; Col.
  destruct (two_sides_dec A B C D).
    left; apply ts__coplanar; assumption.
  destruct (one_side_dec A B C D).
    left; apply os__coplanar; assumption.
  right; intro; destruct (cop__one_or_two_sides A B C D); auto.
Qed.

Lemma ex_diff_cop : forall A B C D, exists E,
  Coplanar A B C E /\ D <> E.
Proof.
  intros A B C D.
  destruct (eq_dec_points A D); [destruct (eq_dec_points B D); subst|].
  - destruct (another_point D) as [E]; exists E; split; Cop.
  - exists B; split; Cop.
  - exists A; split; Cop.
Qed.

Lemma ex_ncol_cop : forall A B C D E, D <> E ->
  exists F, Coplanar A B C F /\ ~ Col D E F.
Proof.
  intros A B C D E HDE.
  destruct (col_dec A B C) as [|HNCol].
    destruct (not_col_exists D E HDE) as [F]; exists F; split; Cop.
  destruct (col_dec D E A); [destruct (col_dec D E B)|].
  - exists C; split; Cop.
    intro; apply HNCol; ColR.
  - exists B; split; Cop.
  - exists A; split; Cop.
Qed.

Lemma ex_ncol_cop2 : forall A B C D, exists E F,
  Coplanar A B C E /\ Coplanar A B C F /\ ~ Col D E F.
Proof.
  intros A B C D.
  destruct (ex_diff_cop A B C D) as [E [HE HDE]].
  destruct (ex_ncol_cop A B C D E HDE) as [F []].
  exists E, F; repeat split; assumption.
Qed.

Lemma cop4__col : forall A1 A2 A3 B1 B2 B3 P Q R, ~ Coplanar A1 A2 A3 B1 -> ~ Col B1 B2 B3 ->
  Coplanar A1 A2 A3 P -> Coplanar B1 B2 B3 P ->
  Coplanar A1 A2 A3 Q -> Coplanar B1 B2 B3 Q ->
  Coplanar A1 A2 A3 R -> Coplanar B1 B2 B3 R ->
  Col P Q R.
Proof.
  intros A1 A2 A3 B1 B2 B3 P Q R HNCop HNCol; intros.
  assert (~ Col A1 A2 A3) by (apply ncop__ncol with B1, HNCop).
  destruct (col_dec P Q R); trivial.
  exfalso; apply HNCop.
  apply coplanar_pseudo_trans with P Q R;
  [assumption|apply coplanar_pseudo_trans with A1 A2 A3; Cop..|].
  apply coplanar_pseudo_trans with B1 B2 B3; Cop.
Qed.

Lemma col_cop2__cop : forall A B C U V P, U <> V ->
  Coplanar A B C U -> Coplanar A B C V -> Col U V P ->
  Coplanar A B C P.
Proof.
  intros A B C U V P HUV HU HV HCol.
  destruct (col_dec A B C) as [HCol1|HNCol].
    apply col__coplanar, HCol1.
  revert dependent C.
  revert A B.
  assert (Haux : forall A B C, ~ Col A B C -> ~ Col U A B ->
  Coplanar A B C U -> Coplanar A B C V -> Coplanar A B C P).
  { intros A B C HNCol HNCol' HU HV.
    apply coplanar_trans_1 with U; [Cop..|].
    apply coplanar_perm_12, col_cop__cop with V; auto.
    apply coplanar_pseudo_trans with A B C; Cop.
  }
  intros A B C HU HV HNCol.
  destruct (col_dec U A B); [destruct (col_dec U A C)|].
  - apply coplanar_perm_12, Haux; Cop; Col.
    intro; apply HNCol; destruct (eq_dec_points U A); [subst|]; ColR.
  - apply coplanar_perm_2, Haux; Cop; Col.
  - apply Haux; assumption.
Qed.

Lemma bet_cop2__cop : forall A B C U V W,
  Coplanar A B C U -> Coplanar A B C W -> Bet U V W -> Coplanar A B C V.
Proof.
  intros A B C U V W HU HW HBet.
  destruct (eq_dec_points U W).
    treat_equalities; assumption.
    apply col_cop2__cop with U W; Col.
Qed.

Lemma col2_cop2__eq : forall A B C U V P Q, ~ Coplanar A B C U -> U <> V ->
  Coplanar A B C P -> Coplanar A B C Q -> Col U V P -> Col U V Q ->
  P = Q.
Proof.
  intros A B C U V P Q HNCop; intros.
  destruct (eq_dec_points P Q); [assumption|].
  exfalso.
  apply HNCop, col_cop2__cop with P Q; ColR.
Qed.

Lemma cong3_cop2__col : forall A B C P Q,
  Coplanar A B C P -> Coplanar A B C Q ->
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  Col A B C.
Proof.
  intros A B C P Q HP HQ HPQ HA HB HC.
  destruct (col_dec A B C); [assumption|].
  destruct (midpoint_existence P Q) as [M HMid].
  assert (Per A M P) by (exists Q; Cong).
  assert (Per B M P) by (exists Q; Cong).
  assert (Per C M P) by (exists Q; Cong).
  elim (eq_dec_points A M); intro HAM.
    treat_equalities.
    assert_diffs; apply col_permutation_2, cop_per2__col with P; Cop.
  assert (Col A B M).
    apply cop_per2__col with P; try apply HUD; assert_diffs; auto.
    apply coplanar_perm_12, col_cop__cop with Q; Col.
    apply coplanar_trans_1 with C; Cop; Col.
  assert (Col A C M).
    apply cop_per2__col with P; try apply HUD; assert_diffs; auto.
    apply coplanar_perm_12, col_cop__cop with Q; Col.
    apply coplanar_trans_1 with B; Cop; Col.
  apply col_transitivity_1 with M; Col.
Qed.

Lemma l9_38 : forall A B C P Q, TSP A B C P Q -> TSP A B C Q P.
Proof.
  intros A B C P Q [HP [HQ [T [HT HBet]]]].
  repeat split; trivial.
  exists T; split; Between.
Qed.

Lemma l9_39 : forall A B C D P Q R, TSP A B C P R -> Coplanar A B C D -> Out D P Q ->
  TSP A B C Q R.
Proof.
  intros A B C D P Q R [HP [HR [T [HT HBet]]]] HCop HOut.
  assert (HNCol : ~ Col A B C) by (apply ncop__ncol with P, HP).
  split.
    intro; assert_diffs; apply HP, col_cop2__cop with D Q; Col.
  split; [assumption|].
  destruct (eq_dec_points D T).
    subst T; exists D; split; [|apply (bet_out__bet P)]; assumption.
  assert (HTS : TS D T Q R).
  { assert (~ Col P D T) by (intro; apply HP, col_cop2__cop with D T; Col).
    apply l9_8_2 with P.
    - repeat split; auto.
        intro; apply HR, col_cop2__cop with D T; Col.
        exists T; split; Col.
    - apply out_one_side; Col.
  }
  destruct HTS as [HNCol1 [HNCol2 [T' []]]].
  exists T'; split; [|assumption].
  apply col_cop2__cop with D T; Col.
Qed.

Lemma l9_41_1 : forall A B C P Q R, TSP A B C P R -> TSP A B C Q R -> OSP A B C P Q.
Proof.
  intros A B C P Q R H1 H2.
  exists R; split; assumption.
Qed.

Lemma l9_41_2 : forall A B C P Q R, TSP A B C P R -> OSP A B C P Q -> TSP A B C Q R.
Proof.
  intros A B C P Q R HPR [S [[HP [_ [X []]]] [HQ [HS [Y []]]]]].
  assert (P <> X /\ S <> X /\ Q <> Y /\ S <> Y) by (repeat split; intro; subst; auto); spliter.
  destruct (col_dec P Q S) as [|HNCol].
  { assert (X = Y) by (apply (col2_cop2__eq A B C Q S); ColR).
    subst Y.
    apply l9_39 with X P; trivial.
    apply l6_2 with S; auto.
  }
  destruct (inner_pasch P Q S X Y) as [Z []]; trivial.
  assert (X <> Z) by (intro; subst; apply HNCol; ColR).
  apply l9_39 with X Z; [|assumption|apply bet_out; auto].
  assert (Y <> Z) by (intro; subst; apply HNCol; ColR).
  apply l9_39 with Y P; [assumption..|apply l6_6, bet_out; auto].
Qed.

Lemma tsp_exists : forall A B C P, ~ Coplanar A B C P -> exists Q, TSP A B C P Q.
Proof.
  intros A B C P HP.
  destruct (segment_construction P A A P) as [Q []].
  assert (HA : Coplanar A B C A) by Cop.
  exists Q; repeat split.
  - assumption.
  - assert (A <> P) by (intro; subst; apply HP, HA); assert_diffs.
    intro; apply HP, col_cop2__cop with A Q; Col.
  - exists A; split; assumption.
Qed.

Lemma osp_reflexivity : forall A B C P, ~ Coplanar A B C P -> OSP A B C P P.
Proof.
  intros A B C P HP.
  destruct (tsp_exists A B C P HP) as [Q].
  exists Q; split; assumption.
Qed.

Lemma osp_symmetry : forall A B C P Q, OSP A B C P Q -> OSP A B C Q P.
Proof.
  intros A B C P Q [R []].
  exists R; split; assumption.
Qed.

Lemma osp_transitivity : forall A B C P Q R, OSP A B C P Q -> OSP A B C Q R -> OSP A B C P R.
Proof.
  intros A B C P Q R [S [HPS HQS]] HQR.
  exists S; split; [|apply l9_41_2 with Q]; assumption.
Qed.

Lemma cop3_tsp__tsp : forall A B C D E F P Q, ~ Col D E F ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar A B C F ->
  TSP A B C P Q -> TSP D E F P Q.
Proof.
  intros A B C D E F P Q HNCol HD HE HF [HP [HQ [T [HT HBet]]]].
  assert (~ Col A B C) by (apply ncop__ncol with P, HP).
  assert (Coplanar D E F A /\ Coplanar D E F B /\ Coplanar D E F C /\ Coplanar D E F T).
    repeat split; apply coplanar_pseudo_trans with A B C; Cop.
  spliter.
  repeat split.
    intro; apply HP; apply coplanar_pseudo_trans with D E F; Cop.
    intro; apply HQ; apply coplanar_pseudo_trans with D E F; Cop.
    exists T; split; assumption.
Qed.

Lemma cop3_osp__osp : forall A B C D E F P Q, ~ Col D E F ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar A B C F ->
  OSP A B C P Q -> OSP D E F P Q.
Proof.
  intros A B C D E F P Q HNCol HD HE HF [R []].
  exists R; split; apply (cop3_tsp__tsp A B C); assumption.
Qed.

Lemma ncop_distincts : forall A B C D, ~ Coplanar A B C D ->
  A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.
Proof.
  intros A B C D H; repeat split; intro; subst; apply H; Cop.
Qed.

Lemma tsp_distincts : forall A B C P Q, TSP A B C P Q ->
  A <> B /\ A <> C /\ B <> C /\ A <> P /\ B <> P /\ C <> P /\ A <> Q /\ B <> Q /\ C <> Q /\ P <> Q.
Proof.
  intros A B C P Q [HP [HQ HT]].
  assert (HP' := ncop_distincts A B C P HP).
  assert (HQ' := ncop_distincts A B C Q HQ).
  spliter; clean.
  repeat split; auto.
  destruct HT; spliter.
  intro; apply HP; treat_equalities; assumption.
Qed.

Lemma osp_distincts : forall A B C P Q, OSP A B C P Q ->
  A <> B /\ A <> C /\ B <> C /\ A <> P /\ B <> P /\ C <> P /\ A <> Q /\ B <> Q /\ C <> Q.
Proof.
  intros A B C P Q [R [HPR HQR]].
  apply tsp_distincts in HPR.
  apply tsp_distincts in HQR.
  spliter; clean; repeat split; auto.
Qed.

Lemma tsp__ncop1 : forall A B C P Q, TSP A B C P Q -> ~ Coplanar A B C P.
Proof.
  unfold TSP; intros; spliter; assumption.
Qed.

Lemma tsp__ncop2 : forall A B C P Q, TSP A B C P Q -> ~ Coplanar A B C Q.
Proof.
  unfold TSP; intros; spliter; assumption.
Qed.

Lemma osp__ncop1 : forall A B C P Q, OSP A B C P Q -> ~ Coplanar A B C P.
Proof.
  intros A B C P Q [R [H1 H2]].
  apply tsp__ncop1 with R, H1.
Qed.

Lemma osp__ncop2 : forall A B C P Q, OSP A B C P Q -> ~ Coplanar A B C Q.
Proof.
  intros A B C P Q [R [H1 H2]].
  apply tsp__ncop1 with R, H2.
Qed.

Lemma tsp__nosp : forall A B C P Q, TSP A B C P Q -> ~ OSP A B C P Q.
Proof.
  intros A B C P Q HTS HOS.
  absurd (TSP A B C P P).
    intro Habs; apply tsp_distincts in Habs; spliter; auto.
    apply l9_41_2 with Q; [apply l9_38 | apply osp_symmetry]; assumption.
Qed.

Lemma osp__ntsp : forall A B C P Q, OSP A B C P Q -> ~ TSP A B C P Q.
Proof.
  intros A B C P Q HOS HTS.
  apply (tsp__nosp A B C P Q); assumption.
Qed.

Lemma osp_bet__osp : forall A B C P Q R, OSP A B C P R -> Bet P Q R -> OSP A B C P Q.
Proof.
  intros A B C P Q R [S [HPS [HR [_ [Y []]]]]] HBet.
  destruct (col_dec P R S) as [|HNCol].
  { exists S.
    split; [assumption|].
    apply l9_39 with Y P; trivial.
    destruct HPS as [HP [HS [X []]]].
    assert (P <> X /\ S <> X /\ R <> Y) by (repeat split; intro; subst; auto); spliter.
    assert (X = Y) by (assert_diffs; apply (col2_cop2__eq A B C R S); ColR).
    subst Y.
    apply out_bet_out_1 with R; [|assumption].
    apply l6_2 with S; auto.
  }
  destruct HPS as [HP [HS [X []]]].
  assert (HOS : OS X Y P Q).
  { apply l9_17 with R; [|assumption].
    assert (P <> X /\ S <> X /\ R <> Y /\ S <> Y) by (repeat split; intro; subst; auto); spliter.
    assert (~ Col S X Y) by (intro; apply HNCol; ColR).
    exists S; repeat split; trivial; try (intro; apply HNCol; ColR).
      exists X; split; Col.
      exists Y; split; Col.
  }
  destruct HOS as [S' [[HNCol1 [HNCol2 [X' []]]] [HNCol3 [_ [Y' []]]]]].
  assert (Coplanar A B C X') by (assert_diffs; apply col_cop2__cop with X Y; Col).
  assert (Coplanar A B C Y') by (assert_diffs; apply col_cop2__cop with X Y; Col).
  assert (HS' : ~ Coplanar A B C S').
    intro; apply HP, col_cop2__cop with X' S'; Col; intro; subst; Col.
  exists S'; repeat split; trivial.
    exists X'; split; assumption.
    intro; apply HS', col_cop2__cop with Q Y'; Col; intro; subst; Col.
    exists Y'; split; assumption.
Qed.

Lemma l9_18_3 : forall A B C X Y P, Coplanar A B C P -> Col X Y P ->
  TSP A B C X Y <-> Bet X P Y /\ ~ Coplanar A B C X /\ ~ Coplanar A B C Y.
Proof.
  intros A B C X Y P HP HCol.
  split; [|intros [HBet [HX HY]]; repeat split; trivial; exists P; split; assumption].
  intros [HX [HY [T [HT HBet]]]].
  repeat split; trivial.
  replace P with T; trivial.
  apply (col2_cop2__eq A B C X Y); Col.
  intro; treat_equalities; auto.
Qed.

Lemma bet_cop__tsp : forall A B C X Y P,
  ~ Coplanar A B C X -> P <> Y -> Coplanar A B C P -> Bet X P Y ->
  TSP A B C X Y.
Proof.
  intros A B C X Y P HX HPY HP HBet.
  apply (l9_18_3 A B C X Y P); Col.
  repeat split; [assumption..|].
  intro; apply HX, col_cop2__cop with P Y; Col.
Qed.

Lemma cop_out__osp : forall A B C X Y P,
  ~ Coplanar A B C X -> Coplanar A B C P -> Out P X Y -> OSP A B C X Y.
Proof.
  intros A B C X Y P HX HP HOut.
  assert (~ Coplanar A B C Y).
    assert_diffs; intro; apply HX, col_cop2__cop with P Y; Col.
  destruct (segment_construction X P P X) as [X' []].
  assert (~ Coplanar A B C X').
    assert_diffs; intro; apply HX, col_cop2__cop with P X'; Col.
  exists X'; repeat split; trivial; exists P; split; trivial.
  apply bet_out__bet with X; assumption.
Qed.

Lemma l9_19_3 : forall A B C X Y P, Coplanar A B C P -> Col X Y P ->
  OSP A B C X Y <-> Out P X Y /\ ~ Coplanar A B C X.
Proof.
  intros A B C X Y P HP HCol.
  split; [|intros []; apply cop_out__osp with P; assumption].
  intro HOS.
  assert (~ Coplanar A B C X /\ ~ Coplanar A B C Y).
    unfold OSP, TSP in HOS; destruct HOS as [Z []]; spliter; split; assumption.
  spliter.
  split; [|assumption].
  apply not_bet_out; [Col|].
  intro HBet.
  apply osp__ntsp in HOS.
  apply HOS.
  repeat split; trivial; exists P; split; assumption.
Qed.

Lemma cop2_ts__tsp : forall A B C D E X Y, ~ Coplanar A B C X ->
  Coplanar A B C D -> Coplanar A B C E -> TS D E X Y ->
  TSP A B C X Y.
Proof.
  intros A B C D E X Y HX HD HE [HNCol [HNCol' [T []]]].
  assert (Coplanar A B C T) by (assert_diffs; apply col_cop2__cop with D E; Col).
  repeat split.
    assumption.
    intro; apply HX, col_cop2__cop with T Y; Col; intro; subst; apply HNCol'; Col.
  exists T; split; assumption.
Qed.

Lemma cop2_os__osp : forall A B C D E X Y, ~ Coplanar A B C X ->
  Coplanar A B C D -> Coplanar A B C E -> OS D E X Y ->
  OSP A B C X Y.
Proof.
  intros A B C D E X Y HX HD HE [Z [HXZ HYZ]].
  assert (HTS : TSP A B C X Z) by (apply cop2_ts__tsp with D E; assumption).
  exists Z; split; [assumption|].
  destruct HTS as [_ []].
  apply l9_2 in HYZ.
  apply l9_38, cop2_ts__tsp with D E; assumption.
Qed.

Lemma cop3_tsp__ts : forall A B C D E X Y, D <> E ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar D E X Y ->
  TSP A B C X Y -> TS D E X Y.
Proof.
  intros A B C D E X Y HDE HD HE HCop HTSP.
  assert (HX : ~ Coplanar A B C X) by (apply tsp__ncop1 with Y, HTSP).
  assert (HY : ~ Coplanar A B C Y) by (apply tsp__ncop2 with X, HTSP).
  apply cop__not_one_side_two_sides.
    assumption.
    intro; apply HX, col_cop2__cop with D E; Col.
    intro; apply HY, col_cop2__cop with D E; Col.
  intro.
  apply tsp__nosp in HTSP.
  apply HTSP, cop2_os__osp with D E; assumption.
Qed.

Lemma cop3_osp__os : forall A B C D E X Y, D <> E ->
  Coplanar A B C D -> Coplanar A B C E -> Coplanar D E X Y ->
  OSP A B C X Y -> OS D E X Y.
Proof.
  intros A B C D E X Y HDE HD HE HCop HOSP.
  assert (HX : ~ Coplanar A B C X) by (apply osp__ncop1 with Y, HOSP).
  assert (HY : ~ Coplanar A B C Y) by (apply osp__ncop2 with X, HOSP).
  apply cop__not_two_sides_one_side.
    assumption.
    intro; apply HX, col_cop2__cop with D E; Col.
    intro; apply HY, col_cop2__cop with D E; Col.
  intro.
  apply osp__ntsp in HOSP.
  apply HOSP, cop2_ts__tsp with D E; assumption.
Qed.

Lemma cop_tsp__ex_cop2 : forall A B C D E P,
  Coplanar A B C P -> TSP A B C D E ->
  exists Q, Coplanar A B C Q /\ Coplanar D E P Q /\ P <> Q.
Proof.
  intros A B C D E P HCop HTSP.
  destruct (col_dec D E P) as [|HNCol].
  { apply tsp_distincts in HTSP; spliter.
    destruct (eq_dec_points P A).
      subst; exists B; repeat split; Cop.
      exists A; repeat split; Cop.
  }
  destruct HTSP as [_ [_ [Q []]]].
  exists Q; repeat split; Cop.
  intro; subst; apply HNCol; Col.
Qed.

Lemma cop_osp__ex_cop2 : forall A B C D E P,
  Coplanar A B C P -> OSP A B C D E ->
  exists Q, Coplanar A B C Q /\ Coplanar D E P Q /\ P <> Q.
Proof.
  intros A B C D E P HCop HOSP.
  destruct (col_dec D E P) as [|HNCol].
  { apply osp_distincts in HOSP; spliter.
    destruct (eq_dec_points P A).
      subst; exists B; repeat split; Cop.
      exists A; repeat split; Cop.
  }
  
    destruct (segment_construction E P P E) as [E' []].
    assert (~ Col D E' P) by (intro; apply HNCol; ColR).
    destruct (cop_tsp__ex_cop2 A B C D E' P) as [Q [HQ1 [HQ2 HPQ]]]; [assumption|..].
    { apply l9_41_2 with E.
        assert_diffs; destruct HOSP as [F [_ [HE]]]; apply bet_cop__tsp with P; Cop.
        apply osp_symmetry, HOSP.
    }
    exists Q; repeat split; auto.
    apply coplanar_perm_2, coplanar_trans_1 with E'; Col; Cop.
Qed.

End T9.

Hint Resolve l9_2 invert_two_sides invert_one_side one_side_symmetry l9_9 l9_9_bis
             l9_38 osp_symmetry osp__ntsp tsp__nosp : side.
Hint Resolve os__coplanar : cop.

Ltac Side := eauto with side.

Ltac not_exist_hyp_perm4 A B C D := first [not_exist_hyp_perm_ncol A B C|not_exist_hyp_perm_ncol A B D|not_exist_hyp_perm_ncol A C D|not_exist_hyp_perm_ncol B C D].

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y);finish)

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);finish)

      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := ncop__ncols A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.
