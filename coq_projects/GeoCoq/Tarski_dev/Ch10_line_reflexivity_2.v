Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity.
Require Import GeoCoq.Meta_theory.Dimension_axioms.upper_dim_2.

Section T10_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cop__cong_on_bissect : forall A B M P X,
 Coplanar A B X P -> Midpoint M A B -> Perp_at M A B P M -> Cong X A X B ->
 Col M P X.
Proof.
intros.
assert(X = M \/ ~ Col A B X /\ Perp_at M X M A B).
assert_diffs; apply(cong_perp_or_mid A B M X); Cong.
induction H3.
treat_equalities; Col.
spliter.
apply perp_in_perp in H1.
apply perp_in_perp in H4.
assert_cols.
apply(cop_perp2__col _ _ _ A B); Perp; Cop.
Qed.

Lemma cong_cop_mid_perp__col : forall A B M P X,
 Coplanar A B X P -> Cong A X B X -> Midpoint M A B -> Perp A B P M -> Col M P X.
Proof.
intros.
apply (cop__cong_on_bissect A B); Cong.
apply l8_15_1; Col.
Qed.

Lemma cop__image_in_col : forall A B P P' Q Q' M,
 Coplanar A B P Q -> ReflectL_at M P P' A B -> ReflectL_at M Q Q' A B ->
 Col M P Q.
Proof.
    intros.
    assert(ReflectL P P' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    assert(ReflectL Q Q' A B).
      eapply (image_in_is_image_spec M).
      assumption.
    unfold ReflectL_at in *.
    spliter.
    induction H4.
      induction H6.
        induction (eq_dec_points A M).
          subst M.
          assert (Per B A P).
            unfold Per.
            exists P'.
            split.
              apply l7_2.
              assumption.
            apply cong_commutativity.
            eapply is_image_spec_col_cong with A B;Col.
          assert (Per B A Q).
            unfold Per.
            exists Q'.
            split.
              apply l7_2.
              assumption.
            apply cong_commutativity.
            eapply is_image_spec_col_cong with A B;Col.
          apply col_permutation_2.

          apply cop_per2__col with B.
            Cop.
            apply perp_distinct in H4.
            spliter.
            auto.
            apply l8_2.
            apply H8.
          apply l8_2.
          assumption.
        assert (Per A M P).
          unfold Per.
          exists P'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          eapply is_image_spec_col_cong.
            apply H2.
          Col.
        assert (Per A M Q).
          unfold Per.
          exists Q'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          eapply is_image_spec_col_cong.
            apply H3.
          apply col_trivial_3.
        apply col_permutation_2.
        apply cop_per2__col with A.
          assert_diffs; apply coplanar_perm_12, col_cop__cop with B; Cop.
          auto.
          apply l8_2.
          apply H9.
          auto.
        apply l8_2.
        assumption.
      subst P'.
      apply l7_3 in H0.
      subst P.
      Col.
    subst Q'.
    apply l7_3 in H1.
    subst Q.
    Col.
Qed.

Lemma l10_10_spec : forall A B P Q P' Q',
 ReflectL P' P A B -> ReflectL Q' Q A B ->
 Cong P Q P' Q'.
Proof.
    intros.
    destruct (eq_dec_points A B).
      subst B.
      assert (P' = P) by (apply (image_spec__eq A); assumption).
      assert (Q' = Q) by (apply (image_spec__eq A); assumption).
      subst; Cong.
    assert(HH0 := H).
    assert(HH1 := H0).
    unfold ReflectL in H.
    unfold ReflectL in H0.
    spliter.
    ex_and H X.
    ex_and H0 Y.
    assert (exists M, Midpoint M X Y).
      apply midpoint_existence.
    ex_elim H6 Z.
    assert (Col A B Z).
      induction (eq_dec_points X Y).
        subst Y.
        apply l7_3 in H7.
        subst X.
        assumption.
      ColR.
    double P Z R.
    double P' Z R'.
    apply cong_commutativity.
    induction H3.
      induction H2.
        assert (ReflectL R R' A B).
          apply is_image_is_image_spec .
            assumption.
          eapply (midpoint_preserves_image ) with P P' Z.
            assumption.
            assumption.
            apply l10_4.
            apply is_image_is_image_spec;auto.
            assumption.
          assumption.
        assert(R <> R').
          intro.
          subst R'.
          assert( P' = P).
            eapply l7_9.
              apply H9.
            assumption.
          subst P'.
          apply perp_distinct in H3.
          spliter.
          absurde.
        assert (Midpoint Y R R') by (eauto using symmetry_preserves_midpoint).
        assert (Cong Q' R' Q R) by (apply (l7_13 Y); assumption).
        assert (Cong P' Z P Z) by (apply (is_image_spec_col_cong A B); assumption).
        assert (Cong Q' Z Q Z) by (apply (is_image_spec_col_cong A B); assumption).
        apply cong_commutativity, (five_segment R R' Z Z); Cong; Between.
          apply cong_transitivity with P Z; [|apply cong_transitivity with P' Z]; Cong.
          intro; treat_equalities; contradiction.
      subst Q'.
      apply l7_3 in H0.
      subst Q.
      apply cong_commutativity.
      eapply is_image_spec_col_cong.
        apply l10_4_spec.
        apply HH0.
      assumption.
    subst P'.
    apply l7_3 in H.
    subst P.
    eapply is_image_spec_col_cong.
      apply l10_4_spec.
      apply HH1.
    assumption.
Qed.

Lemma l10_10 : forall A B P Q P' Q',
 Reflect P' P A B -> Reflect Q' Q A B ->
 Cong P Q P' Q'.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst.
      unfold Reflect in *.
      induction H.
        intuition.
      induction H0.
        intuition.
      spliter.
      apply l7_13 with B; apply l7_2;auto.
    apply l10_10_spec with A B;try apply is_image_is_image_spec;assumption.
Qed.

Lemma image_preserves_bet : forall A B C A' B' C' X Y,
  ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    destruct (eq_dec_points X Y).
      subst Y.
      apply image_spec__eq in H.
      apply image_spec__eq in H0.
      apply image_spec__eq in H1.
      subst; assumption.
    eapply l4_6.
      apply H2.
    unfold Cong_3.
    repeat split; apply l10_10_spec with X Y.
      apply l10_4_spec.
      apply H.
      apply l10_4_spec; assumption.
      apply l10_4_spec.
      apply H.
      apply l10_4_spec.
      assumption.
      apply l10_4_spec.
      apply H0.
    apply l10_4_spec.
    assumption.
Qed.

Lemma image_gen_preserves_bet : forall A B C A' B' C' X Y,
  Reflect A A' X Y ->
  Reflect B B' X Y ->
  Reflect C C' X Y ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    destruct (eq_dec_points X Y).
      subst Y.
      apply image__midpoint in H.
      apply image__midpoint in H0.
      apply image__midpoint in H1.
      subst.
      apply l7_15 with A B C X; Midpoint.
    eapply image_preserves_bet;try apply is_image_is_image_spec; eauto.
Qed.

Lemma image_preserves_col : forall A B C A' B' C' X Y,
  ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    destruct H2 as [HBet|[HBet|HBet]]; [|apply col_permutation_2|apply col_permutation_1];
    apply bet_col; eapply image_preserves_bet; eauto.
Qed.

Lemma image_gen_preserves_col : forall A B C A' B' C' X Y,
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Col A B C ->
  Col A' B' C'.
Proof.
    intros.
    destruct H2 as [HBet|[HBet|HBet]]; [|apply col_permutation_2|apply col_permutation_1];
    apply bet_col; eapply image_gen_preserves_bet; eauto.
Qed.

Lemma image_gen_preserves_ncol : forall A B C A' B' C' X Y,
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  ~ Col A B C ->
  ~ Col A' B' C'.
Proof.
    intros.
    intro.
    apply H2, image_gen_preserves_col with A' B' C' X Y; try (apply l10_4); assumption.
Qed.

Lemma image_gen_preserves_inter : forall A B C D I A' B' C' D' I' X Y,
  Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y -> Reflect D D' X Y ->
  ~ Col A B C -> C <> D ->
  Col A B I -> Col C D I -> Col A' B' I' -> Col C' D' I' ->
  Reflect I I' X Y.
Proof.
    intros.
    destruct (l10_6_existence X Y I) as [I0 HI0]; trivial.
    assert (I' = I0); [|subst; assumption].
    apply (l6_21 A' B' C' D'); trivial.
      apply image_gen_preserves_ncol with A B C X Y; assumption.
      intro; subst D'; apply H4, l10_2_uniqueness with X Y C'; assumption.
      apply image_gen_preserves_col with A B I X Y; assumption.
      apply image_gen_preserves_col with C D I X Y; assumption.
Qed.

Lemma intersection_with_image_gen : forall A B C A' B' X Y,
  Reflect A A' X Y -> Reflect B B' X Y ->
  ~ Col A B A' -> Col A B C -> Col A' B' C ->
  Col C X Y.
Proof.
    intros.
    apply l10_8.
    assert (Reflect A' A X Y) by (apply l10_4; assumption).
    assert (~ Col A' B' A) by (apply image_gen_preserves_ncol with A B A' X Y; trivial).
    assert_diffs.
    apply image_gen_preserves_inter with A B A' B' A' B' A B; trivial.
    apply l10_4; assumption.
Qed.

Lemma image_preserves_midpoint :
 forall A B C A' B' C' X Y,
 ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
 Midpoint A B C ->
 Midpoint A' B' C'.
Proof.
    intros.
    unfold Midpoint in *.
    spliter.
    repeat split.
      eapply image_preserves_bet.
        apply H0.
        apply H.
        apply H1.
        apply H2.
    eapply cong_transitivity.
      eapply l10_10_spec.
        apply H0.
      apply H.
    eapply cong_transitivity.
      apply H3.
    eapply l10_10_spec.
      apply l10_4_spec.
      apply H.
    apply l10_4_spec.
    apply H1.
Qed.


Lemma image_spec_preserves_per : forall A B C A' B' C' X Y,
 ReflectL A A' X Y -> ReflectL B B' X Y -> ReflectL C C' X Y ->
 Per A B C ->
 Per A' B' C'.
Proof.
    intros.
    induction (eq_dec_points X Y).
      subst Y.
      apply image_spec__eq in H.
      apply image_spec__eq in H0.
      apply image_spec__eq in H1.
      subst; assumption.
    double C B C1.
    assert (exists C1', ReflectL C1 C1' X Y).
      apply l10_6_existence_spec.
      assumption.
    ex_and H5 C1'.
    unfold Per.
    exists C1'.
    split.
      eapply image_preserves_midpoint.
        apply H0.
        apply H1.
        apply H6.
      assumption.
    eapply cong_transitivity.
      eapply l10_10_spec.
        apply H.
      apply H1.
    eapply cong_transitivity.
      unfold Per in H2.
      ex_and H2 C2.
      assert (C2=C1).
        eapply symmetric_point_uniqueness.
          apply H2.
        assumption.
      subst C2.
      apply H5.
    eapply l10_10_spec.
      apply l10_4_spec.
      apply H.
    apply l10_4_spec.
    assumption.
Qed.

Lemma image_preserves_per : forall A B C A' B' C' X Y,
 Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
 Per A B C ->
 Per A' B' C'.
Proof.
    intros.
    induction (eq_dec_points X Y).
    - induction H; induction H0; induction H1; spliter; [contradiction..|].
      treat_equalities.
      apply midpoint_preserves_per with A B C X; [|apply l7_2..]; assumption.
    - induction H; induction H0; induction H1; spliter; [|contradiction..].
      apply image_spec_preserves_per with A B C X Y; assumption.
Qed.

Lemma l10_12 : forall A B C A' B' C',
 Per A B C -> Per A' B' C' ->
 Cong A B A' B' -> Cong B C B' C' ->
 Cong A C A' C'.
Proof.
    intros.
    induction (eq_dec_points B C).
      treat_equalities;auto.
    induction (eq_dec_points A B).
      treat_equalities;auto.
    assert (exists X, Midpoint X B B').
      apply midpoint_existence.
    ex_and H5 X.
    double A' X A1.
    double C' X C1.
    assert(Cong_3 A' B' C' A1 B C1)
    by (repeat split;eauto using l7_13, l7_2).
    assert (Per A1 B C1)
      by (eauto using l8_10).
    unfold Cong_3 in H8.
    spliter.
    assert(Cong A B A1 B) by (apply cong_transitivity with A' B'; trivial).
    assert(Cong B C B C1) by (apply cong_transitivity with B' C'; trivial).
    apply cong_transitivity with A1 C1; Cong.
    clear dependent A'; clear dependent B'; clear dependent C'; clear X.

    assert(exists Y, Midpoint Y C C1)
      by (apply midpoint_existence).
    ex_and H0 Y.
    assert(Reflect C1 C B Y) by (apply cong_midpoint__image; assumption).
    assert(exists A2, Reflect A1 A2 B Y).
      apply l10_6_existence.
    ex_elim H2 A2.
    assert (Cong C A2 C1 A1).
      eapply l10_10.
        apply H0.
      assumption.
    apply cong_transitivity with A2 C; Cong.
    assert (Reflect B B B Y) by apply image_triv.
    assert (Per A2 B C).
      eapply (image_preserves_per A1 B C1 A2 B C).
        apply H5.
        assumption.
        assumption.
      assumption.
    assert (Cong A B A2 B).
      apply cong_transitivity with A1 B; trivial.
      apply cong_symmetry, l10_10 with B Y; assumption.
    clear dependent A1; clear dependent C1; clear dependent Y.

    assert (exists Z, Midpoint Z A A2).
      apply midpoint_existence.
    ex_and H0 Z.
    assert (Reflect A2 A B Z) by (apply cong_midpoint__image; Cong).
    destruct (symmetric_point_construction C B) as [C0].
    assert (Cong A C A C0) by (apply per_double_cong with B; assumption).
    assert (Cong A2 C A2 C0) by (apply per_double_cong with B; assumption).
    assert (Reflect C0 C B Z).
      apply is_image_rev, cong_midpoint__image; trivial.
      induction (eq_dec_points A A2).
        treat_equalities; assumption.
      apply (l4_17 A A2); Col.
    assert (Cong A C A2 C0).
      apply l10_10 with B Z; assumption.
    apply cong_transitivity with A2 C0; Cong.
Qed.

Lemma cong4_cop2__eq : forall A B C P Q, ~ Col A B C ->
  Cong A P B P -> Cong A P C P -> Coplanar A B C P ->
  Cong A Q B Q -> Cong A Q C Q -> Coplanar A B C Q ->
  P = Q.
Proof.
    intros A B C P Q HNCol; intros.
    destruct (eq_dec_points P Q); [assumption|].
    exfalso.
    apply HNCol.
    assert (Haux : forall R, Col P Q R -> Cong A R B R /\ Cong A R C R).
      intros R HR; split; apply cong_commutativity, (l4_17 P Q); Cong.
    destruct (midpoint_existence A B) as [D].
    assert_diffs.
    assert (HCol1 : Col P Q D).
    { assert (Coplanar A B C D) by Cop.
      apply cong3_cop2__col with A B; Cong; apply coplanar_pseudo_trans with A B C; Cop.
    }
    destruct (diff_col_ex3 P Q D HCol1) as [R1]; spliter.
    destruct (segment_construction R1 D R1 D) as [R2 []].
    assert_diffs.
    assert (Col P Q R2) by ColR.
    destruct (Haux R1); trivial.
    destruct (Haux R2); trivial.
    assert (Cong A R1 A R2).
    { assert (Per A D R1) by (apply l8_2; exists B; split; Cong).
      apply l10_12 with D D; Cong.
      apply per_col with R1; ColR.
    }
    apply cong3_cop2__col with R1 R2; auto; [apply col_cop2__cop with P Q; auto..| |].
      apply cong_transitivity with A R1; [|apply cong_transitivity with A R2]; Cong.
      apply cong_transitivity with A R1; [|apply cong_transitivity with A R2]; Cong.
Qed.

Lemma l10_16 : forall A B C A' B' P,
 ~ Col A B C -> ~ Col A' B' P -> Cong A B A' B' ->
 exists C', Cong_3 A B C A' B' C' /\ OS  A' B' P C' .
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      apply cong_symmetry in H1.
      apply False_ind.
      apply H.
      apply col_trivial_1.
    assert(exists X, Col A B X /\ Perp A B C X).
      apply l8_18_existence.
      assumption.
    ex_and H3 X.
    assert (exists X', Cong_3 A B X A' B' X').
      eapply l4_14.
        assumption.
      assumption.
    ex_elim H5 X'.
    assert (exists Q, Perp A' B' Q X' /\ OS A' B' P Q).
      apply l10_15.
        eapply l4_13.
          apply H3.
        assumption.
      assumption.
    ex_and H5 Q.
    assert (exists C', Out X' C' Q /\ Cong  X' C' X C).
      eapply l6_11_existence.
        apply perp_distinct in H5.
        spliter.
        assumption.
      intro.
      subst C.
      apply perp_distinct in H4.
      spliter.
      absurde.
    ex_and H8 C'.
    exists C'.
    unfold Cong_3 in *.
    spliter.
    assert (Cong A C A' C').
      induction(eq_dec_points A X).
        subst X.
        apply cong_symmetry in H10.
        apply cong_identity in H10.
        subst X'.
        apply cong_symmetry.
        assumption.
      eapply l10_12.
        3: apply H10.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_right_comm.
            apply H4.
          assumption.
          apply col_trivial_3.
        apply col_trivial_1.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply cong_identity in H10.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply cong_symmetry in H9.
              apply cong_identity in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H5.
            apply col_permutation_5.
            eapply out_col.
            assumption.
          eapply l4_13.
            apply H3.
          unfold Cong_3.
          repeat split;assumption.
          apply col_trivial_3.
        apply col_trivial_1.
      apply cong_symmetry.
      assumption.
    assert (Cong B C B' C').
      induction(eq_dec_points B X).
        subst X.
        apply cong_symmetry in H11.
        apply cong_identity in H11.
        subst X'.
        apply cong_symmetry.
        assumption.
      eapply l10_12.
        3: apply H11.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            assumption.
            apply perp_comm.
            apply H4.
          apply col_permutation_4.
          assumption.
          apply col_trivial_3.
        apply col_trivial_1.
        apply perp_in_per.
        eapply l8_14_2_1b_bis.
          eapply perp_col.
            intro assumption.
            subst X'.
            apply cong_identity in H11.
            contradiction.
            apply perp_sym.
            eapply perp_col.
              intro.
              subst X'.
              apply cong_symmetry in H9.
              apply cong_identity in H9.
              subst X.
              apply perp_distinct in H4.
              spliter.
              absurde.
              apply perp_sym.
              apply perp_comm.
              apply H5.
            apply col_permutation_5.
            eapply out_col.
            assumption.
          apply col_permutation_4.
          eapply l4_13.
            apply H3.
          unfold Cong_3.
          repeat split; assumption.
          apply col_trivial_3.
        apply col_trivial_1.
      apply cong_symmetry.
      assumption.
    repeat split.
      assumption.
      assumption.
      assumption.
    assert (T19 := (l9_19 A' B' C' Q X')).
    assert (OS A' B' C' Q <-> Out X' C' Q /\ ~ Col A' B' C').
      apply T19.
        eapply l4_13.
          apply H3.
        unfold Cong_3.
        repeat split; assumption.
      apply col_permutation_1.
      apply out_col.
      assumption.
    apply cong_symmetry in H1.
    destruct H14.
    spliter.
    assert (OS A' B' C' Q).
      apply H15.
      split.
        assumption.
      intro.
      apply H.
      eapply l4_13.
        apply H16.
      unfold Cong_3.
      repeat split.
        assumption.
        apply cong_symmetry.
        assumption.
      apply cong_symmetry.
      assumption.
    eapply one_side_transitivity.
      apply H7.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma cong_cop_image__col : forall A B P P' X,
 P <> P' -> Reflect P P' A B -> Cong P X P' X -> Coplanar A B P X ->
 Col A B X.
Proof.
    intros.
    unfold Reflect in *.
    induction H0.
      spliter.
      unfold ReflectL in H3.
      spliter.
      ex_and H3 M.
      induction H4.
        induction(eq_dec_points A M).
          subst M.
          assert (Perp P A A B).
            eapply perp_col.
              apply perp_distinct in H4.
              spliter.
              intro.
              subst P.
              apply l7_2 in H3.
              apply is_midpoint_id in H3.
              subst P'.
              absurde.
              apply perp_sym.
              apply perp_right_comm.
              apply H4.
            unfold Col.
            right; left.
            apply midpoint_bet.
            assumption.
          apply perp_comm in H6.
          apply perp_perp_in in H6.
          apply perp_in_comm in H6.
          apply perp_in_per in H6.
          assert (Per X A P).
            unfold Per.
            exists P'.
            split.
              apply l7_2.
              assumption.
            Cong.
          apply l8_2 in H6.
          apply col_permutation_2.
          apply (cop_per2__col P).
            Cop.
            intro.
            subst P.
            apply l7_2 in H3.
            apply is_midpoint_id in H3.
            subst P'.
            absurde.
            assumption.
          assumption.
        assert (Perp P M M A).
          eapply perp_col.
            intro.
            subst P.
            apply l7_2 in H3.
            apply is_midpoint_id in H3.
            subst P'.
            absurde.
            apply perp_sym.
            apply perp_comm.
            eapply perp_col.
              assumption.
              apply H4.
            assumption.
          unfold Col.
          right; left.
          apply midpoint_bet.
          assumption.
        apply perp_comm in H7.
        apply perp_perp_in in H7.
        apply perp_in_comm in H7.
        apply perp_in_per in H7.
        assert (Per X M P).
          unfold Per.
          exists P'.
          split.
            apply l7_2.
            assumption.
          apply cong_commutativity.
          assumption.
        apply l8_2 in H7.
        assert (Col A X M).
          assert (P <> M).
            intro.
            subst P.
            apply l7_2 in H3.
            apply is_midpoint_id in H3.
            subst P'.
            absurde.
          apply (cop_per2__col P).
            apply coplanar_perm_2, col_cop__cop with B; Cop.
            assumption.
            assumption.
          assumption.
        eapply col_transitivity_1.
          apply H6.
          apply col_permutation_5.
          assumption.
        apply col_permutation_5.
        assumption.
      subst P'.
      absurde.
    spliter;subst;Col.
Qed.

Lemma cong_cop_per2_1 :
 forall A B X Y, A <> B -> Per A B X -> Per A B Y ->
 Cong B X B Y -> Coplanar A B X Y -> X = Y \/ Midpoint B X Y.
Proof.
    intros.
    eapply l7_20.
      apply col_permutation_5.
      apply (cop_per2__col A).
        Cop.
        assumption.
        apply l8_2.
        assumption.
      apply l8_2.
      assumption.
    assumption.
Qed.

Lemma cong_cop_per2 : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y -> Coplanar A B X Y ->
 X = Y \/ ReflectL X Y A B.
Proof.
    intros.
    induction (cong_cop_per2_1 A B X Y H H0 H1 H2 H3).
      left; assumption.
    right.
    apply is_image_is_image_spec; auto.
    apply l10_4, cong_midpoint__image; trivial.
    apply per_double_cong with B; assumption.
Qed.

Lemma cong_cop_per2_gen : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y -> Coplanar A B X Y ->
 X = Y \/ Reflect X Y A B.
Proof.
    intros.
    induction (cong_cop_per2 A B X Y H H0 H1 H2 H3).
      left; assumption.
    right.
    apply is_image_is_image_spec; assumption.
Qed.

Lemma ex_perp_cop : forall A B C P,
 A <> B -> exists Q, Perp A B Q C /\ Coplanar A B P Q.
Proof.
  intros A B C P HAB.
  destruct (col_dec A B C) as [HCol|HNCol]; [destruct (col_dec A B P) as [|HNCol]|].
  - destruct (not_col_exists A B HAB) as [P' HNCol].
    destruct (l10_15 A B C P' HCol HNCol) as [Q []].
    exists Q.
    split; trivial.
    exists P; left; Col.
  - destruct (l10_15 A B C P HCol HNCol) as [Q []].
    exists Q.
    split; [|apply os__coplanar]; assumption.
  - destruct (l8_18_existence A B C HNCol) as [Q []].
    exists Q.
    split.
      Perp.
    exists Q; left; split; Col.
Qed.

Lemma hilbert_s_version_of_pasch_aux : forall A B C I P, Coplanar A B C P ->
  ~ Col A I P -> ~ Col B C P -> Bet B I C -> B <> I -> I <> C -> B <> C ->
  exists X, Col I P X /\
            ((Bet A X B /\ A <> X /\ X <> B /\ A <> B) \/
             (Bet A X C /\ A <> X /\ X <> C /\ A <> C)).
Proof.
intros A B C I P HCop HNC HNC' HBet HBI HIC HBC.
assert (HTS : TS I P B C).
  {
  assert_cols; split; try (intro; apply HNC'; ColR).
  split; try (intro; apply HNC'; ColR).
  exists I; Col.
  }
assert (HCop1 : Coplanar A P B I) by (assert_diffs; apply col_cop__cop with C; Cop; Col).
elim (two_sides_dec I P A B); intro HTS'.

  {
  destruct HTS' as [Hc1 [Hc2 [T [HCol HBet']]]].
  exists T; split; Col.
  left; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }

  {
  rename HTS' into HOS.
  assert (HTS' : TS I P A C).
    {
    apply l9_8_2 with B; Col.
    unfold TS in HTS; spliter.
    apply cop__not_two_sides_one_side; Cop.
    intro; apply HOS; apply l9_2; Col.
    }
  destruct HTS' as [Hc1 [Hc2 [T [HCol HBet']]]].
  exists T; split; Col.
  right; split; Col.
  split; try (intro; treat_equalities; Col).
  split; intro; treat_equalities; Col.
  }
Qed.

Lemma hilbert_s_version_of_pasch : forall A B C P Q, Coplanar A B C P ->
  ~ Col C Q P -> ~ Col A B P -> BetS A Q B ->
  exists X, Col P Q X /\ (BetS A X C \/ BetS B X C).
Proof.
intros A B C P Q HCop HNC1 HNC2 HAQB.
rewrite BetSEq in HAQB; spliter.
destruct (hilbert_s_version_of_pasch_aux C A B Q P) as [X [HPQX HBetS]]; Cop;
try exists X; try split; Col; do 2 rewrite BetSEq;
induction HBetS; spliter; repeat split; Between.
Qed.


Lemma two_sides_cases : forall O P A B,
 ~ Col O A B -> OS O P A B -> TS O A P B \/ TS O B P A.
Proof.
intros.
assert (HCop := os__coplanar O P A B H0).
assert(TS O A P B \/ OS O A P B).
{
  apply(cop__one_or_two_sides O A P B); Col.
    Cop.
  unfold OS in H0.
  ex_and H0 R.
  unfold TS in H0.
  spliter.
  Col.
}
induction H1.
left; auto.
right.

assert(TS O B P A \/ OS O B P A).
{
  apply(cop__one_or_two_sides O B P A); Col.
    Cop.
  unfold OS in H0.
  ex_and H0 R.
  unfold TS in H2.
  spliter.
  Col.
}
induction H2.
assumption.
assert(TS O P A B).
{
  apply(l9_31 O A P B); auto.
}
apply l9_9 in H3.
contradiction.
Qed.

Lemma not_par_two_sides :
  forall A B C D I, C <> D -> Col A B I -> Col C D I -> ~ Col A B C ->
  exists X, exists Y, Col C D X /\ Col C D Y /\ TS A B X Y.
Proof.
intros A B C D I HCD HCol1 HCol2 HNC.
assert (HX : exists X, Col C D X /\ I <> X) by (exists C; split; try intro; treat_equalities; Col).
destruct HX as [X [HCol3 HIX]].
destruct (symmetric_point_construction X I) as [Y HMid].
exists X; exists Y; assert_diffs; assert_cols; do 2 (split; try ColR).
split; try (intro; assert (I = X) by (assert_diffs; assert_cols; apply l6_21 with A B C D; Col); Col).
split; try (intro; assert (I = Y) by (assert_diffs; assert_cols; apply l6_21 with A B C D;
                                      Col; ColR); Col).
exists I; unfold Midpoint in HMid; spliter; split; Col; Between.
Qed.

Lemma cop_not_par_other_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  Coplanar A B C P ->
  exists Q, Col C D Q /\ TS A B P Q.
Proof.
intros A B C D I P HCD HCol1 HCol2 HNC1 HNC2 HCop.
destruct (not_par_two_sides A B C D I HCD HCol1 HCol2 HNC1) as [X [Y [HCol3 [HCol4 HTS]]]].
assert (Coplanar A B P X).
  apply coplanar_trans_1 with C; [Col|Cop|].
  exists I; right; right; split; ColR.
elim (two_sides_dec A B P X); intro HOS; [exists X; Col|].
assert_diffs; apply cop__not_two_sides_one_side in HOS; Col; [|intro; unfold TS in HTS; intuition].
exists Y; split; Col.
apply l9_8_2 with X; [|apply one_side_symmetry]; Col.
Qed.

Lemma cop_not_par_same_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  Coplanar A B C P ->
  exists Q, Col C D Q /\ OS A B P Q.
Proof.
intros A B C D I P HCD HCol1 HCol2 HNC1 HNC2 HCop.
destruct (not_par_two_sides A B C D I HCD HCol1 HCol2 HNC1) as [X [Y [HCol3 [HCol4 HTS]]]].
assert (Coplanar A B P X).
  apply coplanar_trans_1 with C; [Col|Cop|].
  exists I; right; right; split; ColR.
elim (one_side_dec A B P X); intro HTS2; [exists X; Col|].
assert_diffs; apply cop__not_one_side_two_sides in HTS2; Col; [|intro; unfold TS in HTS; intuition].
exists Y; split; Col.
exists X; split; Side.
Qed.

End T10_1.

Section T10_2D.

Context `{T2D:Tarski_2D}.

Lemma all_coplanar : forall A B C D, Coplanar A B C D.
Proof.
apply upper_dim_implies_all_coplanar;
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma per2__col : forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X.
Proof.
apply upper_dim_implies_per2__col;
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma perp2__col : forall X Y Z A B,
 Perp X Y A B -> Perp X Z A B -> Col X Y Z.
Proof.
    intros X Y Z A B.
    apply cop_perp2__col, all_coplanar.
Qed.

Lemma cong_on_bissect : forall A B M P X,
 Midpoint M A B -> Perp_at M A B P M -> Cong X A X B ->
 Col M P X.
Proof.
intros A B M P X.
apply cop__cong_on_bissect, all_coplanar.
Qed.

Lemma cong_mid_perp__col : forall A B M P X, Cong A X B X -> Midpoint M A B -> Perp A B P M -> Col M P X.
Proof.
intros A B M P X.
apply cong_cop_mid_perp__col, all_coplanar.
Qed.

Lemma image_in_col : forall A B P P' Q Q' M,
 ReflectL_at M P P' A B -> ReflectL_at M Q Q' A B ->
 Col M P Q.
Proof.
intros A B P P' Q Q' M.
apply cop__image_in_col, all_coplanar.
Qed.

Lemma cong_image__col : forall A B P P' X,
 P <> P' -> Reflect P P' A B -> Cong P X P' X ->
 Col A B X.
Proof.
    intros.
    assert (HCop := all_coplanar A B P X).
    apply cong_cop_image__col with P P'; assumption.
Qed.

Lemma cong_per2_1 :
 forall A B X Y, A <> B -> Per A B X -> Per A B Y ->
 Cong B X B Y -> X = Y \/ Midpoint B X Y.
Proof.
    intros.
    assert (HCop := all_coplanar A B X Y).
    apply (cong_cop_per2_1 A); assumption.
Qed.


Lemma cong_per2 : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y ->
 X = Y \/ ReflectL X Y A B.
Proof.
    intros.
    assert (HCop := all_coplanar A B X Y).
    apply cong_cop_per2; assumption.
Qed.

Lemma cong_per2_gen : forall A B X Y,
 A <> B -> Per A B X -> Per A B Y -> Cong B X B Y ->
 X = Y \/ Reflect X Y A B.
Proof.
    intros.
    assert (HCop := all_coplanar A B X Y).
    apply cong_cop_per2_gen; assumption.
Qed.

Lemma not_two_sides_one_side :
 forall A B X Y,
  ~ Col X A B ->
  ~ Col Y A B ->
  ~ TS A B X Y ->
  OS A B X Y.
Proof.
intros A B X Y.
apply cop__not_two_sides_one_side, all_coplanar.
Qed.

Lemma col_perp2__col :
 forall A B X Y P,
  Col A B P ->
  Perp A B X P ->
  Perp P A Y P ->
  Col Y X P.
Proof.
apply upper_dim_implies_col_perp2__col;
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma hilbert_s_version_of_pasch_2D : forall A B C P Q,
  ~ Col C Q P -> ~ Col A B P -> BetS A Q B ->
  exists X, Col P Q X /\ (BetS A X C \/ BetS B X C).
Proof.
intros A B C P Q.
apply hilbert_s_version_of_pasch, all_coplanar.
Qed.

Lemma not_one_side_two_sides :
 forall A B X Y,
  ~ Col X A B ->
  ~ Col Y A B ->
  ~ OS A B X Y ->
  TS A B X Y.
Proof.
apply upper_dim_implies_not_one_side_two_sides.
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma one_or_two_sides :
 forall A B X Y,
  ~ Col X A B ->
  ~ Col Y A B ->
  TS A B X Y \/ OS A B X Y.
Proof.
apply upper_dim_implies_one_or_two_sides.
unfold upper_dim_axiom; apply upper_dim.
Qed.

Lemma not_par_other_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  exists Q, Col C D Q /\ TS A B P Q.
Proof.
intros.
assert (HCop := all_coplanar A B C P).
apply cop_not_par_other_side with I; assumption.
Qed.

Lemma not_par_same_side :
  forall A B C D I P, C <> D -> Col A B I -> Col C D I -> ~ Col A B C -> ~ Col A B P ->
  exists Q, Col C D Q /\ OS A B P Q.
Proof.
intros.
assert (HCop := all_coplanar A B C P).
apply cop_not_par_same_side with I; assumption.
Qed.

End T10_2D.

Hint Resolve all_coplanar : cop.