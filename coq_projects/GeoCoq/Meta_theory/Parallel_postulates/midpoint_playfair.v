Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section midpoint_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma midpoint_converse_postulate_implies_playfair :
  midpoint_converse_postulate ->
  playfair_s_postulate.
Proof.
intros HT A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim HPar1; clear HPar1; intro HPar1; elim HPar2; clear HPar2; intro HPar2.

  {
  assert (HDiff : P <> A1) by (intro; treat_equalities; apply HPar1; exists P; Col).
  assert (HX := symmetric_point_construction A1 P); destruct HX as [X HMid1].
  assert (HB3 : exists B3, Col B1 B2 B3 /\ BetS A2 B3 X).
    {
    assert (H : P <> B1 \/ P <> B2).
      {
      elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros.
      elim (eq_dec_points P B1); intro; elim (eq_dec_points P B2); intro; treat_equalities; intuition.
      }
    elim H; clear H; intro H.

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 B1 P) as [B3 [HCol HBet]];
      assert_diffs; unfold Midpoint in *; spliter;
      try (exists B3; split); Col; unfold BetS in *; try ColR; [..|repeat split; Between|].

        {
        apply coplanar_perm_22, col_cop__cop with P; Col.
        apply coplanar_perm_2, col_cop__cop with B2; Col.
        apply par__coplanar; Par.
        }

        {
        intro; apply HPar1; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P B1 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar1; apply HPar1; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 B3 A1) by (intro; apply HPar1; exists B3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 B2 P) as [B3 [HCol HBet]];
      assert_diffs; unfold Midpoint in *; spliter;
      try (exists B3; split); Col; unfold BetS in *; try ColR; [..|repeat split; Between|].

        {
        apply coplanar_perm_22, col_cop__cop with P; Col.
        apply coplanar_perm_2, col_cop__cop with B1; Col.
        apply par__coplanar; Par.
        }

        {
        intro; apply HPar1; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P B2 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar1; apply HPar1; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 B3 A1) by (intro; apply HPar1; exists B3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }
    }
  destruct HB3 as [B3 [HCol3 HBet1]].
  assert (HPB3 : P <> B3).
    {
    intro; treat_equalities; apply HPar1.
    exists P; unfold BetS in *; spliter; assert_diffs; assert_cols; split; ColR.
    }
  assert (HPar3 : Par A1 A2 P B3) by (apply par_col2_par with B1 B2; try ColR; try left; Par).
  assert (HC3 : exists C3, Col C1 C2 C3 /\ BetS A2 C3 X).
    {
    assert (H : P <> C1 \/ P <> C2).
      {
      elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros.
      elim (eq_dec_points P C1); intro; elim (eq_dec_points P C2); intro; treat_equalities; intuition.
      }
    elim H; clear H; intro H.

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 C1 P) as [C3 [HCol HBet]];
      assert_diffs; unfold Midpoint in *; spliter;
      try (exists C3; split); Col; unfold BetS in *; try ColR; [..|repeat split; Between|].

        {
        apply coplanar_perm_22, col_cop__cop with P; Col.
        apply coplanar_perm_2, col_cop__cop with C2; Col.
        apply par__coplanar; Par.
        }

        {
        intro; apply HPar2; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P C1 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar2; apply HPar2; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 C3 A1) by (intro; apply HPar2; exists C3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }

      {
      destruct (hilbert_s_version_of_pasch X A1 A2 C2 P) as [C3 [HCol HBet]];
      assert_diffs; unfold Midpoint in *; spliter;
      try (exists C3; split); Col; unfold BetS in *; try ColR; [..|repeat split; Between|].

        {
        apply coplanar_perm_22, col_cop__cop with P; Col.
        apply coplanar_perm_2, col_cop__cop with C1; Col.
        apply par__coplanar; Par.
        }

        {
        intro; apply HPar2; exists A2; split; Col; ColR.
        }

        {
        intro; apply H; apply l6_21 with A1 P C2 P; Col.

          {
          intro; apply par_strict_not_col_3 in HPar2; apply HPar2; ColR.
          }

          {
          assert_diffs; assert_cols; ColR.
          }
        }

        {
        induction HBet; spliter; Between.
        assert (Hc : ~ Bet A2 C3 A1) by (intro; apply HPar2; exists C3; assert_cols; split; ColR).
        exfalso; apply Hc; Between.
        }
      }
    }
  destruct HC3 as [C3 [HCol4 HBet2]].
  assert (HPC3 : P <> C3).
    {
    intro; treat_equalities; apply HPar1.
    exists P; unfold BetS in *; spliter; assert_diffs; assert_cols; split; ColR.
    }
  assert (HPar4 : Par A1 A2 P C3) by (apply par_col2_par with C1 C2; try ColR; try left; Par).
  assert (HCol5 : Col A2 X B3) by (unfold BetS in *; spliter; assert_cols; Col).
  assert (HCol6 : Col A2 X C3) by (unfold BetS in *; spliter; assert_cols; Col).
  assert (HNC' : ~ Col A1 A2 X)
    by (intro; apply HPar1; exists P; assert_diffs; assert_cols; split; ColR).
  assert (B3 = C3) by (apply l7_17 with A2 X; apply HT with A1 P; Col; Par).
  elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros.
  elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros.
  spliter; treat_equalities; split; ColR.
  }

  {
  elim (par_strict_distinct A1 A2 B1 B2 HPar1); intros; spliter; exfalso; apply HPar1.
  exists P; split; Col; ColR.
  }

  {
  elim (par_strict_distinct A1 A2 C1 C2 HPar2); intros; spliter; exfalso; apply HPar2.
  exists P; split; Col; ColR.
  }

  {
  spliter; spliter; split; Col; ColR.
  }
Qed.

End midpoint_playfair.