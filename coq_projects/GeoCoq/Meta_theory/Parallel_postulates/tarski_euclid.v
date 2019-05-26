Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section tarski_euclid.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma tarski_s_euclid_implies_euclid_5 :
  tarski_s_parallel_postulate ->
  euclid_5.
Proof.
intros HT P Q R S T U HPTQ HRTS HQUR HNC HCong1 HCong2.
destruct (symmetric_point_construction R P) as [V HMid].
assert (Hc1 : Bet V P R) by (unfold Midpoint in *; spliter; Between).
assert (Hc2 : Bet Q U R) by (unfold BetS in *; spliter; Between).
destruct (inner_pasch V Q R P U) as [W [HPWQ HUWV]]; Col; clear Hc1; clear Hc2.
assert (HPW : P <> W).
  {
  intro; treat_equalities.
  assert (P <> V).
    {
    intro; treat_equalities; apply HNC; unfold BetS in *; spliter; assert_cols; ColR.
    }
  apply HNC; apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
  spliter; assert_cols; ColR.
  }
destruct (HT P V U W Q) as [X [Y [HPVX [HPUY HXQY]]]]; Between.
assert (HPar : Par_strict Q S P R).
  {
  apply par_not_col_strict with P; Col.
  assert_diffs; unfold BetS in *; spliter;
  apply l12_17 with T; try split; Cong; Between.
  }
assert (HTS : TS Q S P Y).
  {
  apply l9_8_2 with X.

    {
    assert_diffs.
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (~ Col X Q S).
      {
      apply par_strict_not_col_2 with P.
      apply par_strict_symmetry; apply par_strict_col_par_strict with R; Col.
      unfold BetS in *; unfold Midpoint in *; spliter;
      assert_diffs; assert_cols; ColR.
      }
    repeat split; try (exists Q); Col.
    intro HCol.
    assert (Q = Y)
      by (apply l6_21 with Q S X Q; try (intro; treat_equalities); Col).
    treat_equalities.
    assert (Q = U).
      {
      apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
      spliter; apply l6_21 with Q P R Q; Col.
      apply par_strict_not_col_2 with S; Par.
      }
    treat_equalities; unfold BetS in *; spliter; Col.
    }

    {
    assert (P <> R)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> V)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    assert (P <> X)
      by (intro; treat_equalities; apply par_strict_distinct in HPar; spliter; Col).
    apply l12_6; apply par_strict_right_comm;
    apply par_strict_col_par_strict with R; Col.
    assert_cols; ColR.
    }
  }
destruct HTS as [Hc1 [Hc2 [I [HCol HBet]]]];
clear Hc1; clear Hc2; exists I.
assert (HPUI : BetS P U I).
 {
  assert (P <> Y)  by (intro; treat_equalities; Col).
  assert (HPUI : Col P U I) by (assert_cols; ColR).
  split.

    {
    elim HPUI; clear HPUI; intro HPUI; Col.
    elim HPUI; clear HPUI; intro HPUI; exfalso.

      {
      assert (HFalse : TS Q S P U).
        {
        split; Col.
        split; try (exists I; split; Col; Between).
        intro.
        assert (Q = U).
          {
          apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
          spliter; apply l6_21 with S Q R Q; Col.
          apply par_strict_not_col_1 with P; Par.
          }
        treat_equalities; unfold BetS in *; spliter; intuition.
        }
      apply l9_9 in HFalse; apply HFalse.
      apply one_side_transitivity with R.

        {
        apply l12_6; Col.
        }

        {
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
        spliter; assert_diffs; assert_cols; apply l9_19 with Q; Col.
        repeat split; Col.
        apply par_strict_not_col_1 with P; Par.
        }
      }

      {
      assert (HFalse : TS P R I U).
        {
        split; try (intro; apply HPar; exists I; Col).
        split; try (exists P; split; Col; Between).
        intro.
        assert (R = U).
          {
          unfold BetS in *; spliter; apply l6_21 with P R Q U; Col.
          apply par_strict_not_col_1 with S; Par.
          }
        treat_equalities; unfold BetS in *; spliter; intuition.
        }
      apply l9_9 in HFalse; apply HFalse.
      apply one_side_transitivity with Q.

        {
        apply l12_6; apply par_strict_right_comm;
        apply par_strict_col_par_strict with S; Par; Col.
        intro; treat_equalities;
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR; spliter;
        apply HNC; assert_cols; ColR.
        }

        {
        assert (HPar':= HPar); apply par_strict_distinct in HPar.
        apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
        spliter; assert_diffs; assert_cols; apply l9_19 with R; Col.
        repeat split; Between.
        apply par_strict_not_col_3 with S; Par.
        }
      }
    }

    {
    split; try (intro; treat_equalities; apply par_strict_not_col_3 in HPar;
                apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
                spliter; assert_cols; Col).
    try (intro; treat_equalities; Col).
    assert (Q = U).
      {
      apply l6_21 with S Q R Q; Col.
      intro; apply HNC; ColR.
      }
    treat_equalities; unfold BetS in *; spliter; intuition.
    }
 }
split; Col.
assert (HTS : TS Q R S I).
  {
  apply l9_8_2 with P.

    {
    apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
    apply BetSEq in HPUI; spliter; assert_diffs.
    assert_cols; repeat split; try (exists U; Col).
    intro; apply HNC; ColR.
    intro; apply par_strict_not_col_4 in HPar; apply HPar; ColR.
    }

    {
    apply l12_6.
    apply par_not_col_strict with P; Col;
    try (intro; apply par_strict_not_col_3 in HPar; Col).
    apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
    assert_diffs; spliter;
    apply l12_17 with T; try split; Cong; Between.
    }
  }
split.

  {
  elim HCol; intro HSQI; Between.
  assert (HFalse := HTS).
  apply l9_9 in HFalse; exfalso; apply HFalse.
  apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR;
  spliter; apply l9_19 with Q; Col.
  apply par_strict_not_col_4 in HPar; split; Col.
  unfold TS in HTS; spliter; assert_diffs; repeat split; elim HSQI; Between.
  }

  {
  assert (HFalse := HTS); unfold TS in HTS; spliter;
  assert_diffs; repeat split; Col; intro; treat_equalities;
  assert (HTS := not_two_sides_id S Q R); Col.
  }
Qed.

End tarski_euclid.