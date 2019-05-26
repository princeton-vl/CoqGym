Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section posidonius_postulate_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma posidonius_postulate__rah : posidonius_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
intro H.
assert (HF : exists A1 A2 B1 B2,
             Per A2 A1 B1 /\ Per A1 A2 B2 /\
             Cong A1 B1 A2 B2 /\ OS A1 A2 B1 B2 /\
             forall A3 B3,
               Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
               Cong A3 B3 A1 B1).
  {
  destruct H as [A1' [A2' [B1 [B2 [HNC [HNE [HCop HF]]]]]]].
  destruct (l8_18_existence _ _ _ HNC) as [A1 [HC1 HPerp1]].
  assert (HNC' : ~ Col A1' A2' B2).
    {
    intro HC2.
    destruct (midpoint_existence B1 B2) as [B3 HB3].
    assert (HNE' : B1 <> B2) by (intro; treat_equalities; Col).
    assert (HNE'' : B1 <> B3) by (assert_diffs; auto).
    destruct (l8_18_existence A1' A2' B3) as [A3 [HC4 HPerp3]];
    try (intro; apply HNC; assert_diffs; assert_cols; ColR).
    assert (HCong : Cong A1 B1 A3 B3)
      by (apply HF; Col; Perp; ColR).
    assert (HCong' : Cong B1 B2 B3 B2).
      {
      assert (HNE''' : A3 <> B2).
        {
        intro; assert (A1 = A3); treat_equalities.
          {
          apply l8_18_uniqueness with A1' A2' B1; Col.
          apply perp_col0 with A3 B3; Col; Perp.
          }
        assert (HFalse : B3 <> B1) by (assert_diffs; auto).
        apply HFalse; apply between_cong with A1; Cong.
        unfold Midpoint in *; spliter; Between.
        }
      assert (HNE'''' : B3 <> B2).
        {
        intro; assert (A1 = A3); treat_equalities; [|intuition].
        apply l8_18_uniqueness with A1' A2' B1; Col.
        }
      assert (HNE''''' : A1 <> B2).
        {
        intro; treat_equalities; apply HNE''';
        apply l8_18_uniqueness with A1' A2' B3; Col; Perp;
        try (intro; assert_diffs; assert_cols; apply HNC; ColR).
        apply perp_col0 with A1 B1; assert_cols; Col; Perp;
        try (intro; treat_equalities; Col).
        }
      destruct (l11_50_2 B1 A1 B2 B3 A3 B2);
      try solve[unfold Midpoint in *; spliter; Cong].

        {
        intro H.
        assert (A1 = B2); auto.
        apply perp_sym in HPerp1.
        elim (perp_not_col2 _ _ _ _ HPerp1); intro H';
        [apply l6_21 with A1 B1 A1' A2'|apply l6_21 with A1 B1 A2' A1'];
        assert_diffs; Col; assert_cols; ColR.
        }

        {
        apply out_conga with A3 B3 A3 B3;
        try apply conga_refl; try apply out_trivial; auto; do 2(split; auto);
        [|unfold Midpoint in *; spliter; Between].
        left; apply col_two_sides_bet with B3;
        [assert_diffs; assert_cols; ColR|apply l9_2; apply l9_8_2 with B1].

          {
          split; [intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
                  try (intro; treat_equalities; auto); ColR|].
          split; [intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
                  try (intro; treat_equalities; auto); ColR|].
          exists B3; split; Col; unfold Midpoint in *; spliter; auto.
          }

          {
          apply l12_6; apply par_not_col_strict with B1; Col;
          try (apply l12_9 with A1' A2'; Perp); Cop;
          try (apply col2_cop__cop with B1 B2; Col; intro; apply HNC; ColR).
          intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
          try (intro; treat_equalities; auto); ColR.
          }
        }

        {
        apply l11_16; try apply perp_per_1; try solve[assert_diffs; auto];
        apply perp_col0 with A1' A2'; Perp; ColR.
        }
      }
    assert (HFalse : B3 <> B1) by (assert_diffs; auto).
    apply HFalse; apply between_cong with B2; Cong.
    unfold Midpoint in *; spliter; Between.
    }
  destruct (l8_18_existence A1' A2' B2) as [A2 [HC2 HPerp2]]; Col.
  assert (HNE' : A1 <> A2).
    {
    intro; treat_equalities.
    assert (HCong : Cong A1 B1 A1 B2) by (apply HF; Col; Perp).
    assert (HC2 : Col A1 B1 B2).
      apply cop_perp2__col with A1' A2'; Perp.
    elim (l7_20 A1 B1 B2); Col; intro HMid.
    destruct (midpoint_existence A1 B1) as [M HM].
    elim (l7_20 A1 B1 M); try apply HF; Col; Perp; try (ColR);
    try (apply perp_col0 with A1 B1; assert_diffs; Col; Perp).
    intro; treat_equalities; intuition.
    assert_diffs.
    assert (HX : M<>A1) by auto.
    apply HX.
    apply between_equality with B1;
    unfold Midpoint in *; spliter; Between.
    }
  exists A1, A2, B1, B2.
  split; [|split; [|split; [apply HF; Col; Perp|split]]];
  try (apply l8_2; apply perp_per_2; apply perp_col0 with A1' A2'; Perp).

    {
    apply cop__not_two_sides_one_side; auto; try intro HTS;
    try (apply HNC; ColR); try (apply HNC'; ColR);
    [assert_diffs; apply coplanar_perm_16, col2_cop__cop with A1' A2'; Col; Cop|].
    destruct HTS as [HNC'' [_ [I [HC3 HBet]]]].
    destruct (midpoint_existence B1 I) as [B3 HB3].
    assert (HNE'' : B1 <> I) by (intro; treat_equalities; Col).
    destruct (l8_18_existence A1' A2' B3) as [A3 [HC4 HPerp3]];
    try (intro; apply HNC; assert_diffs; assert_cols; ColR).
    assert (HCong : Cong A1 B1 A3 B3)
      by (apply HF; Col; Perp; ColR).
    assert (HCong' : Cong B1 I B3 I).
      {
      assert (HNE''' : A3 <> I).
        {
        intro; assert (A1 = A3); treat_equalities.
          {
          apply l8_18_uniqueness with A1' A2' B1; Col.
          apply perp_col0 with A3 B3; Col; Perp.
          }
        apply HNE'; apply l8_18_uniqueness with A1' A2' B2; Col.
        apply perp_col0 with A1 B1; Col; Perp; intro; treat_equalities; Col.
        }
      assert (HNE'''' : B3 <> I).
        {
        intro; assert (A1 = A3); treat_equalities; [|intuition].
        apply l8_18_uniqueness with A1' A2' B1; Col.
        }
      assert (HNE''''' : A1 <> I).
        {
        intro; treat_equalities; apply HNE';
        apply l8_18_uniqueness with A1' A2' B2; Col; Perp.
        apply perp_col0 with A1 B1; assert_cols; Col; Perp.
        intro; treat_equalities; Col.
        }
      destruct (l11_50_2 B1 A1 I B3 A3 I);
      try solve[unfold Midpoint in *; spliter; Cong].

        {
        intro H.
        assert (A1 = I); auto.
        apply perp_sym in HPerp1.
        elim (perp_not_col2 _ _ _ _ HPerp1); intro H';
        [apply l6_21 with A1 B1 A1' A2'|apply l6_21 with A1 B1 A2' A1'];
        assert_diffs; Col; assert_cols; ColR.
        }

        {
        apply out_conga with A3 B3 A3 B3;
        try apply conga_refl; try apply out_trivial; auto; do 2(split; auto);
        [|unfold Midpoint in *; spliter; Between].
        left; apply col_two_sides_bet with B3;
        [assert_diffs; assert_cols; ColR|apply l9_2; apply l9_8_2 with B1].

          {
          split; [intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
                  try (intro; treat_equalities; auto); ColR|].
          split; [intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
                  try (intro; treat_equalities; auto); ColR|].
          exists B3; split; Col; unfold Midpoint in *; spliter; auto.
          }

          {
          apply l12_6; apply par_not_col_strict with B1; Col.

            {
            apply l12_9 with A1' A2'; Perp; Cop.
            assert_cols; apply col2_cop__cop with B1 B2; Col; Cop; ColR.
            }

            {
            intro; apply HNE'''; apply l6_21 with A1' A2' B1 B3; Col;
            try (intro; treat_equalities; auto); ColR.
            }
          }
        }

        {
        apply l11_16; try apply perp_per_1; try solve[assert_diffs; auto];
        apply perp_col0 with A1' A2'; Perp; ColR.
        }
      }
    assert (HFalse : B3 <> B1) by (assert_diffs; auto).
    apply HFalse; apply between_cong with I; Cong.
    unfold Midpoint in *; spliter; Between.
    }

    {
    intros A3 B3 HC3 HC4 HPerp3.
    apply HF; Col; Perp.
    ColR.
    apply perp_sym; apply perp_col0 with A1 A2; assert_diffs; Col; ColR.
    }
  }
destruct HF as [A [D [B [C [HPer1 [HPer2 [HCong [HOS posid]]]]]]]].
assert (HSac : Saccheri A B C D) by repeat (split; finish).
apply (per_sac__rah A B C D); auto.
destruct (midpoint_existence B C) as [M HM].
destruct (midpoint_existence A D) as [N HN].
assert(HPerp := mid2_sac__perp_lower A B C D M N HSac HM HN).
assert(Hdiff := sac_distincts A B C D HSac).
spliter.
assert_diffs.
apply (t22_7__per _ _ _ D M N); Between;
[apply perp_per_1; auto; apply (perp_col1 _ _ _ D); Col; Perp|
apply cong_left_commutativity; apply posid; Col; Perp].
Qed.

End posidonius_postulate_rah.