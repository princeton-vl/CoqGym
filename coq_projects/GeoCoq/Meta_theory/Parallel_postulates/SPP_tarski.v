Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.tarski_s_euclid_remove_degenerated_cases.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section SPP_tarski.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma impossible_case_5 : forall P Q R S T U I,
  BetS P T Q ->
  BetS R T S ->
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Bet S Q I ->
  Bet U I P ->
  False.
Proof.
intros P Q R S T U I HPTQ HRTS HQUR HNC HNC' HPar1 HPar2 HSQI HPUI.
apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR.
assert (HTS : TS Q S P U) by (assert_diffs; spliter; assert_cols; repeat split;
                                     Col; try (exists I; Col; Between); intro; apply HNC'; ColR).
apply l9_9 in HTS; apply HTS.
apply one_side_transitivity with R.

  {
  apply l12_6; apply par_not_col_strict with P; Col; Par.
  }

  {
  assert (HQS : Q <> S) by (assert_diffs; assumption).
  assert (HQSQ : Col Q S Q) by Col.
  assert (HRUQ : Col R U Q) by (spliter; assert_cols; Col).
  rewrite (l9_19 Q S R U Q HQSQ HRUQ).
  split; spliter; try (intro; apply HNC; assert_cols; ColR); repeat split; Between.
  }
Qed.

Lemma impossible_case_6 : forall P Q R S T U I,
  BetS P T Q ->
  BetS R T S ->
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Bet S Q I ->
  Bet I P U ->
  False.
Proof.
intros P Q R S T U I HPTQ HRTS HQUR HNC HNC' HPar1 HPar2 HSQI HPUI.
apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR.
apply between_symmetry in HPUI.
destruct (inner_pasch S U I Q P HSQI HPUI) as [J [HBet1 HBet2]].
assert (HParS : Par_strict P S Q U).
  {
  apply par_not_col_strict with R.

    {
    spliter; assert_cols.
    apply par_col_par with R; Par.
    ColR.
    }

    {
    spliter; assert_cols; ColR.
    }

    {
    intro; apply HNC.
    spliter; assert_cols; ColR.
    }
  }
apply HParS; exists J; assert_cols; Col.
Qed.

Lemma impossible_case_7 : forall P Q R S T U I,
  BetS P T Q ->
  BetS R T S ->
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Col P U I ->
  Bet Q I S ->
  False.
Proof.
intros P Q R S T U I HPTQ HRTS HQUR HNC HNC' HPar1 HPar2 HPUI HSQI.
apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR.
elim (eq_dec_points I S); intro HIS; treat_equalities.

  {
  assert (HParS : Par_strict Q R P I) by (apply par_not_col_strict with P; Col; Par; unfold BetS in *;
                                          spliter; assert_cols; intro; apply HNC'; ColR).
  apply HParS; exists U; spliter; assert_cols; Col.
  }

  {
  assert (HTS : TS P U Q S) by (assert_diffs; spliter; assert_cols; repeat split;
                                       Col; try (exists I; Col; Between); intro; apply HNC; ColR).
  apply l9_9 in HTS; apply HTS.
  exists R; split.

    {
    spliter; assert_diffs; assert_cols.
    split; try (intro; apply HNC; ColR).
    split; try (intro; apply HNC; ColR).
    exists U; Col; Between.
    }

    {
    destruct HPTQ as [HPTQ HDiff1].
    destruct HQUR as [HQUR HDiff2].
    apply between_symmetry in HQUR.
    destruct (inner_pasch R P Q U T HQUR HPTQ) as [J [HPJU HRJT]].
    assert (HRJS : Bet R J S) by (spliter; eBetween).
    spliter; assert_diffs; assert_cols.
    split; try (intro; apply HNC; ColR).
    split; try (intro; apply HNC; ColR).
    exists J; split; Col; Between.
    }
  }
Qed.

Lemma impossible_case_8 : forall P Q R S T U I,
  BetS P T Q ->
  BetS R T S ->
  BetS Q U R ->
  ~ Col P Q S ->
  ~ Col P R U ->
  Par P R Q S ->
  Par P S Q R ->
  Col P U I ->
  Bet I S Q ->
  False.
Proof.
intros P Q R S T U I HPTQ HRTS HQUR HNC HNC' HPar1 HPar2 HPUI HSQI.
apply BetSEq in HPTQ; apply BetSEq in HRTS; apply BetSEq in HQUR.
elim HPUI; clear HPUI; intro HPUI.

  {
  assert (H : Par_strict P S Q R) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                      spliter; assert_cols; intro; apply HNC'; ColR); apply H.
  apply between_symmetry in HSQI.
  destruct (inner_pasch P Q I U S HPUI HSQI) as [J [HQJU HPJS]]; exists J.
  spliter; assert_diffs; assert_cols; split; Col; ColR.
  }

  {
  elim HPUI; clear HPUI; intro HPUI.

    {
    assert (H : Par_strict P S Q R) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                        spliter; assert_cols; intro; apply HNC'; ColR); apply H.
    apply between_symmetry in HSQI.
    destruct (outer_pasch U Q I P S HPUI HSQI) as [J [HQJU HPSJ]]; exists J.
    spliter; assert_diffs; assert_cols; split; Col; ColR.
    }

    {
    assert (H : Par_strict P R Q S) by (apply par_not_col_strict with Q; Col; Par; unfold BetS in *;
                                        spliter; assert_cols; intro; apply HNC'; ColR); apply H.
    destruct HQUR as [HQUR HDiff].
    destruct (outer_pasch Q I U R P HQUR HPUI) as [J [HQJI HRPJ]]; exists J.
    spliter; assert_diffs; assert_cols; split; Col.
    elim (eq_dec_points Q I); intro HQI; treat_equalities; Col; ColR.
    }
  }
Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid_aux :
  strong_parallel_postulate ->
  (forall A B C D T,
   A <> B ->
   A <> C ->
   A <> D ->
   A <> T ->
   B <> C ->
   B <> D ->
   B <> T ->
   C <> D ->
   C <> T ->
   D <> T ->
   ~ Col A B C ->
   Bet A D T ->
   Bet B D C ->
   exists B', exists B'', exists MB, exists X, Bet A B X /\ Par_strict B C T X /\
   BetS B MB T /\ BetS B' MB B'' /\
   Cong B MB T MB /\ Cong B' MB B'' MB /\
   Col B B' D /\ Bet B'' T X /\
   B <> B' /\ B'' <> T).
Proof.
intros HSPP A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC.
destruct (symmetric_point_construction D B) as [B' HB'].
destruct (midpoint_distinct_2 B D B' HBD HB') as [HB'D HBB'].
destruct HB' as [HBDB' HCong1].
apply between_symmetry in HADT.
apply between_symmetry in HBDB'.
destruct (outer_pasch T B' D A B HADT HBDB') as [B''' [HTB'''B' HABB''']].
destruct (midpoint_existence B T) as [MB HMB].
destruct (midpoint_distinct_1 MB B T HBT HMB) as [HBMB HMBT].
destruct HMB as [HBMBT HCong2].
destruct (symmetric_point_construction B' MB) as [B'' HB''].
assert (HB'MB : MB <> B').
  {
  assert (H : ~ Col B' D MB) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
destruct (midpoint_distinct_2 MB B' B'' HB'MB HB'') as [HB'B'' HB''MB].
destruct HB'' as [HB'MBB'' HCong3].
assert (H1 : BetS B MB T) by (repeat split; Between).
assert (H2 : BetS B' MB B'') by (repeat split; Between).
assert (HB'T : B' <> T).
  {
  assert (H : ~ Col B B' T) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (HB'B''' : B' <> B''').
  {
  assert (H : ~ Col A B B') by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (HB'''T : B''' <> T).
  {
  assert (H : ~ Col A B T) by (intro; apply HABC; assert_cols; ColR).
  intro; treat_equalities; apply H; Col.
  }
assert (H3 : BetS T B''' B') by (repeat split; Between).
assert (H4 : ~ Col B T B'') by (intro; apply HABC; assert_cols; ColR).
assert (H5 : Cong B MB T MB) by Cong.
assert (H6 : Cong B' MB B'' MB) by Cong.
destruct (HSPP B T B' B'' MB B''') as [X [HBetS HX]];
Col; Cop; try (intro; apply H4; assert_diffs; assert_cols; ColR).
assert (HNC : ~ Col B B' B''') by (intro; assert_diffs; assert_cols; apply H4; ColR).
assert (HPar1 : Par B B' T B'') by (unfold BetS in *; spliter; apply l12_17 with MB; try split; Col).
assert (HPar2 : Par B B'' T B')
  by (unfold BetS in *; spliter; assert_diffs; apply l12_17 with MB; try split; Between; Cong).
elim HBetS; clear HBetS; intro HBetS.

  {
  elim HX; clear HX; intro HX.

    {
    assert (H : BetS B'' T X).
      {
      repeat split; try (intro; treat_equalities); Col.
      apply H4; assert_diffs; assert_cols; ColR.
      }
    clear HBetS; rename H into HBetS.
    assert (H : BetS B B''' X).
      {
      repeat split; try (intro; treat_equalities); Col; unfold BetS in *; spliter;
      apply H4; assert_diffs; assert_cols; ColR.
      }
    clear HX; rename H into HX.
    apply BetSEq in HBetS; destruct HBetS as [HB''TX [HB''T [HB''X HBTX]]].
    exists B'; exists B''; exists MB; exists X.
    split; unfold BetS in HX; spliter; eBetween.
    assert (HPar : Par B' B B'' T) by (apply l12_17 with MB; try split; Between; Cong).
    assert (HPar' : Par B C B'' T)
      by (apply par_symmetry; apply par_col_par with B'; Par; assert_cols; ColR).
    split.

      {
      apply par_not_col_strict with T; Col.

        {
        apply par_col_par with B''; Par.
        assert_cols; ColR.
        }

        {
        intro; apply HABC; assert_cols; ColR.
        }
      }

      {
      repeat (split; try assumption); unfold BetS in *; spliter; assert_cols; Col.
      }
    }

    {
    elim HX; clear HX; intro HX.

      {
      exfalso; apply impossible_case_5 with B T B' B'' MB B''' X; spliter; assumption.
      }

      {
      exfalso; apply impossible_case_6 with B T B' B'' MB B''' X; spliter; assumption.
      }
    }
  }

  {
  elim HBetS; clear HBetS; intro HBetS.

    {
    exfalso; apply impossible_case_7 with B T B' B'' MB B''' X; spliter; assumption.
    }

    {
    exfalso; apply impossible_case_8 with B T B' B'' MB B''' X; spliter; assumption.
    }
  }

Qed.

Lemma strong_parallel_postulate_implies_tarski_s_euclid :
  strong_parallel_postulate ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HSPP; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC.
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A B C D T)
as [B' [B'' [MB [X [HABX [HPar' [HBet1 [HBet2 [HCong1 [HCong2 [HBB'D [HB''TX [HBB' HB''T]]]]]]]]]]]]];
destruct (strong_parallel_postulate_implies_tarski_s_euclid_aux HSPP A C B D T)
as [C' [C'' [MC [Y [HACY [HPar [HBet3 [HBet4 [HCong3 [HCong4 [HCC'D [HC''TY [HCC' HC''T]]]]]]]]]]]]];
Between; Col.
clear HBet3; clear HBet4; clear HCong3; clear HCong4;
clear MC; clear HC''TY; clear HC''T; clear HPar'.
exists X; exists Y; repeat split; try assumption.
elim (col_dec X T Y); intro HXTY.

  {
  apply between_symmetry in HACY.
  assert (HU := outer_pasch Y B C A D HACY HBDC); destruct HU as [U [HYUB HADU]].
  apply between_symmetry in HABX.
  assert (HV := outer_pasch X Y B A U HABX HYUB); destruct HV as [V [HXVY HAUV]].
  assert (HAX : A <> X) by (intro; treat_equalities; Col).
  assert (HAY : A <> Y) by (intro; treat_equalities; Col).
  assert (HAXY : ~ Col A X Y) by (intro; assert_cols; apply HABC; ColR).
  assert (HAU : A <> U) by (intro; treat_equalities; Col).
  assert (HEq : T = V) by (assert_cols; apply l6_21 with X Y A D; Col; ColR); subst; assumption.
  }

  {
  assert (HNC : ~ Col T B'' Y) by (intro; apply HXTY; unfold BetS in *; spliter; assert_cols; ColR).
  assert (HCop : Coplanar T B B'' Y).
    {
    apply coplanar_pseudo_trans with A B C; assert_cols; Cop.

      {
      exists D; assert_cols; Col5.
      }

      {
      assert (HABD : ~ Col D A B) by (intro; assert_cols; apply HABC; ColR).
      apply coplanar_trans_1 with D; [Cop..|].
      apply ts__coplanar.
      apply l9_8_2 with X.

        {
        assert (HAX : A <> X) by (intro; treat_equalities; apply HABC; Col).
        split; try (intro; assert_cols; apply HABC; ColR).
        split; try (intro; assert_cols; apply HABC; ColR).
        exists T; split; Col; Between.
        }

        {
        apply invert_one_side.
        assert (HADA : Col A D A) by Col.
        assert (HXBA : Col X B A) by (assert_cols; Col).
        rewrite (l9_19 A D X B A HADA HXBA).
        assert (HAX : A <> X) by (intro; treat_equalities; apply HABC; Col).
        split; try (intro; assert_cols; apply HABC; ColR); split; auto.
        }
      }
    }
  destruct (HSPP T B B'' B' MB Y) as [I [HCol1 HCol2]]; Cong;
  try (unfold BetS in *; spliter; repeat (split; try Between)).
  exfalso; apply HPar; exists I; split; Col.
  elim (eq_dec_points I B); intro HBI; subst; Col.
  unfold BetS in *; spliter; assert_cols; ColR.
  }
Qed.

End SPP_tarski.