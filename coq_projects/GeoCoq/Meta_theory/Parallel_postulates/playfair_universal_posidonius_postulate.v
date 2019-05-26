Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_universal_posidonius_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair__universal_posidonius_postulate : playfair_s_postulate -> universal_posidonius_postulate.
Proof.
intros HP A1 A2 A3 A4 B1 B2 B3 B4 HPar HC1 HC2 HPerp1 HC3 HC4 HPerp2.
elim HPar; intro HParS; [|destruct HParS as [HD1 [HD2 [HC5 HC6]]];
                           assert_diffs; assert_cols;
                           elim (perp_not_col2 _ _ _ _ HPerp1);
                           intro HF; exfalso; apply HF; ColR].
destruct (l8_18_existence A1 A2 B1) as [A1' [HC5 HPerp3]];
try apply par_strict_not_col_1 with B2; Par.
assert (HCong : forall A3 B3,
                  Col A1 A2 A3 -> Col B1 B2 B3 -> Perp A1 A2 A3 B3 ->
                  Cong A3 B3 A1' B1);
[|assert (HCong1 := HCong A3 B3 HC1 HC2 HPerp1);
  assert (HCong2 := HCong A4 B4 HC3 HC4 HPerp2);
  apply cong_transitivity with A1' B1; Cong].
clear HC1; clear HC2; clear HC3; clear HC4; clear HPerp1; clear HPerp2;
clear A3; clear A4; clear B3; clear B4; intros A3 B3 HC1 HC2 HPerp1;
rename HC5 into HC3; rename HPerp3 into HPerp2.
destruct (segment_construction_2 B3 A3 A1' B1) as [B3' [HC4 HCong]];
[assert_diffs; auto|]; elim (eq_dec_points A1' A3); intro HD; treat_equalities.
  {
  assert (HC1 : Col A1' B1 B3).
    apply cop_perp2__col with A1 A2; Perp.
    assert_diffs; apply col_cop__cop with B2; Col.
    apply par__coplanar, HPar.
  assert (B1 = B3); treat_equalities; Cong.
  apply l6_21 with B1 B2 A1' B1; assert_diffs; Col.
  elim (eq_dec_points A1' A1); intro HD1; treat_equalities;
  [elim (eq_dec_points A1' A2); intro HD2; [intuition|];
   apply par_strict_not_col_1 with A2;
   apply par_strict_col2_par_strict with A1' A2; Col; Par|
   apply par_strict_not_col_1 with A1;
   apply par_strict_col2_par_strict with A1 A2; Col; Par].
  }

  {
  assert (HParS' : Par_strict A1' A3 B1 B3').
    {
    apply sac__par_strict1423; split;
    [apply perp_per_1; assert_diffs; try apply perp_col0 with A1 A2; Perp|
     split; [apply perp_per_1; assert_diffs;
             try (apply perp_col0 with A3 B3; try apply perp_col0 with A1 A2);
             Perp; induction HC4; assert_cols; Col|split; Cong]].
    apply one_side_transitivity with B3.

      {
      elim (eq_dec_points B1 B3); intro HD'; treat_equalities;
      [try apply one_side_reflexivity; apply par_strict_not_col_1 in HParS;
       intro; apply HParS; assert_diffs; ColR|].
      apply l12_6; apply par_strict_col2_par_strict with B1 B2; Col.
      apply par_strict_symmetry;
      apply par_strict_col2_par_strict with A1 A2; Col; Par.
      }

      {
      rewrite (l9_19 _ _ _ _ A3); Col; [|induction HC4; assert_cols; Col].
      elim (perp_not_col2 _ _ _ _ HPerp1); intro HNC; [intuition|].
      split; [|intro; apply HNC; assert_diffs; ColR].
      split; [assert_diffs; auto|].
      split; [intro; treat_equalities; assert_diffs; intuition|auto].
      }
    }
  destruct (HP A1 A2 B1 B2 B1 B3' B1) as [_ HC5]; Col;
  [apply par_symmetry; apply par_col2_par with A1' A3;
   assert_diffs; try ColR; try apply par_strict_par; Par|].
  assert (B3 = B3'); treat_equalities; Cong.
  apply l6_21 with B1 B3' A3 B3; try apply par_strict_not_col_1 with A1'; Par;
  assert_diffs; Col; [ColR|induction HC4; assert_cols; Col].
  }
Qed.

End playfair_universal_posidonius_postulate.