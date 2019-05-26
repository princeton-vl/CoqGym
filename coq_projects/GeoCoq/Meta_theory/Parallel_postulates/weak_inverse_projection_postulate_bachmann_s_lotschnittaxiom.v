Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__bachmann_s_lotschnittaxiom :
  weak_inverse_projection_postulate -> bachmann_s_lotschnittaxiom.
Proof.
intro hrap.
cut (forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        Col A1 A2 IAB -> Col B1 B2 IAB ->
        Col A1 A2 IAC -> Col C1 C2 IAC ->
        Col B1 B2 IBD -> Col D1 D2 IBD ->
        Coplanar IAB IAC IBD C1 -> Coplanar IAB IAC IBD C2 ->
        Coplanar IAB IAC IBD D1 -> Coplanar IAB IAC IBD D2 ->
       ~ Col IAB IAC IBD ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).

  {
  clear hrap; intro lotschnitt.
  intros P Q R P1 R1 HPQ HQR HPerQ HPerP HPerR HCop1 HCop2.
  destruct (eq_dec_points P P1).
    subst; exists R; Col.
  destruct (eq_dec_points R R1).
    subst; exists P; Col.
  assert (HNCol : ~ Col P Q R) by (apply per_not_col; auto).
  destruct (lotschnitt P Q Q R P P1 R R1 Q P R) as [S [HS1 HS2]]; Col; Perp; Cop.
  exists S; auto.
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD HPerpAB HPerpAC HPerpBD.
  intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4 HNC1.
  assert (Col IAB IAC A1) by (assert_diffs; ColR).
  assert (Col IAB IAC A2) by (assert_diffs; ColR).
  assert (Col IAB IBD B1) by (assert_diffs; ColR).
  assert (Col IAB IBD B2) by (assert_diffs; ColR).
  assert (Coplanar IAB IAC IBD A1) by Cop.
  assert (Coplanar IAB IAC IBD A2) by Cop.
  assert (Coplanar IAB IAC IBD B1) by Cop.
  assert (Coplanar IAB IAC IBD B2) by Cop.
  assert (HNC2 : ~ Col A1 A2 D1).
    {
    apply par_strict_not_col_1 with D2; apply par_not_col_strict with IBD;
    Col; try (intro; apply HNC1; assert_diffs; ColR).
    apply l12_9 with B1 B2; Perp; CopR.
    }
  assert (HNC3 : ~ Col B1 B2 C1).
    {
    apply par_strict_not_col_1 with C2; apply par_not_col_strict with IAC;
    Col; try (intro; apply HNC1; assert_diffs; ColR).
    apply l12_9 with A1 A2; Perp; CopR.
    }
  assert (HParA : Par_strict A1 A2 D1 D2).
    apply par_not_col_strict with D1; Col; apply l12_9 with B1 B2; Perp; CopR.
  assert (HParB : Par_strict B1 B2 C1 C2).
    apply par_not_col_strict with C1; Col; apply l12_9 with A1 A2; Perp; CopR.
  assert (HNCol3 : ~ Col IAC B1 B2) by (apply par_not_col with C1 C2; Par; ColR).
  assert (HNCol4 : ~ Col IBD A1 A2) by (apply par_not_col with D1 D2; Par; ColR).
  assert (HNCol5 : ~ Col IAB C1 C2) by (apply par_not_col with B1 B2; Par; ColR).
  assert (HNCol6 : ~ Col IAB D1 D2) by (apply par_not_col with A1 A2; Par; ColR).
  assert (HPQ : IAC <> IAB) by (assert_diffs; auto).
  assert (HQR : IAB <> IBD) by (assert_diffs; auto).
  rename IAB into Q; rename IAC into P; rename IBD into R.
  assert (Per P Q R).
    {
    apply perp_per_2; apply perp_col2 with A1 A2; Col;
    apply perp_sym; apply perp_col2 with B1 B2; Col; Perp.
    }
  assert (HNCol7 : ~ Col P Q R) by (apply per_not_col; trivial).
  destruct (angle_bisector P Q R) as [M [HM1 HM2]]; auto.
  assert (HSuma : SumA P Q M P Q M P Q R).
    assert_diffs; apply conga3_suma__suma with P Q M M Q R P Q R; CongA; SumA.
  assert (HAcute : Acute P Q M).
  { apply nbet_sams_suma__acute with P Q R; auto.
      intro HBet; apply HNCol7; Col.
    destruct (sams_dec P Q M P Q M); trivial.
    assert_diffs.
    exfalso; apply (lea__nlta P Q M P Q R).
      exists M; split; CongA.
    apply obtuse_per__lta; trivial.
    apply nsams__obtuse; auto.
  }

  assert (HC3 : exists C3, Col C1 C2 C3 /\ OS P Q R C3).
  { destruct (diff_col_ex3 C1 C2 P) as [C0]; Col; spliter.
    destruct (cop_not_par_same_side P Q C0 P P R) as [C3 []]; Col.
      intro; apply HNCol5; ColR.
      assert (Coplanar P Q R C0); [|Cop].
      assert_diffs; apply col_cop2__cop with C1 C2; Col; Cop.
    exists C3; split; trivial; ColR.
  }
  destruct HC3 as [C3 [HCol7 HOS1]].
  destruct (hrap P Q M P Q R P C3) as [S [HS1 HS2]]; trivial.
    apply out_trivial; auto.
    assert_diffs; auto.
    assert (HP := HPerpAC); destruct HP as [P' [_ [_ [HP1 [HP2 HP3]]]]].
    assert (P = P'); [|treat_equalities; apply HP3; Col].
    elim (perp_not_col2 _ _ _ _ HPerpAC); intro; assert_diffs;
    [apply l6_21 with A1 A2 C1 C2|apply l6_21 with A1 A2 C2 C1]; Col.
    assert (Coplanar P Q R M) by Cop.
    assert (Coplanar P Q R C3); [|CopR].
    assert_diffs; apply col_cop2__cop with C1 C2; Col; Cop.

  assert (HD3 : exists D3, Col D1 D2 D3 /\ OS R Q P D3).
  { destruct (diff_col_ex3 D1 D2 R) as [D0]; Col; spliter.
    destruct (cop_not_par_same_side R Q D0 R R P) as [D3 []]; Col.
      intro; apply HNCol6; ColR.
      assert (Coplanar P Q R D0); [|CopR].
      assert_diffs; apply col_cop2__cop with D1 D2; Col; Cop.
    exists D3; split; trivial; ColR.
  }
  destruct HD3 as [D3 [HCol8 HOS2]].
  destruct (hrap R Q M R Q P R D3) as [T [HT1 HT2]]; Perp.
    apply (acute_conga__acute P Q M); CongA.
    assert_diffs; apply conga3_suma__suma with P Q M P Q M P Q R; CongA.
    apply out_trivial; auto.
    assert_diffs; auto.
    assert (HP := HPerpBD); destruct HP as [R' [_ [_ [HR1 [HR2 HR3]]]]].
    assert (R = R'); [|treat_equalities; apply HR3; Col].
    elim (perp_not_col2 _ _ _ _ HPerpBD); intro; assert_diffs;
    [apply l6_21 with B1 B2 D1 D2|apply l6_21 with B1 B2 D2 D1]; Col.
    assert (Coplanar P Q R M) by Cop.
    assert (Coplanar P Q R D3); [|CopR].
    assert_diffs; apply col_cop2__cop with D1 D2; Col; Cop.

  assert (HOut : Out Q S T) by (apply l6_7 with M; trivial; apply l6_6; assumption).
  assert (HCol9 : Col C1 C2 S) by (assert_diffs; ColR).
  assert (HCol10 : Col D1 D2 T) by (assert_diffs; ColR).
  destruct (col_dec C1 C2 T).
    exists T; Col.
  destruct (col_dec D1 D2 S).
    exists S; Col.
  destruct HOut as [HSQ [HTQ [HBet|HBet]]].
  - assert (HTS : TS C1 C2 R T).
      apply l9_8_2 with Q.
      repeat split; Col; exists S; Col.
      apply l12_6, par_strict_col2_par_strict with B1 B2; Par; Col.
    assert_diffs.
    destruct HTS as [_ [_ [I [HI1 HI2]]]].
    exists I; split; ColR.
  - assert (HTS : TS D1 D2 P S).
      apply l9_8_2 with Q.
      repeat split; Col; exists T; Col.
      apply l12_6, par_strict_col2_par_strict with A1 A2; Par; Col.
    assert_diffs.
    destruct HTS as [_ [_ [I [HI1 HI2]]]].
    exists I; split; ColR.
  }
Qed.

End weak_inverse_projection_postulate_bachmann_s_lotschnittaxiom.