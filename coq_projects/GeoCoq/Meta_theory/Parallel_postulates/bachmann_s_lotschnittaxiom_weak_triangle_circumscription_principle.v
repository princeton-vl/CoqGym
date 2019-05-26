Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bachmann_s_lotschnittaxiom__weak_triangle_circumscription_principle :
  bachmann_s_lotschnittaxiom -> weak_triangle_circumscription_principle.
Proof.
intro bla.
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
  clear bla; intros HP A B C A1 A2 B1 B2 HNC HPer.
  intros HPerpB1 HPerpB2 HCop1 HCop2 HCop3 HCop4.
  destruct (perp_bisect_perp _ _ _ _ HPerpB1) as [A3 [HA [_ [HCol1 [HCol2 _]]]]].
  destruct (perp_bisect_perp _ _ _ _ HPerpB2) as [B3 [HB [_ [HCol3 [HCol4 _]]]]].
  assert (Coplanar A B C A3)
    by (apply col_cop2__cop with A1 A2; Col; Cop).
  assert (Coplanar A B C B3)
    by (apply col_cop2__cop with B1 B2; Col; Cop).
  destruct (HP B C A C A1 A2 B1 B2 C A3 B3) as [I [? ?]]; try (exists I; Col);
  try solve[apply perp_right_comm; apply per_perp; assert_diffs; Perp];
  try solve[apply perp_sym; apply perp_bisect_perp; auto]; Col; try CopR.
  assert (C <> A3).
    {
    assert (HC' := HPerpB1).
    destruct HC' as [[[C' [HMid HCol]] _] _].
    intro; treat_equalities; assert_diffs.
    assert (C = C'); [|treat_equalities; auto].
    elim (perp_not_col2 _ _ _ _ (perp_bisect_perp _ _ _ _ HPerpB1)); intro HNC';
    [apply l6_21 with A1 A2 B C|apply l6_21 with A1 A2 C B]; Col.
    }
  assert (C <> B3).
    {
    assert (HC' := HPerpB2).
    destruct HC' as [[[C' [HMid HCol]] _] _].
    intro; treat_equalities; assert_diffs.
    assert (C = C'); [|treat_equalities; auto].
    elim (perp_not_col2 _ _ _ _ (perp_bisect_perp _ _ _ _ HPerpB2)); intro HNC';
    [apply l6_21 with B1 B2 A C|apply l6_21 with B1 B2 C A]; Col.
    }
  intro; apply HNC; ColR.
  }

  {
  intros A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD HPerpAB HPerpAC HPerpBD.
  intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HNCop1 HCop2 HCop3 HCop4 HNC1.
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
  assert (HPQ : IAC <> IAB) by (assert_diffs; auto).
  assert (HQR : IAB <> IBD) by (assert_diffs; auto).
  destruct (diff_col_ex3 C1 C2 IAC) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
  destruct (diff_col_ex3 D1 D2 IBD) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
  destruct (bla IAC IAB IBD P1 R1) as [I [HI1 HI2]]; auto.
    apply perp_per_2; apply perp_col2 with A1 A2; Col;
    apply perp_sym; apply perp_col2 with B1 B2; Col; Perp.
    apply perp_per_2; apply perp_col2 with A1 A2; Col;
    apply perp_sym; apply perp_col2 with C1 C2; Col; Perp.
    apply perp_per_2; apply perp_col2 with B1 B2; Col;
    apply perp_sym; apply perp_col2 with D1 D2; Col; Perp.
    assert_diffs; apply col_cop2__cop with C1 C2; Col; CopR.
    assert_diffs; apply col_cop2__cop with D1 D2; Col; CopR.
  exists I.
  split; assert_diffs; ColR.
  }
Qed.

End bachmann_s_lotschnittaxiom_weak_triangle_circumscription_principle.