Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma bachmann_s_lotschnittaxiom__weak_inverse_projection_postulate :
  bachmann_s_lotschnittaxiom -> weak_inverse_projection_postulate.
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
  clear bla; intro lotschnitt.
  intros A B C D E F P Q HAcute HPer HSuma HOut HPQ HPerP HCop.
  suma.assert_diffs.
  assert (HNCol : ~ Col A B C).
  { intro HCol.
    apply (per_not_col D E F); auto.
    apply (col2_suma__col A B C A B C); assumption.
  }
  assert (HNCol1 : ~ Col B C P) by (intro; apply HNCol; ColR).
  destruct (l10_6_existence_spec B C P) as [P' HP']; trivial.
  assert (HP'1 : Reflect P P' B C) by (apply is_image_is_image_spec; auto).
  assert (HNCol2 : ~ Col B C P') by (apply osym_not_col with P; trivial).
  destruct (l10_6_existence_spec B C Q) as [Q' HQ']; trivial.
  assert (HQ'1 : Reflect Q Q' B C) by (apply is_image_is_image_spec; auto).
  assert_diffs.
  assert (P' <> Q').
   intro; subst Q'; assert (P = Q) by (apply (l10_2_uniqueness B C P'); assumption); auto.
  apply l6_6 in HOut.
  assert (HCongA : CongA C B P' A B C).
    apply out_conga with C P' P C; try (apply out_trivial); auto.
    apply conga_sym, conga_left_comm, reflectl__conga; auto.
    apply is_image_spec_rev, HP'.
  assert (HTS : TS B C P P').
    repeat split; Col; destruct HP' as [[X [HX1 HX2]] _]; exists X; split; Col; Between.
  assert (HPer1 : Per A B P').
  { apply l11_17 with D E F; trivial.
    apply (suma2__conga A B C A B C); trivial.
    apply conga3_suma__suma with A B C C B P' A B P'; CongA.
    exists P'; assert_diffs; repeat (split; CongA).
      apply l9_9, l9_5 with P B; Col.
      assert (Coplanar P' C A B) by (apply col2_cop__cop with P B; Col; Cop).
      Cop.
  }
  assert (HNCol3 : ~ Col A B P') by (apply per_not_col; auto).
  assert (HNCol4 : ~ Col B P' P) by (intro; apply HNCol3; ColR).
  assert (HPerp1 : Perp A B B P') by (apply per_perp; auto).
  assert (HPerp2 : Perp A B P Q) by (apply perp_left_comm, perp_col with P; Col; apply per_perp; auto).
  assert (HPerp3 : Perp B P' P' Q').
    apply per_perp; auto; apply image_spec_preserves_per with B P Q B C; trivial; apply col__refl; Col.
  assert (HNCol5 : ~ Col P' P Q).
    apply (par_not_col B P'); Col.
    apply par_not_col_strict with P; Col.
    apply l12_9 with A B; Perp; Cop.
    assert (Coplanar P' C A B) by (apply col2_cop__cop with P B; Col; Cop).
    CopR.
  assert (HI := HPerp2); destruct HI as [I [_ [_ [HCol1 [HCol2 _]]]]].
  assert (Coplanar P' C A B) by (apply col2_cop__cop with P B; Col; Cop).
  assert (Coplanar P C A B) by Cop.
  assert (Coplanar Q Q' B C) by Cop.
  destruct (lotschnitt A B B P' P Q P' Q' B P P') as [Y [HY1 HY2]]; Col; try CopR.

    {
    elim (col_dec B C Q); intro; [|CopR].
    assert (Q = Q'); [|treat_equalities; CopR].
    apply col_image_spec__eq with B C; Col.
    }

    {
    exists Y; split; trivial.
    apply col_one_side_out with A.
      apply col_permutation_1, intersection_with_image_gen with P Q P' Q'; Col.
    apply invert_one_side, one_side_transitivity with P'.
      apply cop__not_two_sides_one_side; Col.
      assert (Coplanar P' C A B) by (apply col2_cop__cop with P B; Col; Cop).
      Cop.
      apply (conga_sams_nos__nts A B C A B C P'); SumA.
      apply l9_9, l9_5 with P B; Col.
    apply l12_6, par_strict_col_par_strict with Q'; Col.
      intro; subst; apply HNCol5; Col.
    apply par_not_col_strict with P'; Col.
    apply l12_9 with B P'; Perp; Cop.
    elim (col_dec B C Q); intro; [|CopR].
    assert (Q = Q'); [|treat_equalities; CopR].
    apply col_image_spec__eq with B C; Col.
    }
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

End bachmann_s_lotschnittaxiom_weak_inverse_projection_postulate.