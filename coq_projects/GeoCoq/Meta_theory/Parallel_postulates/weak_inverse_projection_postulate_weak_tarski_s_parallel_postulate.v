Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate_aux :
  forall A B C P T,
    Per A B C -> InAngle T A B C ->
    CongA P B A P B C -> Per B P T -> Coplanar A B C P ->
    InAngle P A B C.
Proof.
  intros A B C P T HPer HInangle HConga HPerP HCop.
  destruct (eq_dec_points P T).
    subst; apply HInangle.
  assert_diffs.
  destruct (angle_bisector A B C) as [P' [HInangle' HConga']]; auto.
  assert_diffs.
  assert (HAcute : Acute P' B A).
    apply acute_sym, conga_inangle_per__acute with C; trivial.
  apply l11_25 with P' A C; try (apply out_trivial); auto.
  assert (HNCol1 : ~ Col A B C) by (apply per_not_col; auto).
  assert (HCol : Col B P P').
    assert (Coplanar A B C P') by Cop.
    apply conga2_cop2__col with A C; trivial; try CopR; intro; apply HNCol1; Col.
  apply (acute_col_perp__out T); Col.
  { apply acute_lea_acute with P' B A; trivial.
    assert (HNCol2 : ~ Col P' B A).
      intro.
      assert (Col P' B C) by (apply (col_conga_col P' B A); assumption).
      apply HNCol1; ColR.
    destruct (col_dec T B P'); [|assert_diffs; destruct (cop__one_or_two_sides B P' A T); Col].
    - apply l11_31_1; auto.
      apply col_one_side_out with A; Col.
      apply invert_one_side, inangle_one_side with C; Col.
      assert (~ Col B P T) by (apply per_not_col; auto).
      intro; assert_diffs; apply HNCol2; ColR.
    - assert (Coplanar A B C P') by Cop.
      assert (Coplanar A B C T) by Cop.
      CopR.
    - apply (l11_30 P' B T P' B C); CongA.
      exists T; split; CongA.
      apply l11_24 in HInangle; apply l11_24 in HInangle'.
      destruct (col_dec B C T).
        apply out341__inangle; auto.
        apply col_in_angle_out with A; Col.
        intro; apply HNCol1; Col.
      assert (HNCol3 : ~ Col P' B C) by (apply (ncol_conga_ncol P' B A); assumption).
      apply os2__inangle.
        exists A; split; Side.
        apply invert_two_sides, in_angle_two_sides; Col.
      apply invert_one_side, inangle_one_side with A; Col.
    - exists T; split; CongA.
      destruct (col_dec B A T).
        apply out341__inangle; auto.
        apply col_in_angle_out with C; Col.
        intro; apply HNCol1; Col.
      apply os2__inangle; trivial.
      apply invert_one_side, inangle_one_side with C; Col.
  }
  apply perp_col with P; Col.
  apply perp_right_comm, per_perp; auto.
Qed.

Lemma weak_inverse_projection_postulate__weak_tarski_s_parallel_postulate :
  weak_inverse_projection_postulate -> weak_tarski_s_parallel_postulate.
Proof.
intro wipp.
cut (forall A B C P T,
       Per A B C -> InAngle T A B C ->
       P <> T -> CongA P B A P B C -> Per B P T -> Coplanar A B C P ->
       exists X Y, Out B A X /\ Col T P X /\ Out B C Y /\ Col T P Y).

  {
  intros rabp A B C T HPer HInAngle.
  assert_diffs.
  destruct (angle_bisector A B C) as [P0 [HIn HConga]]; auto.
  assert_diffs.
  assert (HNCol1 : ~ Col A B C) by (apply per_not_col; auto).
  assert (HNCol2 : ~ Col P0 B A).
  { assert (SumA P0 B A P0 B A A B C) by (apply (conga3_suma__suma A B P0 P0 B C A B C); CongA; SumA).
    intro; apply HNCol1, (col2_suma__col P0 B A P0 B A); assumption.
  }
  assert (HXY : exists X Y, Out B A X /\ Out B C Y /\ Col X T Y).
  { destruct (col_dec B P0 T).
    - assert (HT' : exists T', InAngle T' A B C /\ Perp B T T T').
      { destruct (l10_15 B P0 T A) as [T0 [HPerp HOS]]; Col.
        destruct (cop_inangle__ex_col_inangle A B C T T0) as [T' [HT1 [HT2 HT3]]]; trivial.
            intro; apply HNCol1; Col.
          assert (Coplanar P0 A B C) by Cop.
          assert (Coplanar P0 A B T0) by Cop.
          CopR.
        exists T'; split; trivial.
        assert_diffs.
        apply perp_col with P0; Col.
        apply perp_col1 with T0; Perp.
      }
      destruct HT' as [T' []].
      assert_diffs.
      destruct (rabp A B C T T') as [X [Y]]; Perp; Cop.
        apply col_conga__conga with P0; auto.
      spliter; exists X, Y; repeat (split; trivial); ColR.
    - destruct (l8_18_existence B P0 T) as [P [HP1 HP2]]; trivial.
      assert (Out B P P0).
        apply (acute_col_perp__out T); trivial.
        apply acute_sym, conga_inangle2_per__acute with A C; trivial.
      assert_diffs.
      destruct (rabp A B C P T) as [X [Y]]; auto.
        apply col_conga__conga with P0; auto.
        apply perp_per_1, perp_left_comm, perp_col with P0; auto.
        assert (Coplanar P0 A B C) by Cop.
        assert (Coplanar B P0 P A) by Cop.
        CopR.
      spliter; exists X, Y; repeat (split; trivial); ColR.
  }
  destruct HXY as [X [Y [HOutX [HOutY HCol]]]].
  assert_diffs.
  assert (X <> Y) by (intro; subst; apply HNCol1; ColR).
  exists X, Y; repeat (split; trivial).
  destruct (eq_dec_points T X) as [HTX|HTX]; try (subst; Between).
  destruct (eq_dec_points T Y) as [HTY|HTY]; try (subst; Between).
  apply out2__bet.
  - apply col_one_side_out with B; trivial.
    apply invert_one_side, col_one_side with A; Col.
    apply out_out_one_side with C; trivial.
    apply invert_one_side, in_angle_one_side; Col.
    intro; apply HTX, (l6_21 A B Y X); Col.
    intro; subst; apply HNCol1; ColR.
  - apply col_one_side_out with B; Col.
    apply invert_one_side, col_one_side with C; Col.
    apply one_side_symmetry, out_out_one_side with A; trivial.
    apply invert_one_side, in_angle_one_side; (try apply l11_24); Col.
    intro; apply HTY, (l6_21 B C X Y); Col.
    intro; subst; apply HNCol1; ColR.
  }

  {
  intros A B C P T HPer HInangle HPT HConga HPerP HCop.
  assert_diffs.
  assert (HIn : InAngle P A B C) by (apply conga_cop_inangle_per2__inangle with T; assumption).
  assert (HSumA : SumA P B A P B A A B C).
    apply (conga3_suma__suma A B P P B C A B C); CongA; SumA.
  assert (HAcute : Acute P B A) by (apply acute_sym, conga_inangle_per__acute with C; assumption).
  assert (HOut : Out B P P) by (apply out_trivial; auto).
  destruct (wipp P B A A B C P T) as [X [HX1 HX2]]; trivial.
  assert (Coplanar A B C T) by Cop.
  assert (~ Col A B C) by (apply per_not_col; auto).
  CopR.
  destruct (wipp P B C C B A P T) as [Y [HY1 HY2]]; Perp.
    apply (acute_conga__acute P B A); assumption.
    apply (conga3_suma__suma P B A P B A A B C); CongA.
    assert (Coplanar A B C T) by Cop.
    assert (~ Col A B C) by (apply per_not_col; auto).
    CopR.
  exists X, Y; repeat (split; Col).
  }
Qed.

End weak_inverse_projection_postulate_weak_tarski_s_parallel_postulate.