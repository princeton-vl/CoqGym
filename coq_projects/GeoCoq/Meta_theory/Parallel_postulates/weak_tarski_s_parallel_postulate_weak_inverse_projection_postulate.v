Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Formalization of a proof from Bachmann's article "Zur Parallelenfrage" *)

Lemma  weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux :
  weak_tarski_s_parallel_postulate ->
  forall A B C P T,
    Per A B C -> InAngle T A B C ->
    P <> T -> CongA P B A P B C -> Per B P T -> Coplanar A B C P ->
    (exists X, Out B A X /\ Col T P X) \/ (exists Y, Out B C Y /\ Col T P Y).
Proof.
  intros tora A B C P T HPer HInAngle HPT HCongA HPerP HCop.

  assert (HIn : InAngle P A B C)
    by (apply conga_cop_inangle_per2__inangle with T; assumption).
  assert (HAcute : Acute P B A)
    by (apply acute_sym, conga_inangle_per__acute with C; assumption).
  assert (HAcute' : Acute P B C) by (apply (acute_conga__acute P B A); assumption).
  assert_diffs.
  assert (HPerp : Perp B P P T) by (apply per_perp; auto).
  assert (HNCol : ~ Col A B C) by (apply per_not_col; auto).
  assert (HNCol1 : ~ Col B P T) by (apply per_not_col; auto).
  destruct (col_dec A B T).
    left; exists T; split; Col.
    apply l6_6, acute_col_perp__out_1 with P; Col.
  destruct (tora A B C T) as [U [V [HU [HV HUTV]]]]; trivial.
  destruct (col_dec P T U) as [HCol|HNCol2].
    left; exists U; split; Col.
  destruct (col_dec P T V) as [HCol|HNCol3].
    right; exists V; split; Col.
  destruct (cop__one_or_two_sides P T B U) as [HTS|HOS]; Col.

    {
    assert (Coplanar A B C P) by Cop.
    assert (Coplanar A B C T) by Cop.
    assert (Coplanar A B U C) by (apply col__coplanar; assert_cols; Col).
    CopR.
    }
    destruct HTS as [_ [_ [X [HX1 HX2]]]].
    left; exists X; split; Col.
    apply l6_7 with U; auto.
    assert_diffs; apply l6_6, bet_out; auto.
    intro; subst; apply HNCol1, HX1.
  assert (HTS : TS P T B V).
    apply l9_8_2 with U; Side.
    repeat split; Col.
    exists T; repeat split; Col.
  destruct HTS as [_ [_ [Y [HY1 HY2]]]].
  right; exists Y; split; Col.
  apply l6_7 with V; auto.
  assert_diffs; apply l6_6, bet_out; auto.
  intro; subst; apply HNCol1, HY1.
Qed.

Lemma weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate :
  weak_tarski_s_parallel_postulate -> weak_inverse_projection_postulate.
Proof.
intro wtpp.
cut (forall A B C P T,
       Per A B C -> InAngle T A B C ->
       P <> T -> CongA P B A P B C -> Coplanar A B C P -> Per B P T ->
       exists X Y, Out B A X /\ Col T P X /\ Out B C Y /\ Col T P Y).

  {
  intros rabp A B C D E F P Q HAcute HPerE HSuma HOut HPQ HPerP HCop.
  assert (HNCol1 : ~ Col A B C).
    intro; suma.assert_diffs; apply (per_not_col D E F); auto.
    apply (col2_suma__col A B C A B C); assumption.
  assert (HNCol2 : ~ Col B P Q) by (assert_diffs; apply per_not_col; auto).
  assert (HCongA : CongA A B C P B C).
    assert_diffs; apply out_conga with A C A C; try (apply out_trivial); CongA.
  assert (HNCol3 : ~ Col P B C) by (apply (ncol_conga_ncol A B C); assumption).
  assert (HPerp : Perp B P P Q) by (apply per_perp; assert_diffs; auto).
  apply suma_left_comm in HSuma.
  destruct HSuma as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
  assert (HQ' : exists Q', P <> Q' /\ Col P Q Q' /\ InAngle Q' C B P).
  { destruct (cop_not_par_same_side B P Q P P C) as [Q0 [HCol HOS]]; Col.

      {
      assert (Coplanar A B P C) by Cop.
      CopR.
      }

    destruct (one_side_dec B C P Q0).
      exists Q0; assert_diffs; split; auto; split; Col.
      apply os2__inangle; assumption.
    assert (HQ' : exists Q', Col P Q Q' /\ Col B C Q').
    { destruct (col_dec B C Q0).
        exists Q0; Col.
      assert_diffs.
      destruct (cop__not_one_side_two_sides B C P Q0) as [_ [_ [Q' [HCol' HBet]]]]; Col; Cop.
      exists Q'; split; ColR.
    }
    destruct HQ' as [Q' [HCol1 HCol2]].
    exists Q'.
    assert (P <> Q') by (intro; subst; apply HNCol3; Col).
    split; auto; split; Col.
    apply out321__inangle; auto.
      assert_diffs; auto.
    apply l6_6, (acute_col_perp__out_1 P); Col.
      apply (acute_conga__acute A B C); assumption.
    apply perp_col1 with Q; auto.
  }
  destruct HQ' as [Q' [HPQ' [HCol HInangle]]].
  assert (HInangle' : InAngle Q' C B J).
  { apply in_angle_trans with P; trivial.
    apply l11_25 with A C J; try (apply out_trivial; assert_diffs; auto); [|apply l6_6; assumption].
    apply os_ts__inangle.
      assert (~ Col A B J) by (apply (ncol_conga_ncol A B C); CongA).
      assert_diffs; apply cop__not_one_side_two_sides; Col; Cop.
    assert (~ Col C B J).
      apply (ncol_conga_ncol D E F); CongA; assert_diffs; apply per_not_col; auto.
    apply invert_one_side, one_side_symmetry, cop__not_two_sides_one_side; Col.
      assert_diffs; auto.
    apply conga_sams_nos__nts with A B C; SumA.
  }
  destruct (rabp C B J P Q') as [Y [_ [HY1 [HY2 _]]]]; trivial.
    apply (l11_17 D E F); CongA.
    assert_diffs; apply out_conga with A C A J; try (apply out_trivial); CongA.
    assert (Coplanar A B P C) by Cop.
    CopR.
    apply per_col with Q; auto.
  exists Y; split; ColR.
  }

  {
  intros A B C P T HPer HInAngle HPT HCongA HCop HPerP.
  assert (HNOut : ~ Out B A C) by (intro; assert_diffs; apply (per_not_col A B C); Col).
  assert (HPerp : Perp B P P T) by (assert_diffs; apply per_perp; auto).
  destruct (weak_tarski_s_parallel_postulate__weak_inverse_projection_postulate_aux wtpp A B C P T) as [[X [HX1 HX2]]|[Y [HY1 HY2]]]; trivial.
  - destruct (symmetric_point_construction X P) as [Y HY].
    assert (X <> Y).
    { intro; treat_equalities.
      apply HNOut, l6_7 with P; trivial.
      apply (l11_21_a P B A); trivial.
      apply l6_6, HX1.
    }
    assert (Out B C Y).
    { apply conga_cop_out_reflectl__out with A P X; trivial.
      apply l10_4_spec; split.
        exists P; Col.
      left; apply perp_col2_bis with P T; ColR.
    }
    exists X, Y; repeat (split; try ColR).
  - destruct (symmetric_point_construction Y P) as [X HX].
    assert (X <> Y).
    { intro; treat_equalities.
      apply HNOut, l6_7 with P; apply l6_6; trivial.
      apply (l11_21_a P B C); CongA.
      apply l6_6, HY1.
    }
    assert (Out B A X).
    { apply conga_cop_out_reflectl__out with C P Y; CongA; Cop.
        intro HOut; apply HNOut, l6_6, HOut.
      apply l10_4_spec; split.
        exists P; Col.
      left; apply perp_col2_bis with P T; try ColR.
    }
    exists X, Y; repeat (split; try ColR).
  }
Qed.

End weak_tarski_s_parallel_postulate_weak_inverse_projection_postulate.