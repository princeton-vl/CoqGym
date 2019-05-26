Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

Section par_perp_perp_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma par_perp_perp_implies_playfair :
  perpendicular_transversal_postulate ->
  playfair_s_postulate.
Proof.
intro HPTP; intros A1 A2 B1 B2 C1 C2 P HPar1 HCol1 HPar2 HCol2.
elim (col_dec A1 A2 P); intro HCol.

  {
  elim HPar1; clear HPar1; intro HPar1; try (exfalso; apply HPar1; exists P; Col);
  elim HPar2; clear HPar2; intro HPar2; try (exfalso; apply HPar2; exists P; Col).
  destruct HPar1 as [HDiff1 [HDiff2 [HCol3 HCol4]]]; clear HDiff1;
  destruct HPar2 as [HDiff1 [HDiff3 [HCol5 HCol6]]].
  split; ColR.
  }

  {
  assert(HI := l8_18_existence A1 A2 P HCol); destruct HI as [I [HCol' HPerp]].
  assert (HCop1 : Coplanar B1 B2 P I) by (apply col__coplanar; Col).
  assert (HCop2 : Coplanar C1 C2 P I) by (apply col__coplanar; Col).
  assert (HPerp1 := HPTP A1 A2 B1 B2 P I HPar1 HPerp HCop1).
  assert (HPerp2 := HPTP A1 A2 C1 C2 P I HPar2 HPerp HCop2).
  assert (HCop3 : Coplanar A1 A2 P B1)
    by (assert_diffs; apply col2_cop__cop with B1 B2;
        Col; apply par__coplanar; auto).
  assert (HCop4 : Coplanar A1 A2 P B2)
    by (assert_diffs; apply col2_cop__cop with B1 B2;
        Col; apply par__coplanar; auto).
  assert (HCop5 : Coplanar A1 A2 P C1)
    by (assert_diffs; apply col2_cop__cop with C1 C2;
        Col; apply par__coplanar; auto).
  assert (HCop6 : Coplanar A1 A2 P C2)
    by (assert_diffs; apply col2_cop__cop with C1 C2;
        Col; apply par__coplanar; auto).
  assert (HCop7 : Coplanar A1 A2 P I) by Cop.
  split.

    {
    elim (eq_dec_points P C1); intro HDiff; subst; Col.
    assert (Col P C1 B1).
      {
      elim (eq_dec_points P B1); intro HPB1; subst; Col.
      apply cop_perp2__col with P I.
      CopR.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    assert (Col P C1 B2).
      {
      elim (eq_dec_points P B2); intro HPB2; subst; Col.
      apply cop_perp2__col with P I.
      CopR.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    ColR.
    }

    {
    elim (eq_dec_points P C2); intro HDiff; subst; Col.
    assert (Col P C2 B1).
      {
      elim (eq_dec_points P B1); intro HPB1; subst; Col.
      apply cop_perp2__col with P I.
      CopR.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    assert (Col P C2 B2).
      {
      elim (eq_dec_points P B2); intro HPB2; subst; Col.
      apply cop_perp2__col with P I.
      CopR.
      apply perp_sym; apply perp_col0 with C1 C2; assert_diffs; Col.
      apply perp_sym; apply perp_col0 with B1 B2; assert_diffs; Col.
      }
    ColR.
    }
  }
Qed.

End par_perp_perp_playfair.