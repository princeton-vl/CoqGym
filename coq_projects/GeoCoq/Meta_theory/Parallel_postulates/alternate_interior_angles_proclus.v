Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section alternate_interior_angles_proclus.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma alternate_interior__proclus :
  greenberg_s_axiom ->
  alternate_interior_angles_postulate ->
  proclus_postulate.
Proof.
  intros greenberg aia.
  intros A B C D P Q HPar HP HQ HCop.
  elim(col_dec C D P).
    intro HConf; exists P; split; Col.
  intro HStrict.
  assert(HParS : Par_strict A B C D).
  { apply par_strict_symmetry.
    apply (par_not_col_strict _ _ _ _ P); auto.
    apply par_symmetry; auto.
  }
  assert (HC0 := l8_18_existence C D P).
  destruct HC0 as [C0 []]; auto.
  elim(col_dec P Q C0).
    intro; exists C0; split; auto.
  intro HNCol1.
  assert_diffs.
  assert(HQ1 : exists Q1, Col Q P Q1 /\ OS A B C0 Q1).
  { apply (cop_not_par_same_side _ _ _ _ P); Col.
    apply not_col_permutation_1.
    apply (par_not_col C D); Col; Par.
    assert (Coplanar C D P A).
      {
      elim (eq_dec_points P A); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P B).
      {
      elim (eq_dec_points P B); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P C0) by Cop.
    CopR.
  }
  destruct HQ1 as [Q1 []].
  assert(~Col A B Q1) by (apply (one_side_not_col123 _ _ _ C0); Side).
  assert(P<>Q1) by (intro; subst Q1; auto).
  assert(~ Col P C0 Q1) by (intro; apply HNCol1; ColR).

  assert(HNCol2 : ~Col C0 A B) by (apply (par_not_col C D); Par; Col).
  assert(HA1 : exists A1, Col A B A1 /\ OS P C0 Q1 A1).
  { assert (Coplanar C D P A).
      {
      elim (eq_dec_points P A); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P B).
      {
      elim (eq_dec_points P B); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P C0) by Cop.
    assert (Coplanar A B C0 Q1) by Cop.
    elim(col_dec P C0 A).
    2: intro; apply (cop_not_par_same_side _ _ _ _ P); Col.
    intro.
    assert(HA1 := cop_not_par_same_side P C0 B A P Q1).
    destruct HA1 as [A1 []]; Col.
    intro; apply HNCol2; ColR.
    CopR.
    exists A1; split; Col.
    CopR.
  }
  destruct HA1 as [A1 []].
  assert(~Col P C0 A1) by (apply (one_side_not_col123 _ _ _ Q1); Side).
  assert(HNCol3 : ~Col P C D) by (apply (par_not_col A B); Col).
  assert(HC1 : exists C1, Col C D C1 /\ OS P C0 Q1 C1).
  { assert (Coplanar C D P A).
      {
      elim (eq_dec_points P A); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P B).
      {
      elim (eq_dec_points P B); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P C0) by Cop.
    assert (Coplanar A B C0 Q1) by Cop.
    elim(col_dec P C0 C).
    2: intro; apply (cop_not_par_same_side _ _ _ _ C0); Col.
    intro.
    assert(HC1 := cop_not_par_same_side P C0 D C C0 Q1).
    destruct HC1 as [C1 []]; Col.
    intro; apply HNCol3; ColR.
    CopR.
    exists C1; split; Col.
    CopR.
  }
  destruct HC1 as [C1 []].
  assert(HNCol4 : ~Col P C0 C1) by (apply (one_side_not_col123 _ _ _ Q1); Side).
  assert(HC2 := symmetric_point_construction C1 C0).
  destruct HC2 as [C2].
  assert_cols.
  assert_diffs.
  assert(~ Col C2 P C0) by (intro; apply HNCol4; ColR).
  assert(Col C D C2) by ColR.
  assert(InAngle Q1 C0 P A1) by (apply os2__inangle; Side; apply (col2_os__os A B); Col).
  assert(LtA A1 P Q1 A1 P C0).
  { split.
    exists Q1; split; CongA; apply l11_24; auto.
    intro HConga.
    apply conga_cop__or_out_ts in HConga.
    destruct HConga as [Habs|Habs].
    assert_cols; Col.
    apply l9_9 in Habs.
    apply Habs.
    apply one_side_symmetry.
    apply (col2_os__os A B); auto.
    assert (Coplanar C D P A).
      {
      elim (eq_dec_points P A); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P B).
      {
      elim (eq_dec_points P B); intro; treat_equalities; Cop.
      apply col2_cop__cop with A B; Col; apply par__coplanar; Par.
      }
    assert (Coplanar C D P C0) by Cop.
    assert (Coplanar A B C0 Q1) by Cop.
    assert (Coplanar P C0 Q1 A1) by Cop.
    CopR.
  }
  assert(Acute A1 P Q1).
  { exists A1.
    exists P.
    exists C0.
    split; auto.
    apply (l11_17 P C0 C2).
    - apply perp_per_1; auto.
      apply perp_sym.
      apply (perp_col2 C D); Perp.

    - apply conga_sym.
      apply conga_right_comm.
      apply aia.
      2: apply (par_col4__par A B C D); Col.
      apply (l9_8_2 _ _ C1).
      repeat split; Col; exists C0; split; Col; Between.
      apply (one_side_transitivity _ _ _ Q1); Side.
   }
   assert (HS := greenberg P C0 C1 A1 P Q1).
   destruct HS as [S []]; auto.
     intro; apply HQ; ColR.
     apply perp_per_1; auto; apply perp_sym; apply (perp_col2 C D); Perp.
   assert(Col C D S) by ColR.
   assert_diffs.
   assert(OS P C0 S C1) by (apply invert_one_side; apply out_one_side; Col).
   assert(HY : InAngle Q1 C0 P S).
   { assert(OS P C0 S C1) by (apply invert_one_side; apply out_one_side; Col).
     assert(~ Col P C0 S) by (apply (one_side_not_col123 _ _ _ C1); auto).
     apply os2__inangle.
     apply (one_side_transitivity _ _ _ C1); Side.
     exists A1.
     assert(OS P C0 S A1).
     { apply (one_side_transitivity _ _ _ C1); auto.
       apply (one_side_transitivity _ _ _ Q1); Side.
     }
     assert(TS P S C0 A1) by (apply l9_31; auto; apply l12_6; apply (par_strict_col4__par_strict A B C D); auto).
     split; auto.
     assert(CongA A1 P S C0 S P) by (apply aia; Side; apply (par_col4__par A B C D); auto).
     assert(Hlta : LtA A1 P S A1 P Q1) by (apply (conga_preserves_lta P S C0 A1 P Q1); CongA).
     destruct Hlta as [Hlea HNConga].
     assert_diffs.
     apply invert_two_sides.
     apply in_angle_two_sides; auto.
     2: apply not_col_permutation_1; apply (par_not_col C D); Col; apply (par_strict_col2_par_strict _ _ A B); Par.
     - intro.
       elim (out_dec P S Q1); intro Habs.
       apply HNConga; apply (out_conga A1 P S A1 P S); try (apply out_trivial); CongA.
       apply not_out_bet in Habs; Col.
       assert(~ OS P C0 S A1); auto.
       apply l9_9.
       apply l9_2.
       apply (l9_8_2 _ _ Q1); auto.
       repeat split; Col.
       exists P.
       split; Col; Between.

     - apply l11_24.
       apply lea_in_angle; Lea; CongA.
       apply (one_side_transitivity _ _ _ C0).
       apply one_side_symmetry; apply (col2_os__os A B); auto.
       apply l12_6; apply (par_strict_col4__par_strict A B C D); auto.
   }
   destruct HY as [_ [_ [_ [Y [HY1 HY2]]]]].
   exists Y.
   split.
   2: ColR.
   destruct HY2.
   subst Y; Col.
   ColR.
Qed.

End alternate_interior_angles_proclus.