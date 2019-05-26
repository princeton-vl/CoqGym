Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_aristotle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma proclus__aristotle : proclus_postulate -> aristotle_s_axiom.
Proof.
  intros proclus P Q A B C HNCol Hacute.
  assert(HD0 := l10_15 B A B C).
  destruct HD0 as [D0 []]; Col.
  assert(HD := segment_construction B D0 P Q).
  destruct HD as [D []].
  assert(HNCol1 : ~ Col B A D0) by (apply perp_not_col; auto).
  assert_diffs.
  assert(D<>B) by (intro;Between).
  assert(~ Col D B A) by (intro; apply HNCol1; ColR).
  assert(HY0 := l10_15 D B D A).
  destruct HY0 as [Y0 [HPerp HOS]]; Col.
  assert(Perp B A B D) by (apply (perp_col1 _ _ _ D0); Perp; Col).
  assert(HPar : Par B A Y0 D).
    {
    apply (l12_9 _ _ _ _ D B); Perp; Cop.
    }
  assert(HY := proclus B A Y0 D B C).
  destruct HY as [Y []]; Col.
  assert (Coplanar B A C D0) by Cop.
  assert (Coplanar A C B D)
    by (assert_diffs; assert_cols; apply col2_cop__cop with B D0; Col; Cop).
  assert (Coplanar D B A Y0) by Cop.
  CopR.
  apply (par_not_col_strict _ _ _ _ D) in HPar; Col.
  assert(~ Col Y B A) by (apply (par_not_col Y0 D); Col; Par).
  assert(HX := l8_18_existence A B Y).
  destruct HX as [X []]; Col.
  exists X.
  exists Y.

  assert(OS B A C D).
  { apply (one_side_transitivity _ _ _ D0); auto.
    apply out_one_side; Col.
    apply bet_out; Between.
  }
  assert(Hlta : LtA A B C A B D).
  { destruct Hacute as [A' [B' [C' [HPer Hlta]]]].
    apply (conga_preserves_lta A B C A' B' C'); try (apply conga_refl); auto.
    destruct Hlta.
    assert_diffs.
    apply l11_16; auto.
    apply perp_per_2; auto.
  }
  assert(HNCol2 : ~ Col B C D).
  { intro.
    elim(bet_dec C B D).
    { intro.
      assert(~ OS B A C D); auto.
      apply l9_9.
      repeat split; Col.
      exists B.
      repeat split; Col.
    }
    intro.
    destruct Hlta as [_ HNConga].
    apply HNConga.
    apply (out_conga A B C A B C); try (apply out_trivial); CongA.
    apply not_bet_out; Col.
  }
  assert_diffs.
  assert(Y<>D) by (intro; subst Y; Col).
  assert(OS B A C D).
    apply (one_side_transitivity _ _ _ D0); auto; apply out_one_side; Col; apply bet_out; auto.
  assert(Par_strict B D X Y).
  { apply (par_not_col_strict _ _ _ _ Y); Col.
    apply (l12_9 _ _ _ _ B A); Perp; Cop.
  assert (Coplanar B A C D0) by Cop.
  assert (Coplanar A C B D)
    by (assert_diffs; assert_cols; apply col2_cop__cop with B D0; Col; Cop).
  apply coplanar_perm_12, col2_cop__cop with B C; Col; Cop.
    intro; assert(Col B C D); Col; ColR.
  }
  assert(InAngle C A B D) by (apply lea_in_angle; Lea; CongA; Side).
  assert(Out B C Y).
  { apply (col_one_side_out _ A); Col.
    apply (one_side_transitivity _ _ _ D); auto.
    apply l12_6.
    apply (par_strict_col_par_strict _ _ _ Y0); Par; Col.
  }

  assert(Out B A X).
  { apply (col_one_side_out _ D); Col.
    apply one_side_symmetry.
    apply (one_side_transitivity _ _ _ Y).
    apply l12_6; auto.
    apply (one_side_transitivity _ _ _ C).
    apply out_one_side; try (apply l6_6); Col.
    apply invert_one_side.
    apply in_angle_one_side; try (apply l11_24); Col.
  }

  assert(Per B X Y).
  { assert (~ Col B D X) by (apply (par_strict_not_col_1 _ _ _ Y); auto).
    assert_diffs.
    apply perp_per_1; auto.
    apply perp_left_comm.
    apply (perp_col _ A); Col; Perp.
  }

  assert(Cong B D X Y).
  { assert_diffs.
    assert(HAAS := l11_50_2 B Y D Y B X).
    destruct HAAS; Cong.
      apply not_col_permutation_5; apply (par_strict_not_col_4 _ _ X); auto.
      apply l11_16; Perp; apply perp_per_2; auto; apply (perp_col _ Y0); Col; Perp.
    apply conga_comm.

(* proclus -> alternate_interior *)
apply proclus_s_postulate_implies_strong_parallel_postulate in proclus.
apply strong_parallel_postulate_implies_tarski_s_euclid in proclus.
apply tarski_s_euclid_implies_playfair in proclus.
apply playfair__alternate_interior in proclus.
rename proclus into aia.

    apply aia.
    - apply l9_2.
      apply (l9_8_2 _ _ A).
      apply (col_preserves_two_sides C B); Col; apply in_angle_two_sides; Col.
      apply invert_one_side; apply out_one_side; Col.

    - apply par_left_comm.
      apply (par_col_par _ _ _ A); Col.
      apply (par_col_par_2 _ Y0); Col.
      apply par_strict_par; Par.
   }

  repeat (split; auto).
  - apply (l5_6 P Q B D); Cong.
    apply le_right_comm.
    exists D0.
    split; Between; Cong.

  - intro.
    assert(D0=B); auto.
    apply (between_cong D B D0); Between.
    apply (cong_transitivity _ _ P Q).
    Cong.
    apply (cong_transitivity _ _ X Y); Cong.
Qed.

End proclus_aristotle.