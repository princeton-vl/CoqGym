Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section original_spp_inverse_projection_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma original_spp__inverse_projection_postulate :
  alternative_strong_parallel_postulate -> inverse_projection_postulate.
Proof.
  intros ospp A B C P Q Hacute Hout HPQ HPer HCop.
  assert_diffs.
  assert_cols.
  elim(col_dec A B C).
  { intro.
    exists P.
    split; Col.
    apply (l6_7 _ _ A); auto.
    apply not_bet_out; Col.
    intro.
    destruct Hacute as [x [y [z [HPer2 Hlta]]]].
    assert_diffs.
    assert(HN := not_lta_and_gta A B C x y z).
    apply HN.
    split; auto.
    split.
    apply l11_31_2; Between.
    intro; destruct Hlta; CongA.
  }
  intro HNCol1.
  assert(HNCol2 : ~ Col B P Q) by (apply per_not_col; auto).
  assert(HQ0 := cop_not_par_same_side A B Q P P C).
  destruct HQ0 as [Q0 []]; Col; Cop.
    intro; apply HNCol2; ColR.
  assert(HNCol3 : ~ Col A B Q0) by (apply (one_side_not_col123 _ _ _ C); Side).
  assert(P<>Q0) by (intro; subst; Col).
  assert (HSuma := ex_suma C B P B P Q0).
  destruct HSuma as [D [E [F]]]; auto.

  assert(HY := ospp C B P Q0 D E F).
  destruct HY as [Y []]; auto.
    apply (col_one_side _ A); Side.
  { intro.
    assert(Hlta : LtA A B C C B P).
    { apply acute_per__lta; auto.
      apply (bet_per_suma__per123 _ _ _ B P Q0 D E F); auto.
      apply l8_2.
      apply (l8_3 Q); Perp; Col.
    }
    destruct Hlta as [Hlea HNConga].
    apply HNConga.
    apply conga_right_comm.
    apply (out_conga A B C A B C); try (apply out_trivial); CongA.
  }

  exists Y.
  split.
  2: ColR.
  assert(HB0 := l10_15 A B B C).
  destruct HB0 as [B0 []]; Col.
  assert(HNCol4 : ~ Col A B B0) by (apply (one_side_not_col123 _ _ _ C); Side).
  assert(HNCol5 : ~ Col B C P) by (intro; apply HNCol1; ColR).
  assert_diffs.
  assert(P<>Y) by (intro; subst; auto).
  apply (col_one_side_out _ B0); auto.
  apply (one_side_transitivity _ _ _ P).
  apply (one_side_transitivity _ _ _ A).
  - apply invert_one_side.
    apply in_angle_one_side; Col.
    { intro.
      assert(HInter := l8_16_1 B0 B A C B).
      destruct HInter; Col; Perp.
      assert(Habs : LtA A B C A B C) by (apply acute_per__lta; auto).
      destruct Habs; CongA.
    }
    apply l11_24.
    apply lea_in_angle; CongA; Side.
    apply lta__lea.
    apply acute_per__lta; auto.
    apply perp_per_1; Perp.

  - apply out_one_side; Col.

  - apply l12_6.
    assert(HPar : Par B B0 P Y).
    { apply (l12_9 _ _ _ _ A B); Perp; Cop.
      apply coplanar_trans_1 with C; Col; Cop.
      apply perp_right_comm.
      apply (perp_col1 _ _ _ P); Col.
      apply perp_sym.
      apply (perp_col1 _ _ _ Q); Col; Perp; ColR.
    }
    destruct HPar; auto.
    exfalso.
    spliter.
    apply HNCol2; ColR.
Qed.

End original_spp_inverse_projection_postulate.