Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_similar.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__similar : postulate_of_right_saccheri_quadrilaterals -> postulate_of_existence_of_similar_triangles.
Proof.
  intro rah.
  destruct lower_dim_ex as [A [B0 [C]]].
  assert(~ Col A B0 C) by (unfold Col; assumption).
  destruct (l10_15 C A C B0) as [B []]; Col.
  assert(HNCol1 : ~ Col C A B) by (apply (one_side_not_col123 _ _ _ B0); Side).
  assert(Per A C B) by Perp.
  destruct (symmetric_point_construction A B) as [B'].
  assert_diffs.
  assert(HNCol2 : ~ Col A C B') by (intro; apply HNCol1; ColR).
  assert(HNCol3 : ~ Col B B' C) by (intro; apply HNCol2; ColR).
  destruct (l8_18_existence A C B') as [C' []]; auto.
  exists A; exists B; exists C; exists A; exists B'; exists C'.
  assert(Par_strict B C B' C').
    apply (par_not_col_strict _ _ _ _ B'); Col; apply (l12_9 _ _ _ _ A C); Perp; Cop.
  assert(HNCol4 : ~ Col B C C') by (apply (par_strict_not_col_4 _ _ B'); auto).
  assert_diffs.
  assert(Bet A C C').
  { apply (col_two_sides_bet _ B); Col.
    apply l9_2.
    apply (l9_8_2 _ _ B').
      repeat split; Col; exists B; split; Col; Between.
      apply l12_6; Par.
  }
  assert(A <> C') by (intro; treat_equalities; auto).
  assert(Per B' C' A) by (apply perp_per_1; auto; apply (perp_col1 _ _ _ C); Col; Perp).
  assert(CongA B C A B' C' A) by (apply l11_16; Perp).
  assert(CongA C A B C' A B').
    apply (out_conga C A B C A B); try (apply out_trivial); CongA; apply bet_out; Between.
  split; Col; split.

    {
    intro.
    absurd(B = B'); auto.
    apply (between_cong A); Between.
    }

    {
    split; [|repeat (split; auto)].
    apply (sams2_suma2__conga456 C A B _ _ _ _ _ _ B C A).
    SumA.
    apply (conga2_sams__sams C' A B' A B' C'); CongA; SumA.
    apply t22_12__rah; Perp.
    apply (conga3_suma__suma C' A B' A B' C' B' C' A); CongA; apply t22_12__rah; auto.
    }
Qed.

End rah_similar.