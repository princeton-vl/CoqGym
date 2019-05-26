Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section original_euclid_original_spp.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma original_euclid__original_spp : euclid_s_parallel_postulate -> alternative_strong_parallel_postulate.
Proof.
  intros oe A B C D P Q R Hos HSuma HNBet.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert(HD' := symmetric_point_construction D C).
  destruct HD' as [D'].
  assert (Hdiff := HSuma).
  apply suma_distincts in Hdiff.
  spliter.
  assert_diffs.
  elim(lea_total B C D C B A'); auto.
  { intro.
    assert(HY := oe A B C D P Q R).
    destruct HY as [Y []]; auto.
      apply (sams_chara _ _ _ _ _ _ A'); Between.
    assert_cols.
    exists Y; auto.
  }

  intro.
  assert(SAMS D' C B C B A') by (apply (sams_chara _ _ _ _ _ _ D); Between).
  assert(HSuma' := ex_suma A' B C B C D').
  destruct HSuma' as [P' [Q' [R' HSuma']]]; auto.
  assert(Hdiff := HSuma').
  apply suma_distincts in Hdiff.
  spliter.
  assert(HY := oe A' B C D' P' Q' R').
  destruct HY as [Y []]; SumA.
  3: exists Y; split; ColR.
  { assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
    assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
    exists D.
    split.
    apply l9_2; apply (l9_8_2 _ _ A); auto.
    - repeat split; Col.
      intro; apply HNCol1; ColR.
      exists B; Col; Between.
    - repeat split; Col.
      intro; apply HNCol2; ColR.
      exists C.
      split; Col; Between.
  }
  intro.
  apply HNBet.
  apply (bet_conga__bet P' Q' R'); auto.
  apply (suma2__conga A B C B C D); auto.
  apply suma_sym.
  apply (conga3_suma__suma A' B C B C D' P' Q' R'); auto.
  3: apply conga_refl; auto.
  - assert(HNCol : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
    assert(TS C B D D').
    { repeat split; Col.
      intro; apply HNCol; ColR.
      exists C; Col; Between.
    }
    apply (sams2_suma2__conga123 _ _ _ _ _ _ B C D' P' Q' R'); auto.
      SumA.
    { apply sams_left_comm.
      repeat split; Col.
        right; intro; assert_cols; Col.
      exists D'.
      split; CongA; split.
        apply l9_9; auto.
      split; Cop.
      intro Hts; destruct Hts as [_ []]; assert_cols; Col.
    }
    apply suma_left_comm.
    exists D'.
    split; CongA; split.
      apply l9_9; auto.
    split; Cop.
    apply conga_line; Between.

  - assert(HNCol : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
    assert(TS B C A A').
    { repeat split; Col.
      intro; apply HNCol; ColR.
      exists B; Col; Between.
    }
    apply (sams2_suma2__conga456 A' B C _ _ _ _ _ _ P' Q' R'); auto.
      SumA.
    { apply sams_left_comm.
      apply sams_sym.
      repeat split; Col.
        right; intro; assert_cols; Col.
      exists A'.
      split; CongA; split.
        apply l9_9; auto.
      split; Cop.
      intro Hts; destruct Hts as [_ []]; assert_cols; Col.
    }
    apply suma_sym.
    exists A'.
    split; CongA; split.
      apply l9_9; auto.
    split; Cop.
    apply conga_line; Between.
Qed.

End original_euclid_original_spp.