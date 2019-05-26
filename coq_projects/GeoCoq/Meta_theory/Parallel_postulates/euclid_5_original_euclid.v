Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section euclid_5_original_euclid.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma euclid_5__original_euclid : euclid_5 -> euclid_s_parallel_postulate.
Proof.
  intros eucl A B C D P Q R Hos HIsi HSuma HNBet.
  assert(HM := midpoint_existence B C).
  destruct HM as [M].
  assert(HD' := symmetric_point_construction D C).
  destruct HD' as [D'].
  assert(HE := symmetric_point_construction D' M).
  destruct HE as [E].
  assert(Hdiff := HSuma).
  apply suma_distincts in Hdiff.
  spliter.
  assert_diffs.
  assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
  assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
  assert(HNCol3 : ~ Col M C D) by (intro; apply HNCol2; ColR).
  assert(HNCol4 : ~ Col M C D') by (intro; apply HNCol3; ColR).
  assert_diffs.
  assert(HNCol5 : ~ Col D' C B) by (intro; apply HNCol4; ColR).
  assert(HNCol6 : ~ Col M C E) by (intro; apply HNCol4; ColR).
  assert(HSAS := l11_49 C M D' B M E).
  destruct HSAS as [HCong HSAS]; eCong.
    apply l11_14; Between.
  destruct HSAS as [HConga1 HConga2]; auto.
  assert_diffs.
  assert(HA' : InAngle A C B E).
  { apply lea_in_angle; auto.
    - apply (l11_30 A B C B C D').
        apply (sams_chara D); Between; SumA.
        apply conga_pseudo_refl; auto.
      apply (out_conga M C D' M B E); try (apply bet_out); Between.

    - exists D'.
      split.
      { repeat split; auto; try (intro; apply HNCol4; ColR).
        exists M.
        split; Col; Between.
      }
      apply (l9_8_2 _ _ D); Side.
      { repeat split; Col.
        exists C; Col; Between.
      }
  }
  destruct HA' as [_ [_ [_ [A' [HBet [Habs|Hout]]]]]].
  { subst.
    exfalso.
    apply HNCol5; ColR.
  }

  assert(HY := eucl B C E D' M A').
  destruct HY as [Y HY]; Col; eCong; repeat split; Between.
    intro; subst; apply HNCol1; ColR.
  { intro.
    subst.
    apply HNBet.
    apply (bet_conga__bet D' C D); Between.
    apply (suma2__conga A B C B C D); auto.
    apply (conga3_suma__suma D' C B B C D D' C D); try (apply conga_refl); auto.
    2: apply (out_conga D' C M E B M); try (apply out_trivial); CongA; try (apply bet_out); Between.
    exists D.
    repeat (split; CongA); Cop.
    apply l9_9.
    repeat split; Col.
    exists C; Col; Between.
  }
  unfold BetS in HY.
  spliter.
  exists Y.
  split.
    apply (l6_7 _ _ A'); try solve [apply l6_6; auto]; apply (bet_out); auto.
  apply (l6_2 _ _ D'); Between.
Qed.

End euclid_5_original_euclid.