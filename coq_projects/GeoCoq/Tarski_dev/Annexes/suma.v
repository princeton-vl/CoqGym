Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section Suma_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma suma_distincts : forall A B C D E F G H I, SumA A B C D E F G H I ->
   A<>B /\ B<>C /\ D<>E /\ E<>F /\ G<>H /\ H<>I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J HJ].
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma trisuma_distincts : forall A B C D E F, TriSumA A B C D E F ->
  A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
  intros A B C D E F HTri.
  destruct HTri as [G [H [I [HSuma HSuma1]]]].
  apply suma_distincts in HSuma.
  apply suma_distincts in HSuma1.
  spliter; repeat split; auto.
Qed.

Lemma ex_suma : forall A B C D E F, A<>B -> B<>C -> D<>E -> E<>F ->
   exists G H I, SumA A B C D E F G H I.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  exists A.
  exists B.
  elim (col_dec A B C).
  { intro HColB.
    destruct (angle_construction_4 D E F C B A) as [J [HConga HCop]]; auto.
    assert_diffs.
    exists J.
    exists J.
    repeat (split; CongA); Cop.
      apply (col123__nos); Col.
  }
  intro HNColB.
  elim (col_dec D E F).
  { intro HColE.
    elim (bet_dec D E F).
    { intro HEBet.
      assert (HJ : exists J, Midpoint B C J) by (apply symmetric_point_construction).
      destruct HJ as [J HMid].
      assert_diffs.
      destruct HMid as [HJBet HCong].
      exists J.
      exists J.
      split.
      apply conga_line; Between; repeat split; auto; intro; treat_equalities; absurde.
      split.
        apply col124__nos; Col.
      split; CongA; Cop.
    }
    intro HENBet.
    assert (HEOut : Out E D F) by (apply l6_4_2; auto).
    exists C.
    exists C.
    split.
    apply (out_conga C B C D E D); auto; try (apply out_trivial); CongA.
    split.
      apply col124__nos; Col.
    split; CongA; Cop.
  }
  intro HNColE.
  assert (HJ : exists J, CongA D E F C B J /\ TS C B J A) by (apply ex_conga_ts; Col).
  destruct HJ as [J [HConga HTwo]].
  assert_diffs.
  exists J.
  exists J.
  repeat (split; CongA); Cop.
  apply l9_9; apply l9_2; apply invert_two_sides; auto.
Qed.

(** Unicity of the sum. *)

Lemma suma2__conga : forall A B C D E F G H I G' H' I',
   SumA A B C D E F G H I -> SumA A B C D E F G' H' I' -> CongA G H I G' H' I'.
Proof.
  intros A B C D E F G H I G' H' I' Hsuma Hsuma'.
  destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HCop]]]].
  destruct Hsuma' as [J' [HJ'1 [HJ'2 [HJ'3 HCop']]]].
  assert_diffs.
  assert (HcongaC : CongA C B J C B J') by (apply (conga_trans C B J D E F); auto; apply conga_sym; auto).
  assert (HcongaA : CongA A B J A B J').
  { elim (col_dec A B C).
    { intro HColB.
      elim (bet_dec A B C).
      { intro HBBet.
        apply (l11_13 C B J C B J'); Between.
      }
      intro HBNBet.
      assert (HBOut : Out B A C) by (apply l6_4_2; auto).
      apply (l11_10 C B J C B J'); try (apply out_trivial); auto.
    }
    intro HNColB.
    elim (col_dec D E F).
    { intro HColE.
      apply (out_conga A B J A B J); try (apply out_trivial); CongA.
      elim (bet_dec D E F).
      { intro HEBet.
        apply l6_3_2; repeat split; auto.
        exists C.
        split; auto; split; apply (bet_conga__bet D E F); CongA.
      }
      intro HENBet.
      assert (HEOut : Out E D F) by (apply l6_4_2; auto).
      apply (l6_7 B J C); apply (l11_21_a D E F); CongA.
    }
    intro HNColE.
    apply (l11_22a A B J C A B J' C); auto.
    repeat (split; try (apply cop__not_one_side_two_sides); CongA); Cop;
    apply (ncol_conga_ncol D E F); CongA.
  }
  apply (conga_trans G H I A B J).
  CongA.
  apply (conga_trans A B J A B J'); auto.
Qed.

(** Commutativity of the sum. *)

Lemma suma_sym : forall A B C D E F G H I, SumA A B C D E F G H I -> SumA D E F A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J [HCongaBCJ [HNOne [HCongaABJ HCop]]]].
  assert_diffs.
  elim (col_dec A B C).
  { intro HColB.
    elim (bet_dec A B C).
    { intro HBBet.
      assert (HK : exists K, Midpoint E F K) by (apply symmetric_point_construction).
      destruct HK as [K [HKBet HCong]].
      assert_diffs.
      exists K.
      split; try (apply conga_line; auto).
      split.
        intro HOne.
        assert (~ Col E F K) by (apply (one_side_not_col123 E F K D); apply one_side_symmetry; auto).
        assert_cols; Col.
      split; Cop.
      apply (conga_trans D E K A B J); auto.
      apply conga_left_comm; apply (l11_13 F E D C B J); Between; CongA.
    }
    intro HBNBet.
    assert (HBOut : Out B A C) by (apply l6_4_2; auto).
    exists F.
    split.
    apply (l11_10 F E F C B C); try (apply out_trivial); CongA.
    split.
    apply col124__nos; Col.
    split; Cop.
    apply (conga_trans D E F A B J); auto.
    apply conga_sym.
    apply (l11_10 C B J D E F); try (apply out_trivial); auto.
  }

  intro HNColB.
  elim (col_dec D E F).
  { intro HColE.
    assert (HK : exists K, CongA A B C F E K) by (apply angle_construction_3; auto).
    destruct HK as [K HConga].
    assert_diffs.
    exists K.
    split; CongA.
    split.
    intro HOne; assert (~ Col E F D) by (apply (one_side_not_col123 E F D K); auto); Col.
    split; Cop.
    apply (conga_trans D E K A B J); auto.
    elim (bet_dec D E F).
    { intro HEBet.
      apply conga_sym; apply conga_left_comm.
      apply (l11_13 C B A F); CongA; Between.
      apply (bet_conga__bet D E F); CongA.
    }
    intro HENBet.
    assert (HEOut : Out E D F) by (apply l6_4_2; auto).
    apply conga_sym.
    apply (l11_10 A B C F E K); try (apply out_trivial); auto.
    apply (l11_21_a D E F); CongA.
  }

  intro HNColE.
  assert (HK : exists K, CongA A B C F E K /\ TS F E K D) by (apply ex_conga_ts; Col).
  destruct HK as [K [HConga HTwo]].
  exists K.
  split; CongA.
  split.
  apply l9_9; apply l9_2; apply invert_two_sides; auto.
  split; Cop.
  apply (conga_trans D E K A B J); auto.
  apply conga_sym; apply conga_right_comm.
  apply (l11_22a A B J C K E D F).
  split.
  apply cop__not_one_side_two_sides; Col; Cop.
    intro; assert (Col D E F) by (apply (col_conga_col C B J D E F); Col); Col.
  split.
    apply invert_two_sides; auto.
  split; CongA.
Qed.

(** CongA preserves SumA. *)

Lemma conga3_suma__suma : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   SumA A B C D E F G H I ->
   CongA A B C A' B' C' ->
   CongA D E F D' E' F' ->
   CongA G H I G' H' I' ->
   SumA A' B' C' D' E' F' G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' Hsuma HCongaB HCongaE HCongaH.
  assert (Hsuma' : SumA D' E' F' A B C G' H' I').
  { apply suma_sym.
    destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HCop]]]].
    exists J.
    split.
    apply (conga_trans C B J D E F); auto.
    split; auto.
    split; auto.
    apply (conga_trans A B J G H I); auto.
  }
  apply suma_sym.
  destruct Hsuma' as [J [HJ1 [HJ2 [HJ3 HCop]]]].
  exists J.
  split.
    apply (conga_trans F' E' J A B C); auto.
  repeat (split; auto).
Qed.

(** Out preserves SumA. *)

Lemma out6_suma__suma : forall A B C D E F G H I A' C' D' F' G' I',
   SumA A B C D E F G H I -> Out B A A' -> Out B C C' -> Out E D D' ->
   Out E F F' -> Out H G G' -> Out H I I' -> SumA A' B C' D' E F' G' H I'.
Proof.
  intros.
  assert_diffs.
  apply (conga3_suma__suma A B C D E F G H I); auto.
    apply (out_conga A B C A B C); try (apply out_trivial); CongA.
    apply (out_conga D E F D E F); try (apply out_trivial); CongA.
    apply (out_conga G H I G H I); try (apply out_trivial); CongA.
Qed.

(** ABC + 0 =  ABC (two lemmas) *)

Lemma out546_suma__conga : forall A B C D E F G H I, SumA A B C D E F G H I ->
   Out E D F -> CongA A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  assert(A<>B/\B<>C/\D<>E/\E<>F/\G<>H/\H<>I) by (apply suma_distincts; auto).
  spliter.
  apply (suma2__conga A B C D E F A B C); auto.
  exists C.
  split.
  apply (out_conga C B C D E D); try (apply out_trivial); CongA.
  split.
    apply col124__nos; Col.
  split; Cop; CongA.
Qed.

Lemma out546__suma : forall A B C D E F, A <> B -> B <> C -> Out E D F -> SumA A B C D E F A B C.
Proof.
  intros A B C D E F HAB HBC Hout.
  assert_diffs.
  destruct (ex_suma A B C D E F) as [G [H [I Hsuma]]]; auto.
  apply (conga3_suma__suma A B C D E F G H I); try (apply conga_refl); auto.
  apply conga_sym, out546_suma__conga with D E F; auto.
Qed.

(** 0 + DEF = DEF (two lemmas) *)

Lemma out213_suma__conga : forall A B C D E F G H I, SumA A B C D E F G H I ->
   Out B A C -> CongA D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  apply (out546_suma__conga D E F A B C); auto.
  apply suma_sym; auto.
Qed.

Lemma out213__suma : forall A B C D E F, D <> E -> E <> F -> Out B A C -> SumA A B C D E F D E F.
Proof.
  intros; apply suma_sym, out546__suma; auto.
Qed.

(** Some permutation properties:*)

Lemma suma_left_comm : forall A B C D E F G H I,
   SumA A B C D E F G H I -> SumA C B A D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); CongA.
Qed.

Lemma suma_middle_comm : forall A B C D E F G H I,
   SumA A B C D E F G H I -> SumA A B C F E D G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); CongA.
Qed.

Lemma suma_right_comm : forall A B C D E F G H I,
   SumA A B C D E F G H I -> SumA A B C D E F I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); CongA.
Qed.

Lemma suma_comm : forall A B C D E F G H I,
   SumA A B C D E F G H I -> SumA C B A F E D I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); CongA.
Qed.

(** Basic cases of sum *)

Lemma ts__suma : forall A B C D, TS A B C D -> SumA C B A A B D C B D.
Proof.
  intros A B C D HTS.
  exists D.
  assert_diffs.
  split; CongA.
  split; Side.
  split; CongA; Cop.
Qed.

Lemma inangle__suma : forall A B C P, InAngle P A B C -> SumA A B P P B C A B C.
Proof.
  intros A B C P HInangle.
  assert (Hcopy := HInangle); destruct Hcopy as [HAB [HCB [HPB _]]].
  exists C; repeat (split; CongA); Cop.
  elim (col_dec B P A).
    apply col123__nos.
  intro HNCol.
  elim (col_dec B P C).
    apply col124__nos.
  intro HNCol2.
  apply l9_9, invert_two_sides, in_angle_two_sides; Col.
Qed.

Lemma bet__suma : forall A B C P, A <> B -> B <> C -> P <> B -> Bet A B C ->
  SumA A B P P B C A B C.
Proof.
  intros A B C P HAB HBC HPB HBet.
  apply inangle__suma.
  apply in_angle_line; auto.
Qed.


(** Characterization of SAMS using LeA. *)

Lemma sams_chara : forall A B C D E F A', A<>B -> A'<>B -> Bet A B A' ->
   (SAMS A B C D E F <-> LeA D E F C B A').
Proof.
  intros A B C D E F A' HAB HA'B HABA'.
  split.
  - intro Hint.
    destruct Hint as [_ [HUn [J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
    assert_diffs.
    destruct HUn as [HEOut | HBNBet].
    apply l11_31_1; auto.
    elim (col_dec A B C).
    { intro HColB.
      apply l11_31_2; auto.
      apply (bet_out_out_bet A B A'); try (apply out_trivial); auto.
      apply l6_4_2; auto.
    }
    intro HNColB.
    elim (col_dec D E F).
    { intro HColE.
      elim (bet_dec D E F).
      { intro HDEF.
        exfalso.
        apply HJ3.
        assert (HCBJ : Bet C B J) by (apply (bet_conga__bet D E F); CongA; Between); assert_cols.
        repeat split; Col.
        intro; apply HNColB; apply (l6_16_1 B J C A); Col.
        exists B.
        split; Col; Between.
      }
      intro; apply l11_31_1; auto; apply l6_4_2; auto.
    }
    intro HNColE.
    apply (l11_30 C B J C B A'); try (apply conga_refl); auto.
    exists J.
    split; CongA.
    apply l11_24; apply (in_angle_reverse A); auto.
    assert (HTwo : TS B C A J).
    { apply cop__not_one_side_two_sides; Cop.
      apply (ncol_conga_ncol D E F); CongA.
    }
    destruct HTwo as [_ [_ [X [HXCol HXBet]]]].
    repeat split; auto.
    exists X.
    split; auto.
    elim (eq_dec_points B X); auto.
    intro HBX.
    right.
    apply (col_one_side_out B A X C); Col.
    apply invert_one_side.
    apply (one_side_transitivity A B X J).
    { apply out_one_side.
      left; intro; apply HNColB; apply (l6_16_1 B X); Col.
      assert (HAX : A<>X) by (intro; treat_equalities; Col).
      repeat split; auto.
      intro; treat_equalities; auto.
    }
    apply one_side_symmetry.
    apply cop__not_two_sides_one_side; Col; Cop.
    intro; apply HNColB; apply (l6_16_1 B X); Col; apply (col_transitivity_2 J); Col.
    intro; treat_equalities; auto.

  - intro Hlea.
    assert_diffs.
    split; auto.
    elim (col_dec A B C).
    { intro HColB.
      elim (bet_dec A B C).
      { intro HBBet.
        assert (HEOut : Out E D F).
        { assert (Out B C A') by (apply (l6_3_2); repeat split; auto; exists A; repeat split; Between).
          apply (l11_21_a C B A'); auto.
          apply lea_asym; auto.
          apply l11_31_1; auto.
        }
        split; try left; auto.
        exists C.
        split.
        apply (out_conga C B C D E D); try (apply out_trivial); CongA.
        split.
        apply col124__nos; Col.
        split; Cop.
        apply not_two_sides_id.
      }
      intro HBNBet.
      assert (HBOut : Out B A C) by (apply not_bet_out; auto).
      split.
      right; auto.
      assert (HJ : exists J : Tpoint, CongA D E F C B J) by (apply (angle_construction_3 D E F C B); auto).
      destruct HJ as [J HJ].
      exists J.
      split; CongA.
      split.
      apply col123__nos; Col.
      split; Cop.
      intro HTwo; destruct HTwo as [HBA [HNCol _]]; Col.
    }
    intro HNColB.
    assert (HNColB' : ~ Col A' B C) by (intro; apply HNColB; apply (l6_16_1 B A'); Col).
    elim (col_dec D E F).
    { intro HNColE.
      assert (HEOut : Out E D F).
      { apply not_bet_out; auto.
        intro HEBet.
        apply HNColB'.
        apply bet_col; apply between_symmetry.
        apply (bet_lea__bet D E F); auto.
      }
      split.
      left; auto.
      exists C.
      split.
      apply (out_conga C B C D E D); try (apply out_trivial); CongA.
      split.
      apply col124__nos; Col.
      split; Cop.
      apply not_two_sides_id.
    }
    intro HNColE.
    split.
    right; intro; Col.
    assert (HJ : exists J, CongA D E F C B J /\ TS C B J A) by (apply ex_conga_ts; Col).
    destruct HJ as [J [HCongaJ HTwo]].
    assert_diffs.
    exists J.
    split; CongA.
    split.
    apply l9_9; apply l9_2; apply invert_two_sides; auto.
    elim (col_dec A B J).
    { intro HColJ.
      split; Cop.
      intro HTwo'.
      destruct HTwo' as [HBA [HNColC [HNColJ _]]].
      Col.
    }
    intro HNColJ.
    assert (HF : ~ TS A' B C J).
    { apply l9_9_bis.
      apply one_side_symmetry.
      apply (in_angle_one_side); auto.
      intro; apply HNColJ; apply (l6_16_1 B A'); Col.
      apply l11_24.
      destruct Hlea as [K [HInAngle HCongaK]].
      apply (conga_preserves_in_angle C B A' K C B A' J); CongA.
      apply (conga_trans C B K D E F); CongA.
      exists A; split; auto.
      repeat (split; Col).
      exists B; split; Between; Col.
    }
    split; Cop.
    intro; apply HF.
    apply (col_preserves_two_sides A B); Col.
Qed.

Lemma sams_distincts : forall A B C D E F, SAMS A B C D E F ->
   A<>B /\ B<>C /\ D<>E /\ E<>F.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HP1 [HP2 [J HJ]]].
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma sams_sym : forall A B C D E F, SAMS A B C D E F ->
   SAMS D E F A B C.
Proof.
  intros A B C D E F Hisi.
  assert(A<>B/\B<>C/\D<>E/\E<>F) by (apply sams_distincts; auto).
  spliter.
  assert(HD' : exists D', Midpoint E D D') by apply symmetric_point_construction.
  destruct HD' as [D'].
  assert(HA' : exists A', Midpoint B A A') by apply symmetric_point_construction.
  destruct HA' as [A'].
  assert_diffs.
  apply (sams_chara D E F A B C D'); Between.
  apply lea_right_comm.
  apply (l11_36 D _ _ A'); Between.
  apply lea_right_comm.
  apply (sams_chara A); Between.
Qed.

Lemma sams_right_comm : forall A B C D E F, SAMS A B C D E F ->
   SAMS A B C F E D.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HAB [HUn [J [HJ1 [HJ2 HJ3]]]]].
  split; auto.
  split.
  { destruct HUn.
    left; apply l6_6; auto.
    right; auto.
  }
  exists J.
  split.
  apply conga_right_comm; auto.
  split; auto.
Qed.

Lemma sams_left_comm : forall A B C D E F, SAMS A B C D E F ->
   SAMS C B A D E F.
Proof.
  intros.
  apply sams_sym.
  apply sams_right_comm.
  apply sams_sym.
  assumption.
Qed.

Lemma sams_comm : forall A B C D E F, SAMS A B C D E F ->
   SAMS C B A F E D.
Proof.
  intros.
  apply sams_left_comm.
  apply sams_right_comm.
  assumption.
Qed.

Lemma conga2_sams__sams : forall A B C D E F A' B' C' D' E' F',
   CongA A B C A' B' C' -> CongA D E F D' E' F' ->
   SAMS A B C D E F -> SAMS A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HCongaB HCongaE Hisi.
  assert(HA0 : exists A0, Midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, Midpoint B' A' A'0) by apply symmetric_point_construction.
  destruct HA'0 as [A'0].
  assert_diffs.
  apply (sams_chara _ _ _ _ _ _ A'0); Between.
  apply (l11_30 D E F C B A0); try (apply (sams_chara A)); Between.
  apply conga_comm.
  apply (l11_13 A B C A'); Between.
Qed.

Lemma out546__sams : forall A B C D E F, A <> B -> B <> C -> Out E D F -> SAMS A B C D E F.
Proof.
  intros A B C D E F HAB HBC HOut.
  destruct (segment_construction A B A B) as [A' [HBet HCong]].
  assert_diffs.
  apply sams_chara with A'; auto.
  apply l11_31_1; auto.
Qed.

Lemma out213__sams : forall A B C D E F, D <> E -> E <> F -> Out B A C -> SAMS A B C D E F.
Proof.
  intros; apply sams_sym, out546__sams; trivial.
Qed.

Lemma bet_suma__sams : forall A B C D E F G H I, SumA A B C D E F G H I -> Bet G H I ->
  SAMS A B C D E F.
Proof.
  intros A B C D E F G H I HSuma HBet.
  destruct HSuma as [A' [HConga1 [HNOS [HCop HConga2]]]].
  apply (bet_conga__bet _ _ _ A B A') in HBet; CongA.
  assert_diffs.
  repeat split; auto.
  - elim (bet_dec A B C).
    { intro HBet'; left.
      apply (l11_21_a C B A'); trivial.
      apply l6_2 with A; Between.
    }
    intro HNBet; auto.
  - exists A'; repeat (split; auto).
    intro HTS; destruct HTS as [_ []]; assert_cols; Col.
Qed.

Lemma bet__sams : forall A B C P, A <> B -> B <> C -> P <> B -> Bet A B C -> SAMS A B P P B C.
Proof.
  intros A B C P HAB HBC HPB HBet.
  apply bet_suma__sams with A B C.
    apply bet__suma; auto.
    assumption.
Qed.

Lemma suppa__sams : forall A B C D E F, SuppA A B C D E F -> SAMS A B C D E F.
Proof.
  intros A B C D E F [HAB [A' [HBet HCong]]].
  assert_diffs.
  apply (conga2_sams__sams A B C C B A'); CongA.
  apply bet__sams; auto.
Qed.

Lemma inangle__sams : forall A B C P, InAngle P A B C -> SAMS A B P P B C.
Proof.
  intros A B C P HInangle.
  assert (Hcopy := HInangle); destruct Hcopy as [HAB [HCB [HPB HX]]].
  repeat split; auto.
  { destruct (bet_dec A B P) as [HBet|]; [left|auto].
    apply l6_2 with A; Between.
    destruct HX as [X [HBet1 [HXB|HOut]]]; [subst X; Between|].
    assert (HBet2 : Bet X B A) by (assert_diffs; apply (l6_2 P); Between; apply l6_6, HOut).
    eBetween.
  }
  exists C; split; CongA.
  destruct (col_dec B P A) as [HCol|HNCol].
    repeat split; [apply col123__nos, HCol|intro HTS; destruct HTS as []; Col|Cop].
  repeat split; Cop.
  - destruct (col_dec B P C) as [HCol1|HNCol1].
      apply col124__nos, HCol1.
    apply l9_9, invert_two_sides, in_angle_two_sides; Col.
  - destruct (col_dec A B C) as [HCol1|HNCol1].
      intro HTS; destruct HTS as [_ []]; Col.
    apply l9_9_bis, in_angle_one_side; Col.
Qed.

End Suma_1.


Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D (swap_diff B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H (swap_diff B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H (swap_diff C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_at ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= conga_diff1 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= conga_diff2 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= conga_diff45 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= conga_diff56 A B C A' B' C' H);clean_reap_hyps

      | H:(Orth_at ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:SumA ?A ?B ?C ?D ?E ?F ?G ?I ?J |- _ =>
      let h := fresh in
      not_exist_hyp6 A B B C D E E F G I I J;
      assert (h := suma_distincts A B C D E F G I J H);decompose [and] h;clear h;clean_reap_hyps
      | H: TriSumA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp5 A B B C A C D E E F;
      assert (h := trisuma_distincts A B C D E F H);decompose [and] h;clear h; clean_reap_hyps
      | H:SAMS ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := sams_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(InAngle ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := inangle_distincts A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:LeA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lea_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:LtA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lta_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Acute ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := acute_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Obtuse ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := obtuse_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:SuppA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
 end.

Hint Resolve suma_sym suma_left_comm suma_middle_comm suma_right_comm
             suma_comm ts__suma inangle__suma bet__suma
             sams_right_comm sams_comm sams_left_comm sams_sym
             out213__sams out546__sams bet__sams suppa__sams inangle__sams : suma.

Ltac SumA := eauto with suma.

Section Suma_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** ABC <= ABC + DEF. *)

Lemma sams_suma__lea123789 : forall A B C D E F G H I, SumA A B C D E F G H I ->
   SAMS A B C D E F -> LeA A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  assert_diffs.
  spliter.
  elim(col_dec A B C).
  { intro HColB.
    elim(bet_dec A B C).
    { intro HBBet.
      destruct Hisi as [_[[HEout|]]]; try solve[exfalso; auto].
      apply conga__lea.
      apply (out546_suma__conga _ _ _ D E F); auto.
    }
    intro HBout.
    apply l11_31_1; auto.
    apply not_bet_out; auto.
  }
  intro HNColB.
  elim(col_dec D E F).
  { intro HColE.
    elim(bet_dec D E F).
    { intro HEBet.
      apply sams_sym in Hisi.
      destruct Hisi as [_[[HBout|]]]; try solve[exfalso; auto].
      apply l11_31_1; auto.
    }
    intro HEout.
    apply conga__lea.
    apply (out546_suma__conga _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(col_dec G H I).
  { intro HColH.
    elim(bet_dec G H I).
      apply l11_31_2; auto.
    intro HHout.
    apply not_bet_out in HHout; auto.
    exfalso.
    destruct Hisi as [_ [HUn _]].
    destruct HUn as [HEout | HBNBet].
      apply HNColE; apply col_permutation_4; apply out_col; auto.
    destruct Hsuma as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
    apply HJ2.
    apply conga_sym in HJ4.
    apply l11_21_a in HJ4; auto.
    apply (l9_19 _ _ _ _ B); try split; Col.
  }
  intro HNColH.
  destruct Hisi as [_ [_ [J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
  assert_diffs.
  assert(HNColJ : ~ Col J B C).
  { intro HColJ.
    apply HNColE.
    apply (col_conga_col J B C); CongA.
  }
  assert(HCongaJ : CongA A B J G H I).
  { apply (suma2__conga A B C D E F); auto.
    exists J.
    repeat (split; CongA).
  }
  assert(HNColJ2 : ~ Col J B A).
  { intro HColJ.
    apply HNColH.
    apply (col_conga_col A B J); Col.
  }
  apply (l11_30 A B C A B J); CongA.
  exists C.
  split; CongA.
  apply cop__not_one_side_two_sides in HJ2; Cop.
  destruct HJ2 as [a [b [X [HColX HXBet]]]].
  repeat split; auto.
  exists X.
  split; auto.
  right.
  assert(HNColX : ~Col X A B).
  { intro.
    apply HNColJ2.
    apply col_permutation_1; apply (col_transitivity_1 A X); Col.
    intro; subst X; Col.
  }
  assert_diffs.
  apply (col_one_side_out _ A); Col.
  apply invert_one_side.
  apply (one_side_transitivity _ _ _ J).
  - apply out_one_side.
    left; Col.
    apply bet_out; auto.
  - apply one_side_symmetry.
    apply cop__not_two_sides_one_side; Col; Cop.
Qed.

(** DEF <= ABC + DEF. *)

Lemma sams_suma__lea456789 : forall A B C D E F G H I, SumA A B C D E F G H I ->
   SAMS A B C D E F -> LeA D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  apply (sams_suma__lea123789 D E F A B C G H I); SumA.
Qed.

(** LeA preserves SAMS. *)

Lemma sams_lea2__sams : forall A B C D E F A' B' C' D' E' F',
   SAMS A' B' C' D' E' F' -> LeA A B C A' B' C' -> LeA D E F D' E' F' ->
   SAMS A B C D E F.
Proof.
  intros A B C D E F A' B' C' D' E' F' Hisi HleaB HleaE.
  assert(HA0 : exists A0, Midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, Midpoint B' A' A'0) by apply symmetric_point_construction.
  destruct HA'0 as [A'0].
  assert_diffs.
  apply (sams_chara _ _ _ _ _ _ A0); Between.
  apply (lea_trans D E F D' E' F'); auto.
  apply (lea_trans D' E' F' C' B' A'0).
  - apply (sams_chara A'); Between.
  - apply lea_comm.
    apply (l11_36 A B C A'); Between.
Qed.

Lemma sams_lea456_suma2__lea : forall A B C D E F G H I D' E' F' G' H' I',
   LeA D E F D' E' F' -> SAMS A B C D' E' F' -> SumA A B C D E F G H I ->
   SumA A B C D' E' F' G' H' I' -> LeA G H I G' H' I'.
Proof.
  intros A B C D E F G H I D' E' F' G' H' I' Hlea Hisi' Hsuma Hsuma'.
  assert_diffs.
  elim(out_dec E' D' F').
  { intro HE'out.
    apply conga__lea.
    apply (conga_trans _ _ _ A B C).
    apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto; apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (out546_suma__conga _ _ _ D' E' F'); auto.
  }
  intro HE'Nout.
  elim(col_dec A B C).
  { intro HColB.
    destruct Hisi' as [_ [[HE'out|HBNBet]_]].
    exfalso; auto.
    apply not_bet_out in HColB; auto.
    apply (l11_30 D E F D' E' F'); auto; apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  elim(col_dec D' E' F').
  { intro HColE'.
    apply sams_sym in Hisi'.
    destruct Hisi' as [_ [[HBout|HE'NBet]_]]; exfalso.
    apply HNColB; assert_cols; Col.
    apply not_bet_out in HColE'; auto.
  }
  intro HNColE'.
  clear HE'Nout.
  elim(col_dec D E F).
  { intro HColE.
    assert(~ Bet D E F) by (intro; apply HNColE'; apply bet_col; apply (bet_lea__bet D E F); auto).
    apply (l11_30 A B C G' H' I'); try (apply conga_refl); auto.
    apply (sams_suma__lea123789 _ _ _ D' E' F'); auto.
    apply (out546_suma__conga _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(col_dec G' H' I').
  { intro HColH'.
    elim(bet_dec G' H' I').
    apply l11_31_2; auto.
    intro HH'out.
    apply not_bet_out in HH'out; auto.
    exfalso.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ G' H' I'); auto.
    apply (sams_suma__lea123789 _ _ _ D' E' F'); auto.
  }
  intro HNColH'.
  destruct Hisi' as [_[_[F'1]]].
  spliter.
  apply(l11_30 _ _ _ _ _ _ D E F C B F'1) in Hlea; CongA.
  destruct Hlea as [F1].
  spliter.
  assert_diffs.
  assert(CongA A B F'1 G' H' I').
  apply (suma2__conga A B C D' E' F'); auto; exists F'1; repeat (split; CongA).
  assert(~ Col A B F'1) by (apply (ncol_conga_ncol G' H' I'); CongA).
  assert(~ Col C B F'1) by (apply (ncol_conga_ncol D' E' F'); CongA).
  apply (l11_30 A B F1 A B F'1); auto.
  - exists F1.
    split; CongA.
    apply l11_24.
    apply (in_angle_trans _ _ _ C).
    apply l11_24; auto.
    assert(Hts : TS B C A F'1) by (apply cop__not_one_side_two_sides; Col; Cop).
    destruct Hts as [_ [_ [X]]].
    spliter.
    repeat split; auto.
    exists X.
    split; Between.
    right.
    apply (col_one_side_out _ A); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ F'1); auto.
      apply out_one_side; Col; apply bet_out; auto; intro; subst A; Col.
    apply one_side_symmetry; apply cop__not_two_sides_one_side; Col.

  - apply (suma2__conga A B C D E F); auto.
    exists F1.
    repeat (split; CongA).
    { apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ F'1).
        apply l9_2; apply cop__not_one_side_two_sides; Col; Cop.
      apply invert_one_side; apply one_side_symmetry.
      apply in_angle_one_side; Col.
      apply not_col_permutation_4; apply (ncol_conga_ncol D E F); auto.
    }
    apply coplanar_perm_12, coplanar_trans_1 with F'1; Col; Cop.
Qed.

Lemma sams_lea123_suma2__lea : forall A B C D E F G H I A' B' C' G' H' I',
   LeA A B C A' B' C' -> SAMS A' B' C' D E F -> SumA A B C D E F G H I ->
   SumA A' B' C' D E F G' H' I' -> LeA G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C'.
  intros.
  apply (sams_lea456_suma2__lea D E F A B C _ _ _ A' B' C'); SumA.
Qed.

(** SumA preserves LeA. *)

Lemma sams_lea2_suma2__lea : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA A B C A' B' C' -> LeA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LeA G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HleaB HleaD Hisi' Hsuma Hsuma'.
  assert_diffs.
  assert(Haux := ex_suma A B C D' E' F').
  destruct Haux as [G'' [H'' [I'']]]; auto.
  apply (lea_trans _ _ _ G'' H'' I'').
  - apply (sams_lea456_suma2__lea A B C D E F _ _ _ D' E' F'); auto.
    apply (sams_lea2__sams _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  - apply (sams_lea123_suma2__lea A B C D' E' F' _ _ _ A' B' C'); auto.
Qed.

(** Unicity of the difference of angles. *)

Lemma sams2_suma2__conga456 : forall A B C D E F D' E' F' G H I,
   SAMS A B C D E F -> SAMS A B C D' E' F' ->
   SumA A B C D E F G H I -> SumA A B C D' E' F' G H I ->
   CongA D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' G H I Hisi Hisi' Hsuma Hsuma'.
  assert_diffs.
  elim(col_dec A B C).
  { intro HColB.
    elim(bet_dec A B C).
    { intro HBBet.
      destruct Hisi as [_ [[HEout|]_]]; try solve [exfalso; Between].
      destruct Hisi' as [_ [[HE'out|]_]]; try solve [exfalso; Between].
      apply l11_21_b; auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    apply (conga_trans _ _ _ G H I).
    - apply (out213_suma__conga A B C); auto.
    - apply conga_sym.
      apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  destruct Hisi as [_[_[J [HJ1 [HJ2 [HJ3 HJ4]]]]]].
  destruct Hisi' as [_[_[J' [HJ'1 [HJ'2 [HJ'3 HJ'4]]]]]].
  assert_diffs.
  apply (conga_trans _ _ _ C B J); try solve [apply conga_sym; auto].
  apply (conga_trans _ _ _ C B J'); auto.
  assert(CongA A B J A B J').
  { apply (conga_trans _ _ _ G H I).
      apply (suma2__conga A B C D E F); auto; exists J; repeat (split; CongA).
    apply (suma2__conga A B C D' E' F'); auto; exists J'; repeat (split; CongA).
  }
  assert(HJJ' : Out B J J' \/ TS A B J J').
    apply conga_cop__or_out_ts; auto.
    apply coplanar_trans_1 with C; Cop; Col.
  destruct HJJ' as [Hout|Hts].
  - apply (out_conga C B J C B J); try (apply out_trivial); CongA.
  - exfalso.
    apply HJ'3.
    apply (l9_8_2 _ _ J); auto.
    apply one_side_symmetry.
    apply cop__not_two_sides_one_side; Col.
    apply two_sides_not_col in Hts; Col.
Qed.

(** Unicity of the difference on the left. *)

Lemma sams2_suma2__conga123 : forall A B C A' B' C' D E F G H I,
   SAMS A B C D E F -> SAMS A' B' C' D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D E F G H I ->
   CongA A B C A' B' C'.
Proof.
  intros A B C A' B' C' D E F G H I Hisi Hisi' Hsuma Hsuma'.
  apply (sams2_suma2__conga456 D E F _ _ _ _ _ _ G H I); SumA.
Qed.

Lemma suma_assoc_1 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   SumA A' B' C' G H I K L M -> SumA A B C D' E' F' K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F' HisiBE HisiEH HsBE HsEH HsB'H.
  assert(HA0 : exists A0, Midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HD0 : exists D0, Midpoint E D D0) by apply symmetric_point_construction.
  destruct HD0 as [D0].
  assert_diffs.
  elim(col_dec A B C).
  { intro HColB.
    elim(bet_dec A B C).
    { intro HBBet.
      destruct HisiBE as [_ [[HEout | HBNBet] HJ]]; try solve [exfalso; Between].
      apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    assert(Hexsuma : exists K0 L0 M0, SumA A B C D' E' F' K0 L0 M0) by (apply ex_suma; auto).
    destruct Hexsuma as [K0 [L0 [M0]]].
    apply (conga3_suma__suma A B C D' E' F' K0 L0 M0); try (apply conga_refl); auto.
    apply (conga_trans _ _ _ D' E' F').
    apply conga_sym; apply (out213_suma__conga A B C); auto.
    apply (suma2__conga D E F G H I); auto.
    apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
    apply conga_sym.
    apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  assert(~ Col C B A0) by (intro; apply HNColB; apply (l6_16_1 _ A0); Col).
  elim(col_dec D E F).
  { intro HColE.
    elim(bet_dec D E F).
    { intro HEBet.
      destruct HisiEH as [_ [[HHout | HENBet] HJ]]; try solve [exfalso; Between].
      apply (conga3_suma__suma A B C D E F A' B' C'); try (apply conga_refl); try (apply (out546_suma__conga _ _ _ G H I)); auto.
    }
    intro HEout.
    apply not_bet_out in HEout; auto.
    apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
    apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
    apply (out213_suma__conga D E F); auto.
  }
  intro HNColE.
  assert(~ Col F E D0) by (intro; apply HNColE; apply (l6_16_1 _ D0); Col).
  elim(col_dec G H I).
  { intro HColH.
    elim(bet_dec G H I).
    { intro HHBet.
      apply sams_sym in HisiEH.
      destruct HisiEH as [_ [[HEout | HHNBet] HJ]]; try solve [exfalso; Between].
      exfalso.
      apply HNColE.
      apply col_permutation_4.
      apply out_col; auto.
    }
    intro HHout.
    apply not_bet_out in HHout; auto.
    apply (conga3_suma__suma A B C D E F A' B' C'); try (apply conga_refl); try (apply (out546_suma__conga _ _ _ G H I)); auto.
  }
  intro HNColH.
  assert(~ OS B C A A0).
  { apply l9_9.
    repeat split; Col.
    exists B.
    split; Col; Between.
  }
  assert(HisiA0: SAMS A B C A0 B C).
  { split; auto.
    split.
      right; intro; assert_cols; Col.
    exists A0.
    repeat (split; CongA); Cop.
    unfold TS.
    intro; spliter; assert_cols; Col.
  }
  assert(~ OS E F D D0).
  { apply l9_9.
    repeat split; Col.
    exists E.
    split; Col; Between.
  }
  assert(HisiD0: SAMS D E F D0 E F).
  { split; auto.
    split.
      right; intro; assert_cols; Col.
    exists D0.
    repeat (split; CongA); Cop.
    unfold TS.
    intro; spliter; assert_cols; Col.
  }
  elim(col_dec A' B' C').
  { intro HColB'.
    elim(bet_dec A' B' C').
    { intro HB'Bet.
      elim(col_dec D' E' F').
      { intro HColE'.
        elim(bet_dec D' E' F').
        { intro HE'Bet.
          apply suma_sym.
          apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto; try solve [apply conga_line; auto].
          apply conga_sym.
          apply (conga_trans _ _ _ D0 E F).
          - apply (sams2_suma2__conga123 _ _ _ _ _ _ D E F A' B' C'); SumA.
            apply suma_sym.
            exists D0.
            split.
            apply conga_pseudo_refl; auto.
            split; auto.
            split; Cop.
            apply conga_line; Between.
          - apply (sams2_suma2__conga456 D E F _ _ _ _ _ _ D' E' F'); auto.
            exists D0.
            split.
            apply conga_pseudo_refl; auto.
            split; auto.
            split; Cop.
            apply conga_line; Between.
        }
        intro HE'out.
        apply not_bet_out in HE'out; auto.
        exfalso.
        apply HNColE.
        apply col_permutation_4.
        apply out_col.
        apply (out_lea__out _ _ _ D' E' F'); auto.
        apply (sams_suma__lea123789 _ _ _ G H I); auto.
      }
      intro HNColE'.
      assert(CongA D E F C B A0).
      { apply (sams2_suma2__conga456 A B C _ _ _ _ _ _ A' B' C'); auto.
        apply (sams_chara _ _ _ _ _ _ A0); try (apply lea_refl); Between.
        apply (conga3_suma__suma A B C C B A0 A B A0); try (apply conga_refl); try (apply conga_line); Between.
        exists A0.
        repeat (split; CongA); Cop.
      }
      assert(HJ : SAMS C B A0 G H I) by (apply (conga2_sams__sams D E F G H I); try (apply conga_refl); auto).
      destruct HJ as [_ [_ [J]]].
      destruct HisiEH as [_ [_ [F1]]].
      spliter.
      assert_diffs.
      assert(CongA C B J D' E' F').
      { apply (conga_trans _ _ _ D E F1); auto.
        - apply (l11_22 _ _ _ A0 _ _ _ F); auto.
          split.
            left; split; apply cop__not_one_side_two_sides; Cop; apply (ncol_conga_ncol G H I); CongA.
          split.
          { apply (sams2_suma2__conga456 A B C _ _ _ _ _ _ A' B' C'); auto.
            apply (sams_chara _ _ _ _ _ _ A0); try (apply lea_refl); Between.
            apply (conga3_suma__suma A B C C B A0 A B A0); try (apply conga_refl); try (apply conga_line); Between.
            exists A0.
            repeat (split; CongA); Cop.
          }
          apply (conga_trans _ _ _ G H I); auto.
          apply conga_sym; auto.

        - apply (suma2__conga D E F G H I); auto.
          exists F1.
          repeat (split; CongA).
      }
      apply (conga3_suma__suma A B C D' E' F' A B J); try (apply conga_refl); auto.
      { exists J.
        split.
        { apply (suma2__conga C B A0 G H I).
          exists J; repeat (split; CongA).
          apply (conga3_suma__suma D E F G H I D' E' F'); CongA.
        }
        split.
        { apply l9_9.
          apply invert_two_sides; apply l9_2.
          apply (l9_8_2 _ _ A0).
            repeat split; Col; exists B; split; Col; Between.
          apply cop__not_two_sides_one_side; Col.
          apply not_col_permutation_2.
          apply (ncol_conga_ncol D' E' F'); CongA.
        }
        split; CongA.
        apply coplanar_perm_12, coplanar_trans_1 with A0; Cop; Col.
      }
      apply (suma2__conga A' B' C' G H I); auto.
      apply (conga3_suma__suma A B A0 A0 B J A B J); try (apply conga_refl); auto; try (apply conga_line); Between.
      exists J.
      repeat (split; CongA); Cop.
      apply col123__nos; Col.
    }
    intro HB'out.
    apply not_bet_out in HB'out; auto.
    exfalso.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (sams_suma__lea123789 _ _ _ D E F); auto.
  }
  intro HNColB'.
  clear dependent A0.
  destruct HisiBE as [_ [_ [C1 HC1]]].
  spliter.
  assert_diffs.
  assert(CongA A' B' C' A B C1).
  { apply (suma2__conga A B C D E F); auto.
    apply (conga3_suma__suma A B C C B C1 A B C1); CongA.
    exists C1.
    repeat (split; CongA).
  }
  assert(OS B C1 C A).
  { apply one_side_symmetry.
    apply os_ts1324__os.
    - apply invert_one_side.
      apply cop__not_two_sides_one_side; Col.
      apply not_col_permutation_2; apply (ncol_conga_ncol A' B' C'); auto.
    - apply cop__not_one_side_two_sides; Col; Cop.
      apply (ncol_conga_ncol D E F); CongA.
  }
  elim(col_dec D' E' F').
  { intro HColE'.
    elim(bet_dec D' E' F').
    { intro HE'Bet.
      assert(HC0 : exists C0, Midpoint B C C0) by apply symmetric_point_construction.
      destruct HC0 as [C0].
      spliter.
      assert_diffs.
      assert(TS B C1 C C0).
      { repeat split; auto.
        apply (ncol_conga_ncol D E F); CongA.
        intro; apply HNColE; apply (col_conga_col C B C1); CongA; apply (l6_16_1 _ C0); Col.
        exists B.
        split; Col; Between.
      }
      apply (conga3_suma__suma A B C C B C0 A B C0); try (apply conga_refl); auto.
        exists C0; repeat (split; CongA); Cop; apply col124__nos; Col.
        apply conga_line; Between.
      apply (suma2__conga A' B' C' G H I); auto.
      apply (conga3_suma__suma A B C1 C1 B C0 A B C0).
      - exists C0; repeat (split; CongA).
          apply l9_9; apply (l9_8_2 _ _ C); auto.
        apply coplanar_perm_2, col_cop__cop with C; Col; Cop.
      - apply conga_sym; assumption.
      - apply (sams2_suma2__conga456 C B C1 _ _ _ _ _ _ C B C0); auto.
          apply (sams_chara _ _ _ _ _ _ C0); try (apply lea_refl); Between.
          apply (conga2_sams__sams D E F G H I); CongA.
          exists C0; repeat (split; CongA); Cop; apply l9_9; auto.
        apply (conga3_suma__suma D E F G H I D' E' F'); try (apply conga_refl); try (apply conga_sym); auto.
        apply conga_line; Between.
      - apply conga_refl; auto.
    }
    intro HE'out.
    apply not_bet_out in HE'out; auto.
    exfalso.
    apply HNColE.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (sams_suma__lea123789 _ _ _ G H I); auto.
  }
  intro HNColE'.
  clear dependent D0.
  assert(HJ : SAMS C B C1 G H I) by (apply (conga2_sams__sams D E F G H I); CongA).
  destruct HJ as [_ [_ [J]]].
  destruct HisiEH as [_ [_ [F1 HF1]]].
  spliter.
  assert_diffs.
  assert(CongA C B J D' E' F').
  { apply (conga_trans _ _ _ D E F1); auto.
    - apply (l11_22 _ _ _ C1 _ _ _ F); auto.
      split.
        left; split; apply cop__not_one_side_two_sides; Cop;
        [apply (ncol_conga_ncol D E F)|apply (ncol_conga_ncol G H I)..]; CongA.
      split.
      CongA.
      apply (conga_trans _ _ _ G H I); CongA.

    - apply (suma2__conga D E F G H I); auto.
      exists F1.
      repeat (split; CongA).
  }
  assert (~ Col C B C1) by (apply (ncol_conga_ncol D E F); CongA).
  apply (conga3_suma__suma A B C C B J A B J); try (apply conga_refl); auto.
  - exists J.
    repeat (split; CongA).
    { apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ C1).
      apply l9_2; apply cop__not_one_side_two_sides; Cop; apply (ncol_conga_ncol D E F); CongA.
      apply invert_one_side.
      apply cop__not_two_sides_one_side; Cop; Col.
      apply not_col_permutation_2, (ncol_conga_ncol D' E' F'); CongA.
    }
    apply coplanar_perm_12, coplanar_trans_1 with C1; Cop; Col.
  - apply (suma2__conga A' B' C' G H I); auto.
    apply (conga3_suma__suma A B C1 C1 B J A B J); CongA.
    exists J.
    repeat (split; CongA).
    { apply l9_9.
      apply (l9_8_2 _ _ C); auto.
      apply cop__not_one_side_two_sides; Cop.
      apply (ncol_conga_ncol G H I); CongA.
    }
    apply coplanar_perm_12, coplanar_trans_1 with C; Cop.
Qed.

Lemma suma_assoc_2 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   SumA A B C D' E' F' K L M -> SumA A' B' C' G H I K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  apply suma_sym.
  apply (suma_assoc_1 G H I D E F A B C K L M D' E' F'); SumA.
Qed.

(** Associativity of the sum of angles. *)

Lemma suma_assoc : forall A B C D E F G H I K L M A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   (SumA A' B' C' G H I K L M <-> SumA A B C D' E' F' K L M).
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  split.
    apply (suma_assoc_1 _ _ _ D E F); auto.
    apply (suma_assoc_2 _ _ _ D E F); auto.
Qed.

Lemma sams_assoc_1 : forall A B C D E F G H I A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   SAMS A' B' C' G H I -> SAMS A B C D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' Hsams1 Hsams2 Hs1 Hs2 Hsams1'.
  assert_diffs.
  elim(col_dec A B C).
  { intro HColB.
    destruct Hsams1 as [_ [[HEout|HBout]_]].
    - apply (conga2_sams__sams A' B' C' G H I); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.

    - apply not_bet_out in HBout; auto.
      apply sams_sym.
      repeat split; auto.
      exists F'.
      split.
      apply l11_21_b; try (apply out_trivial); auto.
      split.
        apply col124__nos; Col.
      split; Cop.
      apply not_two_sides_id.
  }
  intro HNColB.
  elim(col_dec D E F).
  { intro HColE.
    destruct Hsams2 as [_ [[HHout|HEout]_]].
    - apply (conga2_sams__sams A B C D E F); try (apply conga_refl); auto.
      apply (out546_suma__conga _ _ _ G H I); auto.

    - apply not_bet_out in HEout; auto.
      apply (conga2_sams__sams A' B' C' G H I); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.
  }
  intro HNColE.
  elim(col_dec G H I).
  { intro HColH.
    apply sams_sym in Hsams2.
    destruct Hsams2 as [_ [[HEout|HHout]_]].
    exfalso; assert_cols; Col.
    apply not_bet_out in HHout; auto.
    apply (conga2_sams__sams A B C D E F); try (apply conga_refl); auto.
    apply (out546_suma__conga _ _ _ G H I); auto.
  }
  intro HNColH.
  split; auto.
  split.
  right; intro; assert_cols; Col.
  assert(~ Col A' B' C').
  { intro.
    exfalso.
    destruct Hsams1' as [_ [[|HB'out]_]].
    assert_cols; Col.
    apply not_bet_out in HB'out; auto.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (sams_suma__lea123789 _ _ _ D E F); auto.
  }
  assert(HC1 : exists C1, CongA C B C1 D E F /\ ~ OS B C A C1 /\ ~ TS A B C C1 /\ Coplanar A B C C1).
    destruct Hsams1 as [_ []]; auto.
  destruct HC1 as [C1].
  spliter.
  assert_diffs.
  assert(CongA A B C1 A' B' C') by (apply (suma2__conga A B C D E F); auto; exists C1; repeat (split; CongA)).
  assert(HJ :exists J, CongA C1 B J G H I /\ ~ OS B C1 C J /\ ~ TS C B C1 J /\ Coplanar C B C1 J).
  { apply (conga2_sams__sams _ _ _ _ _ _ C B C1 G H I) in Hsams2; CongA.
    destruct Hsams2 as [_ [_ HJ]]; auto.
  }
  destruct HJ as [J [HJ1 [HJ2 [HJ3 HJ4]]]].
  spliter.
  apply (conga2_sams__sams _ _ _ _ _ _ A B C1 C1 B J) in Hsams1'; CongA.
  destruct Hsams1' as [_ [_ [J']]].
  spliter.
  assert_diffs.
  assert (~ Col A B C1) by (apply (ncol_conga_ncol A' B' C'); CongA).
  assert (~ Col C B C1) by (apply (ncol_conga_ncol D E F); CongA).
  assert (Coplanar C1 B A J) by (apply coplanar_trans_1 with C; Cop; Col).
  assert (HUn : Out B J' J \/ TS C1 B J' J).
    apply conga_cop__or_out_ts; auto.
    apply coplanar_trans_1 with A; Cop; Col.
  destruct HUn as [HJJ'|Hts].
  { exists J.
    split; [|repeat split].
    - apply (suma2__conga D E F G H I); auto.
      apply (conga3_suma__suma C B C1 C1 B J C B J); try (apply conga_refl); auto.
      exists J.
      repeat (split; CongA).

    - elim(col_dec C B J).
      intro; apply col124__nos; Col.
      intro.
      apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ C1).
        apply l9_2; apply cop__not_one_side_two_sides; Col; Cop.
      apply invert_one_side.
      apply cop__not_two_sides_one_side; Col; Cop.

    - elim(col_dec A B J).
        intro; intro Hts; destruct Hts; spliter; Col.
      intro.
      apply l9_9_bis.
      apply (one_side_transitivity _ _ _ C1).
        apply cop__not_two_sides_one_side; Col.
      apply (one_side_transitivity _ _ _ J');
      [|apply invert_one_side; apply out_one_side; Col].
      apply cop__not_two_sides_one_side; Col.
      apply not_col_permutation_2; apply (ncol_conga_ncol A B J); auto.
      apply out2__conga; try (apply out_trivial); auto.

    - apply coplanar_trans_1 with C1; Cop; Col.
  }
  exfalso.
  apply l9_2 in Hts.
  apply invert_two_sides in Hts.
  apply HJ2.
  exists J'.
  split; auto.
  apply (l9_8_2 _ _ A).
  - apply cop__not_one_side_two_sides; Cop.
    apply (ncol_conga_ncol G H I); auto.
    apply (conga_trans _ _ _ C1 B J); CongA.
  - apply os_ts1324__os.
    apply invert_one_side; apply cop__not_two_sides_one_side; Col.
    apply cop__not_one_side_two_sides; Col; Cop.
Qed.

Lemma sams_assoc_2 : forall A B C D E F G H I A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   SAMS A B C D' E' F' -> SAMS A' B' C' G H I.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply sams_sym.
  apply (sams_assoc_1 G H I D E F A B C D' E' F'); SumA.
Qed.

Lemma sams_assoc : forall A B C D E F G H I A' B' C' D' E' F',
   SAMS A B C D E F -> SAMS D E F G H I ->
   SumA A B C D E F A' B' C' -> SumA D E F G H I D' E' F' ->
   (SAMS A' B' C' G H I <-> SAMS A B C D' E' F').
Proof.
  intros A B C D E F.
  split.
  apply (sams_assoc_1 _ _ _ D E F); auto.
  apply (sams_assoc_2 _ _ _ D E F); auto.
Qed.

Lemma sams_nos__nts : forall A B C J, SAMS A B C C B J -> ~ OS B C A J ->
  ~ TS A B C J.
Proof.
  intros A B C J HIsi HNOS HTS.
  destruct HIsi as [_ [HUn [J' [HConga [HNOS' [HNTS HCop]]]]]].
  assert (Coplanar C B J J').
    apply coplanar_trans_1 with A; Cop.
    apply two_sides_not_col in HTS; Col.
  destruct (conga_cop__or_out_ts C B J J') as [HOut|HTS1]; CongA.
  - apply HNTS.
    apply l9_2, l9_8_2 with J; Side.
    apply invert_one_side, out_one_side; trivial.
    destruct HTS as [_ []]; Col.
  - destruct HTS as [HNCol1 [HNCol2 _]].
    assert_diffs.
    absurd (OS B C J J'); Side.
    destruct HTS1 as [HNCol _].
    assert (~ Col C B J') by (apply (ncol_conga_ncol C B J); Col; CongA).
    exists A; split; apply cop__not_one_side_two_sides; Col; Side.
      apply coplanar_trans_1 with J'; Col; Cop.
      Cop.
Qed.

Lemma conga_sams_nos__nts : forall A B C D E F J,
  SAMS A B C D E F -> CongA C B J D E F -> ~ OS B C A J -> ~ TS A B C J.
Proof.
  intros A B C D E F J HIsi HConga.
  apply sams_nos__nts.
  assert_diffs.
  apply (conga2_sams__sams A B C D E F); CongA.
Qed.


(** If B <= B', E <= E' and B + E = B' + E', then B = B' and E = E' *)

Lemma sams_lea2_suma2__conga123 : forall A B C D E F G H I A' B' C' D' E' F',
   LeA A B C A' B' C' -> LeA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G H I -> CongA A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' HleaB HleaE Hisi' Hsuma Hsuma'.
  assert_diffs.
  apply (sams2_suma2__conga123 _ _ _ _ _ _ D E F G H I); auto.
    apply (sams_lea2__sams _ _ _ _ _ _ A' B' C' D' E' F'); auto.
    apply (sams_lea2__sams _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  assert (Haux := ex_suma A' B' C' D E F).
  destruct Haux as [G' [H' [I']]]; auto.
  apply (conga3_suma__suma A' B' C' D E F G' H' I'); try (apply conga_refl); auto.
  apply lea_asym.
  apply (sams_lea456_suma2__lea A' B' C' D E F _ _ _ D' E' F'); auto.
  apply (sams_lea123_suma2__lea A B C D E F _ _ _ A' B' C'); auto.
  apply (sams_lea2__sams _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
Qed.

Lemma sams_lea2_suma2__conga456 : forall A B C D E F G H I A' B' C' D' E' F',
   LeA A B C A' B' C' -> LeA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G H I -> CongA D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply (sams_lea2_suma2__conga123 _ _ _ A B C G H I _ _ _ A' B' C'); SumA.
Qed.

(** If B + E = E, then B = 0 *)

Lemma sams_suma__out213 : forall A B C D E F, SumA A B C D E F D E F -> SAMS A B C D E F -> Out B A C.
Proof.
  intros A B C D E F HSuma HIsi.
  assert_diffs.
  apply (l11_21_a D E D).
    apply out_trivial; auto.
  apply sams_lea2_suma2__conga123 with D E F D E F D E F; Lea.
  exists F; repeat (split; CongA); Cop.
  apply col123__nos; Col.
Qed.

Lemma sams_suma__out546 : forall A B C D E F, SumA A B C D E F A B C -> SAMS A B C D E F -> Out E D F.
Proof.
  intros A B C D E F HSuma HIsi.
  apply sams_suma__out213 with A B C.
    apply suma_sym; trivial.
  apply sams_sym; trivial.
Qed.

(** If B < B' and E <= E', then B + E < B' + E' *)

Lemma sams_lea_lta123_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA A B C A' B' C' -> LeA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HltaB HleaE Hisi' Hsuma Hsuma'.
  assert_diffs.
  split.
  apply (sams_lea2_suma2__lea A B C D E F _ _ _ A' B' C' D' E' F'); Lea.
  intro.
  destruct HltaB as [HleaB HNConga].
  apply HNConga.
  apply (sams_lea2_suma2__conga123 _ _ _ D E F G H I _ _ _ D' E' F'); auto.
  apply (conga3_suma__suma A' B' C' D' E' F' G' H' I'); CongA.
Qed.

Lemma sams_lea_lta456_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA A B C A' B' C' -> LtA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta123_suma2__lta D E F A B C _ _ _ D' E' F' A' B' C'); SumA.
Qed.

Lemma sams_lta2_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA A B C A' B' C' -> LtA D E F D' E' F' -> SAMS A' B' C' D' E' F' ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta123_suma2__lta A B C D E F _ _ _ A' B' C' D' E' F'); auto.
  apply lta__lea; auto.
Qed.

(** If E >= E' and B + E <= B' + E', then B <= B' *)

Lemma sams_lea2_suma2__lea123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA D' E' F' D E F -> LeA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LeA A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lta_dec A' B' C' A B C).
  2: intro; apply nlta__lea; auto.
  intro Hlta.
  exfalso.
  assert(~ LeA G H I G' H' I'); auto.
  apply lta__nlea.
  apply(sams_lea_lta123_suma2__lta A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma sams_lea2_suma2__lea456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA A' B' C' A B C -> LeA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LeA D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea2_suma2__lea123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma_sym); auto.
  apply sams_sym; assumption.
Qed.

(** If E > E' and B + E <= B' + E', then B < B' *)

Lemma sams_lea_lta456_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA D' E' F' D E F -> LeA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lea_dec A' B' C' A B C).
  2: intro; apply nlea__lta; auto.
  intro Hlea.
  exfalso.
  assert(~ LeA G H I G' H' I'); auto.
  apply lta__nlea.
  apply(sams_lea_lta456_suma2__lta A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma sams_lea_lta123_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA A' B' C' A B C -> LeA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta456_suma2__lta123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma_sym); auto.
  apply sams_sym; assumption.
Qed.

(** If E >= E' and B + E < B' + E', then B < B' *)

Lemma sams_lea_lta789_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA D' E' F' D E F -> LtA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lea_dec A' B' C' A B C).
  2: intro; apply nlea__lta; auto.
  intro Hlta.
  exfalso.
  assert(~ LtA G H I G' H' I'); auto.
  apply lea__nlta.
  apply(sams_lea2_suma2__lea A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma sams_lea_lta789_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LeA A' B' C' A B C -> LtA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta789_suma2__lta123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma_sym); auto.
  apply sams_sym; assumption.
Qed.

Lemma sams_lta2_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA D' E' F' D E F -> LtA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta789_suma2__lta123 _ _ _ D E F G H I _ _ _ D' E' F' G' H' I'); auto.
  apply lta__lea; assumption.
Qed.

Lemma sams_lta2_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   LtA A' B' C' A B C -> LtA G H I G' H' I' -> SAMS A B C D E F ->
   SumA A B C D E F G H I -> SumA A' B' C' D' E' F' G' H' I' -> LtA D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (sams_lea_lta789_suma2__lta456 A B C _ _ _ G H I A' B' C' _ _ _ G' H' I'); auto.
  apply lta__lea; assumption.
Qed.

(** The sum of two angles of a triangle is less than a straight angle (three lemmas) *)

Lemma sams123231 : forall A B C, A <> B -> A <> C -> B <> C -> SAMS A B C B C A.
Proof.
  intros A B C.
  intros.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  apply (sams_chara _ _ _ _ _ _ A'); Between.
  elim(col_dec A B C).
  { intro HCol.
    elim(bet_dec A C B).
    { intro HCBet.
      apply conga__lea.
      apply conga_line; Between.
      apply (between_exchange3 A); Between.
    }
    intro.
    apply l11_31_1; auto.
    apply l6_6.
    apply not_bet_out; Col.
  }
  intro.
  apply lta__lea.
  apply l11_41_aux; Col; Between.
Qed.

Lemma col_suma__col : forall A B C D E F, Col D E F -> SumA A B C B C A D E F -> Col A B C.
Proof.
  intros A B C D E F HCol HSuma.
  destruct (col_dec A B C) as [|HNCol]; [trivial|].
  exfalso.
  destruct (bet_dec D E F).
  - assert (HP := symmetric_point_construction A B).
    destruct HP as [P].
    assert_diffs.
    assert (Hlta : LtA D E F A B P);
    [|destruct Hlta as [Hlea HNConga]; apply HNConga; apply conga_line; Between].
    assert (TS B C A P).
    { repeat split; Col.
      intro; apply HNCol; ColR.
      exists B; Col; Between.
    }
    apply (sams_lea_lta456_suma2__lta A B C B C A _ _ _ A B C C B P); Lea.
      apply l11_41_aux; Col; Between.
    { split; auto; split.
        right; intro; apply HNCol; Col.
      exists P.
      split; CongA.
      split; Side.
      split; Cop.
      intro Hts.
      destruct Hts as [_ [Habs]].
      apply Habs; Col.
    }
    exists P; repeat (split; CongA); Side; Cop.

  - assert_diffs.
    apply HNCol.
    apply col_permutation_3.
    apply out_col.
    apply (out_lea__out _ _ _ D E F).
      apply not_bet_out; Col.
    apply (sams_suma__lea456789 A B C); auto.
    apply sams123231; auto.
Qed.

Lemma ncol_suma__ncol : forall A B C D E F, ~ Col A B C -> SumA A B C B C A D E F -> ~ Col D E F.
Proof.
  intros A B C D E F HNCol HSuma HCol.
  apply HNCol, col_suma__col with D E F; assumption.
Qed.


(** Sum of two right angles is a straight angle:
  90+90=180.
 *)

Lemma per2_suma__bet : forall A B C D E F G H I, Per A B C -> Per D E F ->
   SumA A B C D E F G H I -> Bet G H I.
Proof.
  intros A B C D E F G H I HB HE HSuma.
  destruct HSuma as [A1 [HConga1 [HNos [HCop HConga2]]]].
  assert_diffs.
  assert(Per A1 B C) by (apply (l11_17 D E F); CongA).
  apply (bet_conga__bet A B A1); auto.
  apply (col_two_sides_bet _ C).
  apply col_permutation_2; apply cop_per2__col with C; Cop.
  apply cop__not_one_side_two_sides; Cop; apply per_not_col; auto.
Qed.

Lemma bet_per2__suma : forall A B C D E F G H I,
   A <> B -> B <> C -> D <> E -> E <> F -> G <> H -> H <> I ->
   Per A B C -> Per D E F ->
   Bet G H I -> SumA A B C D E F G H I.
Proof.
  intros A B C D E F G H I H1 H2 H3 H4 H5 H6 HB HE HBet.
  destruct (ex_suma A B C D E F) as [G' [H' [I' HSuma]]]; auto.
  apply conga3_suma__suma with A B C D E F G' H' I'; [|apply conga_refl..|]; auto.
  assert_diffs.
  apply conga_line; auto.
  apply (per2_suma__bet A B C D E F); assumption.
Qed.

Lemma per2__sams : forall A B C D E F, A <> B -> B <> C -> D <> E -> E <> F ->
  Per A B C -> Per D E F -> SAMS A B C D E F.
Proof.
  intros A B C D E F HAB HBC HDE HEF HPerB HPerE.
  destruct (ex_suma A B C D E F) as [G [H [I]]]; auto.
  apply bet_suma__sams with G H I; [|apply (per2_suma__bet A B C D E F)]; assumption.
Qed.

(** If 90+x=180 then x=90. *)

Lemma bet_per_suma__per456 : forall A B C D E F G H I, Per A B C -> Bet G H I ->
   SumA A B C D E F G H I -> Per D E F.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  assert(HA1 := symmetric_point_construction A B).
  destruct HA1 as [A1].
  assert_diffs.
  assert(~ Col A B C) by (apply per_not_col; auto).
  apply (l11_17 A B C); auto.
  apply (sams2_suma2__conga456 A B C _ _ _ _ _ _ G H I); auto.
  - apply (sams_chara _ _ _ _ _ _ A1); Between.
    apply conga__lea.
    apply conga_left_comm.
    apply l11_18_1; Between; Perp.

  - destruct HSuma as [F1 [HConga1 [HNos [HCop HConga2]]]].
    repeat split; auto.
    right; intro; assert_cols; Col.
    exists F1.
    repeat (split; auto).
    intro Habs.
    destruct Habs as [_ [Habs]].
    apply Habs.
    apply col_permutation_2.
    apply bet_col.
    apply (bet_conga__bet G H I); CongA.

  - assert(HSuma' := ex_suma A B C A B C).
    destruct HSuma' as [G' [H' [I']]]; auto.
    assert_diffs.
    apply (conga3_suma__suma A B C A B C G' H' I'); try (apply conga_refl); auto.
    apply conga_line; auto.
    apply (per2_suma__bet A B C A B C); auto.
Qed.

(** If x+90=180 then x=90. *)

Lemma bet_per_suma__per123 : forall A B C D E F G H I, Per D E F -> Bet G H I ->
   SumA A B C D E F G H I -> Per A B C.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  apply (bet_per_suma__per456 D E F _ _ _ G H I); SumA.
Qed.

(** If x+x=180 then x=90. *)

Lemma bet_suma__per : forall A B C D E F, Bet D E F -> SumA A B C A B C D E F ->
   Per A B C.
Proof.
  intros A B C D E F HBet HSuma.
  assert_diffs.
  destruct HSuma as [A' [HConga1 [_ [_ HConga2]]]].
  apply l8_2.
  apply (l11_18_2 _ _ _ A'); CongA.
  apply (bet_conga__bet D E F); CongA.
Qed.

(** If x<90 then x+x<180 (two lemmas). *)

Lemma acute__sams : forall A B C, Acute A B C -> SAMS A B C A B C.
Proof.
  intros A B C Hacute.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  apply (sams_chara _ _ _ _ _ _ A'); Between.
  apply acute_obtuse__lta; auto.
  apply obtuse_sym.
  apply (acute_bet__obtuse A); Between.
Qed.

Lemma acute_suma__nbet : forall A B C D E F, Acute A B C -> SumA A B C A B C D E F -> ~ Bet D E F.
Proof.
  intros A B C D E F Hacute HSuma.
  assert_diffs.
  intro.
  apply (nlta A B C).
  apply acute_per__lta; auto.
  apply (bet_suma__per _ _ _ D E F); auto.
Qed.

(** If x<90 and y<90 then x+y<180 (two lemmas). *)

Lemma acute2__sams : forall A B C D E F, Acute A B C -> Acute D E F -> SAMS A B C D E F.
Proof.
  assert (Haux : forall A B C D E F, Acute A B C -> LeA D E F A B C -> SAMS A B C D E F).
  { intros A B C D E F HAcute HLea.
    apply sams_lea2__sams with A B C A B C.
      apply acute__sams, HAcute.
      assert_diffs; apply lea_refl; auto.
      assumption.
  }
  intros A B C D E F HAcute1 HAcute2.
  assert_diffs.
  destruct (lea_total A B C D E F); SumA.
Qed.

Lemma acute2_suma__nbet : forall A B C D E F G H I,
  Acute A B C -> Acute D E F -> SumA A B C D E F G H I -> ~ Bet G H I.
Proof.
  assert (Haux : forall A B C D E F G H I, Acute A B C -> LeA D E F A B C -> SumA A B C D E F G H I ->
    ~ Bet G H I).
  { intros A B C D E F G H I HAcute HLea HSuma HBet.
    assert_diffs.
    destruct (ex_suma A B C A B C) as [A' [B' [C']]]; auto.
    apply (acute_suma__nbet A B C A' B' C'); trivial.
    apply (bet_lea__bet G H I); [apply HBet|].
    apply sams_lea2_suma2__lea with A B C D E F A B C A B C; trivial.
      apply lea_refl; auto.
      apply acute__sams, HAcute.
  }
  intros A B C D E F G H I HAcute1 HAcute2 HSuma.
  assert_diffs.
  destruct (lea_total A B C D E F); auto.
    apply suma_sym in HSuma; apply (Haux D E F A B C); assumption.
    apply (Haux A B C D E F); assumption.
Qed.

(** If x<90 then x+90<180 (two lemmas) *)

Lemma acute_per__sams : forall A B C D E F, A <> B -> B <> C ->
  Per A B C -> Acute D E F -> SAMS A B C D E F.
Proof.
  intros A B C D E F HAB HBC HPer HAcute.
  apply sams_lea2__sams with A B C A B C.
    apply per2__sams; auto.
    apply lea_refl; auto.
    apply acute_per__lta; auto.
Qed.

Lemma acute_per_suma__nbet : forall A B C D E F G H I, A <> B -> B <> C ->
  Per A B C -> Acute D E F -> SumA A B C D E F G H I -> ~ Bet G H I.
Proof.
  intros A B C D E F G H I HAB HBC HPer HAcute HSuma HBet.
  assert_diffs.
  apply (nlta G H I).
  apply sams_lea_lta456_suma2__lta with A B C D E F A B C A B C; Lea.
    apply per2__sams; auto.
    apply bet_per2__suma; auto.
Qed.

(** If x>90 then x+x>180. *)

Lemma obtuse__nsams : forall A B C, Obtuse A B C -> ~ SAMS A B C A B C.
Proof.
  intros A B C Hobtuse.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  intro.
  apply (nlta A B C).
  apply (lea123456_lta__lta _ _ _ A' B C).
  - apply lea_right_comm.
    apply (sams_chara A); Between.
  - apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); Between.
Qed.

(** If x+x<180 then x<90. *)

Lemma nbet_sams_suma__acute : forall A B C D E F, ~ Bet D E F -> SAMS A B C A B C ->
   SumA A B C A B C D E F -> Acute A B C.
Proof.
  intros A B C D E F HNBet HIsi HSuma.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro HUn.
  exfalso.
  destruct HUn.
  - apply HNBet.
    apply (per2_suma__bet A B C A B C); auto.
  - assert(~ SAMS A B C A B C); auto.
    apply obtuse__nsams; auto.
Qed.

(** If x+x>180 then x>90. *)

Lemma nsams__obtuse : forall A B C, A <> B -> B <> C -> ~ SAMS A B C A B C -> Obtuse A B C.
Proof.
  intros A B C HAB HBC HNIsi.
  elim(angle_partition A B C); auto.
  - intro.
    exfalso.
    apply HNIsi.
    apply acute__sams; auto.

  - intro HUn.
    destruct HUn; auto.
    exfalso.
    apply HNIsi.
    assert(HA' := symmetric_point_construction A B).
    assert(HNCol : ~ Col A B C) by (apply per_not_col; auto).
    destruct HA' as [A'].
    assert_diffs.
    repeat split; auto.
    right; intro; Col.
    exists A'.
    split.
      apply conga_right_comm; apply conga_sym; apply l11_18_1; Between; Perp.
    split.
    { apply l9_9.
      repeat split; Col.
        intro; apply HNCol; ColR.
      exists B; Col; Between.
    }
    split; Cop.
    intro Hts; destruct Hts as [_ []]; assert_cols; Col.
Qed.

(** If doubling two acute angles makes the same result, then these angles are congruent *)

Lemma sams2_suma2__conga : forall A B C D E F A' B' C',
  SAMS A B C A B C -> SumA A B C A B C D E F ->
  SAMS A' B' C' A' B' C' -> SumA A' B' C' A' B' C' D E F ->
  CongA A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HIsi HSuma HIsi' HSuma'.
  assert_diffs.
  destruct (lea_total A B C A' B' C'); trivial; [|apply conga_sym];
  eapply sams_lea2_suma2__conga123; eauto.
Qed.

Lemma acute2_suma2__conga : forall A B C D E F A' B' C',
  Acute A B C -> SumA A B C A B C D E F ->
  Acute A' B' C' -> SumA A' B' C' A' B' C' D E F ->
  CongA A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HB HSuma HB'.
  apply sams2_suma2__conga; try apply acute__sams; assumption.
Qed.

(** Sum of two straight angles is a null angle *)

Lemma bet2_suma__out : forall A B C D E F G H I, Bet A B C -> Bet D E F ->
  SumA A B C D E F G H I -> Out H G I.
Proof.
  intros A B C D E F G H I HBet1 HBet2 HSuma.
  assert_diffs.
  apply (eq_conga_out A B).
  apply (suma2__conga A B C D E F); trivial.
  exists A; split.
    apply conga_line; Between.
  split.
    apply col123__nos; Col.
  split; CongA; Cop.
Qed.

(** Sum of two degenerate angles is degenerate *)

Lemma col2_suma__col : forall A B C D E F G H I, Col A B C -> Col D E F ->
  SumA A B C D E F G H I -> Col G H I.
Proof.
  intros A B C D E F G H I HCol1 HCol2 HSuma.
  destruct (bet_dec A B C).
  destruct (bet_dec D E F).
  - apply col_permutation_4, out_col, (bet2_suma__out A B C D E F); assumption.
  - apply (col_conga_col A B C); trivial.
    apply out546_suma__conga with D E F; trivial.
    apply not_bet_out; assumption.
  - apply (col_conga_col D E F); trivial.
    apply (out213_suma__conga A B C); trivial.
    apply not_bet_out; assumption.
Qed.

(** The sum of two supplementary angles is a flat angle (two lemmas) *)

Lemma suma_suppa__bet : forall A B C D E F G H I,
  SuppA A B C D E F -> SumA A B C D E F G H I -> Bet G H I.
Proof.
  intros A B C D E F G H I [_ [A' [HBet HCong]]] [A'' [HConga1 [HNOS [HCop HConga2]]]].
  apply (bet_conga__bet A B A''); trivial.
  assert_diffs.
  apply between_symmetry, l6_2 with A'; Between.
  destruct (conga_cop__or_out_ts C B A' A'') as [|HTS]; auto.
    apply coplanar_perm_3, col_cop__cop with A; Col; Cop.
    apply conga_trans with D E F; CongA.
  exfalso.
  apply HNOS.
  exists A'; split; [|Side].
  destruct HTS as [HNCol1 [HNCol2 _]].
  repeat split.
    intro; apply HNCol1; ColR.
    Col.
  exists B; split; Col.
Qed.

Lemma bet_suppa__suma : forall A B C D E F G H I, G <> H -> H <> I ->
  SuppA A B C D E F -> Bet G H I -> SumA A B C D E F G H I.
Proof.
  intros A B C D E F G H I; intros.
  assert_diffs.
  destruct (ex_suma A B C D E F) as [G' [H' [I']]]; auto.
  apply (conga3_suma__suma A B C D E F G' H' I'); try apply conga_refl; auto.
  assert_diffs.
  apply conga_line; auto.
  apply (suma_suppa__bet A B C D E F); assumption.
Qed.

(** If the sum of two angles is a flat angle, then they are supplementary *)

Lemma bet_suma__suppa : forall A B C D E F G H I,
  SumA A B C D E F G H I -> Bet G H I -> SuppA A B C D E F.
Proof.
  intros A B C D E F G H I [A' [HConga1 [_ [_ HConga2]]]] HBet.
  assert_diffs.
  split; auto.
  exists A'.
  split; CongA.
  apply (bet_conga__bet G H I); CongA.
Qed.

(** The sum of two angles is equal to the sum of their two supplementary angles *)

Lemma bet2_suma__suma : forall A B C D E F G H I A' D', A' <> B -> D' <> E ->
  Bet A B A' -> Bet D E D' -> SumA A B C D E F G H I -> SumA A' B C D' E F G H I.
Proof.
  intros A B C D E F G H I A' D' HBA' HED' HBetA HBetD [J [HJ1 [HJ2 [HJ3 HJ4]]]]; spliter.
  destruct (segment_construction C B B C) as [C' []].
  assert_diffs.
  apply (conga3_suma__suma A B C' D' E F G H I); [|apply l11_14; Between|CongA..].
  exists J.
  split.
    apply l11_13 with C D; Between.
  repeat (split; trivial).
    intro; apply HJ2, col_one_side with C'; Col.
  apply coplanar_perm_3, col_cop__cop with C; Col; Cop.
Qed.

Lemma suma_suppa2__suma : forall A B C D E F G H I A' B' C' D' E' F',
  SuppA A B C A' B' C' -> SuppA D E F D' E' F' -> SumA A B C D E F G H I ->
  SumA A' B' C' D' E' F' G H I.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' [_ [A0 []]] [_ [D0 []]] HSuma.
  assert_diffs.
  apply (conga3_suma__suma A0 B C D0 E F G H I); CongA.
  apply bet2_suma__suma with A D; auto.
Qed.

(** If doubling two obtuse angles makes the same result, then these angles are congruent *)

Lemma suma2_obtuse2__conga : forall A B C D E F A' B' C',
  Obtuse A B C -> SumA A B C A B C D E F ->
  Obtuse A' B' C' -> SumA A' B' C' A' B' C' D E F ->
  CongA A B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' HB HSuma HB' HSuma'.
  destruct (segment_construction A B A B) as [A0 []].
  destruct (segment_construction A' B' A' B') as [A0' []].
  assert_diffs.
  apply l11_13 with A0 A0'; Between.
  apply acute2_suma2__conga with D E F.
    apply (bet_obtuse__acute A); auto.
    apply bet2_suma__suma with A A; auto.
    apply (bet_obtuse__acute A'); auto.
    apply bet2_suma__suma with A' A'; auto.
Qed.

(** If doubling two angles makes the same result, then they are either congruent or supplementary *)

Lemma bet_suma2__or_conga : forall A B C D E F A' B' C' A0, A0 <> B ->
  Bet A B A0 -> SumA A B C A B C D E F -> SumA A' B' C' A' B' C' D E F ->
  CongA A B C A' B' C' \/ CongA A0 B C A' B' C'.
Proof.
  intros A B C D E F A' B' C' A0 HBA0 HBet HSuma.
  revert A' B' C'.
  assert (Haux : forall A' B' C', Acute A' B' C' -> SumA A' B' C' A' B' C' D E F ->
    CongA A B C A' B' C' \/ CongA A0 B C A' B' C').
  { intros A' B' C' HAcute' HSuma'.
    assert_diffs.
    destruct (angle_partition A B C) as [HAcute|[HPer|HObtuse]]; auto.
    - left; apply acute2_suma2__conga with D E F; auto.
    - exfalso.
      apply (acute_suma__nbet A' B' C' D E F); [..|apply (per2_suma__bet A B C A B C)]; assumption.
    - right; apply acute2_suma2__conga with D E F; auto.
        apply (bet_obtuse__acute A); auto.
        apply bet2_suma__suma with A A; auto.
  }
  intros A' B' C' HSuma'.
  assert_diffs.
  destruct (angle_partition A' B' C') as [HAcute|[HPer|HObtuse]]; auto.
  - left.
    apply l11_16; auto.
    apply bet_suma__per with D E F; [apply (per2_suma__bet A' B' C' A' B' C')|]; assumption.
  - destruct (segment_construction A' B' A' B') as [A0' []].
    assert_diffs.
    destruct (Haux A0' B' C').
      apply (bet_obtuse__acute A'); auto.
      apply bet2_suma__suma with A' A'; auto.
      right; apply l11_13 with A A0'; Between.
      left; apply l11_13 with A0 A0'; Between.
Qed.

Lemma suma2__or_conga_suppa : forall A B C A' B' C' D E F ,
  SumA A B C A B C D E F -> SumA A' B' C' A' B' C' D E F ->
  CongA A B C A' B' C' \/ SuppA A B C A' B' C'.
Proof.
  intros A B C A' B' C' D E F HSuma HSuma'.
  destruct (segment_construction A B A B) as [A0 []].
  assert_diffs.
  destruct (bet_suma2__or_conga A B C D E F A' B' C' A0); auto.
  right.
  split; auto.
  exists A0; split; CongA.
Qed.


(** Basic properties about the sum of the angles of a triangle *)

Lemma ex_trisuma : forall A B C, A <> B -> B <> C -> A <> C ->
  exists D E F, TriSumA A B C D E F.
Proof.
  intros A B C HAB HBC HAC.
  destruct (ex_suma A B C B C A) as [G [H [I HSuma1]]]; auto.
  assert_diffs.
  destruct (ex_suma G H I C A B) as [D [E [F HSuma2]]]; auto.
  exists D; exists E; exists F; exists G; exists H; exists I.
  split; assumption.
Qed.

Lemma trisuma_perm_231 : forall A B C D E F, TriSumA A B C D E F -> TriSumA B C A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  assert_diffs.
  assert(Hex:= ex_suma B C A C A B).
  destruct Hex as [B2 [C2 [A2 Hex]]]; auto.
  exists B2.
  exists C2.
  exists A2.
  split; auto.
  apply suma_sym.
  apply (suma_assoc A B C B C A C A B D E F A1 B1 C1 B2 C2 A2); try (apply sams123231); auto.
Qed.

Lemma trisuma_perm_312 : forall A B C D E F, TriSumA A B C D E F -> TriSumA C A B D E F.
Proof.
  intros.
  do 2 apply trisuma_perm_231.
  assumption.
Qed.

Lemma trisuma_perm_321 : forall A B C D E F, TriSumA A B C D E F -> TriSumA C B A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  apply suma_sym in HT2.
  assert_diffs.
  assert(Hex:= ex_suma C A B A B C).
  destruct Hex as [C2 [A2 [B2 Hex]]]; auto.
  exists C2.
  exists A2.
  exists B2.
  split.
  SumA.
  apply suma_middle_comm.
  apply (suma_assoc C A B A B C B C A D E F C2 A2 B2 A1 B1 C1); try (apply sams123231); auto.
Qed.

Lemma trisuma_perm_213 : forall A B C D E F, TriSumA A B C D E F -> TriSumA B A C D E F.
Proof.
  intros.
  apply trisuma_perm_321.
  apply trisuma_perm_312.
  assumption.
Qed.

Lemma trisuma_perm_132 : forall A B C D E F, TriSumA A B C D E F -> TriSumA A C B D E F.
Proof.
  intros.
  apply trisuma_perm_321.
  apply trisuma_perm_231.
  assumption.
Qed.

Lemma conga_trisuma__trisuma : forall A B C D E F D' E' F',
  TriSumA A B C D E F -> CongA D E F D' E' F' -> TriSumA A B C D' E' F'.
Proof.
  intros A B C D E F D' E' F' HTri HConga.
  destruct HTri as [G [H [I [HSuma1 HSuma2]]]].
  exists G; exists H; exists I; split; trivial.
  assert_diffs; apply (conga3_suma__suma G H I C A B D E F); CongA.
Qed.

Lemma trisuma2__conga : forall A B C D E F D' E' F',
  TriSumA A B C D E F -> TriSumA A B C D' E' F' -> CongA D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' HTri HTri'.
  destruct HTri as [G [H [I [HSuma1 HSuma2]]]].
  destruct HTri' as [G' [H' [I' [HSuma1' HSuma2']]]].
  apply (suma2__conga G H I C A B); trivial.
  assert_diffs.
  apply (conga3_suma__suma G' H' I' C A B D' E' F'); CongA.
  apply (suma2__conga A B C B C A); trivial.
Qed.

Lemma conga3_trisuma__trisuma : forall A B C D E F A' B' C', TriSumA A B C D E F ->
  CongA A B C A' B' C' -> CongA B C A B' C' A' -> CongA C A B C' A' B' ->
  TriSumA A' B' C' D E F.
Proof.
  intros A B C D E F A' B' C' HTri HCongaB HCongaC HCongaA.
  destruct HTri as [G [H [I [HSuma HSuma']]]].
  assert_diffs; exists G; exists H; exists I; split;
  [apply (conga3_suma__suma A B C B C A G H I)|apply (conga3_suma__suma G H I C A B D E F)]; CongA.
Qed.

(** The sum of the angles of a degenerate triangle is a straight angle *)

Lemma col_trisuma__bet : forall A B C P Q R, Col A B C -> TriSumA A B C P Q R -> Bet P Q R.
Proof.
  intros A B C P Q R HCol HTri.
  destruct HTri as [D [E [F []]]].
  assert_diffs.
  destruct HCol as [|[|]].
  - apply (bet_conga__bet A B C); auto.
    apply (conga_trans _ _ _ D E F).
    apply (out546_suma__conga _ _ _ B C A); try (apply bet_out); Between.
    apply (out546_suma__conga _ _ _ C A B); try (apply l6_6; apply bet_out); auto.
  - apply (bet_conga__bet B C A); auto.
    apply (conga_trans _ _ _ D E F).
    apply (out213_suma__conga A B C); try (apply l6_6; apply bet_out); auto.
    apply (out546_suma__conga _ _ _ C A B); try (apply bet_out); Between.
  - apply (bet_conga__bet C A B); auto.
    apply (out213_suma__conga D E F); auto.
    apply (l11_21_a B C A); try (apply l6_6; apply bet_out); auto.
    apply (out213_suma__conga A B C); try (apply bet_out); Between.
Qed.

(** Decidability properties *)

Lemma suma_dec : forall A B C D E F G H I, SumA A B C D E F G H I \/ ~ SumA A B C D E F G H I.
Proof.
  intros A B C D E F G H I.
  destruct(eq_dec_points A B).
    subst; right; intro; assert_diffs; auto.
  destruct(eq_dec_points C B).
    subst; right; intro; assert_diffs; auto.
  destruct(eq_dec_points D E).
    subst; right; intro; assert_diffs; auto.
  destruct(eq_dec_points F E).
    subst; right; intro; assert_diffs; auto.
  destruct (ex_suma A B C D E F) as [G' [H' [I']]]; auto.
  destruct(conga_dec G H I G' H' I') as [|HNCongA].
    left; apply (conga3_suma__suma A B C D E F G' H' I'); CongA.
  right.
  intro.
  apply HNCongA, (suma2__conga A B C D E F); auto.
Qed.

Lemma sams_dec : forall A B C D E F, SAMS A B C D E F \/ ~ SAMS A B C D E F.
Proof.
  intros A B C D E F.
  destruct(eq_dec_points A B).
    subst; right; intro; assert_diffs; auto.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  destruct(lea_dec D E F C B A') as [|HNlea].
    left; apply (sams_chara _ _ _ _ _ _ A'); Between.
  right.
  intro.
  apply HNlea, (sams_chara A); Between.
Qed.

Lemma trisuma_dec : forall A B C P Q R, TriSumA A B C P Q R \/ ~ TriSumA A B C P Q R.
Proof.
  intros A B C P Q R.
  destruct(eq_dec_points A B).
    subst; right; intros [D [E [F []]]]; assert_diffs; auto.
  destruct(eq_dec_points B C).
    subst; right; intros [D [E [F []]]]; assert_diffs; auto.
  destruct(eq_dec_points A C).
    subst; right; intros [D [E [F []]]]; assert_diffs; auto.
  destruct (ex_trisuma A B C) as [D [E [F]]]; auto.
  destruct (conga_dec D E F P Q R) as [|HNCong].
    left; apply conga_trisuma__trisuma with D E F; assumption.
    right; intro; apply HNCong, (trisuma2__conga A B C); assumption.
Qed.

End Suma_2.

Hint Resolve per2__sams acute2__sams acute_per__sams sams123231 bet_suppa__suma : suma.
