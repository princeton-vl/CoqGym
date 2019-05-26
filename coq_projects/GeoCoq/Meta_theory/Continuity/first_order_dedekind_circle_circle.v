Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.circles.

Section Dedekind_circle_circle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** This proof is inspired by Franz Rothe's proof of Theorem 8.5 in Several topics from geometry *)

Lemma circle_circle_aux : (forall A B C D P Q,
  OnCircle P C D -> OnCircle Q C D -> InCircleS P A B -> OutCircleS Q A B ->
  OS A C P Q \/ (Col P A C /\ ~ Col Q A C) \/ (~ Col P A C /\ Col Q A C ) ->
  exists Z : Tpoint, OnCircle Z A B /\ OnCircle Z C D) ->
  circle_circle.
Proof.
  intro Haux.
  cut (forall A B C D P Q,
  OnCircle P C D -> OnCircle Q C D -> InCircleS P A B -> OutCircleS Q A B ->
  Coplanar A C P Q -> (~ Col P A C \/ ~ Col Q A C) ->
  exists Z : Tpoint, OnCircle Z A B /\ OnCircle Z C D).
  - intros Haux' A B C D P Q HPOn HQOn HPIn HQOut.
    assert (HQ' : exists Q', OnCircle Q' C D /\ OutCircle Q' A B /\ Col Q' A C).
    { destruct (segment_construction A C C D) as [Q' []].
      exists Q'.
      repeat split; Col.
      apply le_transitivity with A Q; trivial.
      apply triangle_inequality with C; trivial.
      apply cong_transitivity with C D; Cong.
    }
    clear dependent Q.
    destruct HQ' as [Q [HQOn [HQOut HCol]]].
    destruct (cong_dec A P A B).
      exists P; split; trivial.
    destruct (cong_dec A B A Q).
      exists Q; Circle.
    assert (HPInS : InCircleS P A B) by (split; trivial).
    assert (HQOutS : OutCircleS Q A B) by (split; trivial).
    assert (A <> C).
    { intro; subst C.
      apply (not_and_lt A B A P); split; trivial.
      apply (cong2_lt__lt A B A Q); Cong.
      apply cong_transitivity with A D; Cong.
    }
    assert (C <> D).
      intro; treat_equalities; apply (not_and_lt A C A B); split; trivial.
    destruct (col_dec P A C); [|apply Haux' with P Q; Cop].
    destruct (exists_cong_per A C C D) as [R [HR1 HR2]].
    assert_diffs.
    apply per_not_col in HR1; auto.
    destruct (circle_cases A B R) as [HOn|HNOn].
      exists R; split; trivial.
    destruct HNOn; [apply Haux' with R Q|apply Haux' with P R]; Col; Cop.

  - intros A B C D P Q HPOn HQOn HPIn HQOut HCop HDij.
    destruct (col_dec P A C) as [HCol|HNCol].
    { destruct HDij.
        contradiction.
      apply Haux with P Q; auto.
    }
    destruct (col_dec Q A C).
      apply Haux with P Q; auto.
    destruct (cop__one_or_two_sides A C P Q); trivial; [|apply Haux with P Q; auto].
    destruct (l10_2_existence A C P) as [P' HP'].
    assert_diffs.
    apply Haux with P' Q; trivial.
      apply cong_transitivity with C P; trivial.
      apply cong_commutativity, (is_image_col_cong A C); Col.
      apply cong2_lt__lt with A P A B; Cong.
      apply cong_symmetry, cong_commutativity, (is_image_col_cong A C); Col.
    left.
    exists P; split; Side.
    apply l10_14; auto.
    intro; subst; apply HNCol, l10_8, HP'.
Qed.

Lemma fod__circle_circle : first_order_dedekind -> circle_circle.
Proof.
  intro dedekind.
  apply circle_circle_aux.
  intros A B C D P Q HPOn HQOn HPIn HQOut HDij.
  assert (A <> C).
  { intro; subst C.
    apply (not_and_lt A B A P); split; trivial.
    apply (cong2_lt__lt A B A Q); Cong.
    apply cong_transitivity with A D; Cong.
  }
  assert (P <> Q) by (intro; apply (not_and_lt A P A B); subst; split; trivial).
  assert (C <> D) by (intro; treat_equalities; auto).
  assert (HOS : forall X Y, Bet P X Q -> Bet P Y Q -> X <> P -> X <> Q -> Y <> P -> Y <> Q -> OS A C X Y).
  { intros X Y; intros.
    destruct HDij as [HOS|[[HP HQ]|[HQ HP]]].
    - apply one_side_transitivity with P; [apply one_side_symmetry|]; apply l9_17 with Q; trivial.
    - apply one_side_transitivity with Q; [apply one_side_symmetry|];
      apply out_one_side_1 with P; Col; apply l6_6, bet_out; auto.
    - apply one_side_transitivity with P; [apply one_side_symmetry|];
      apply out_one_side_1 with Q; Col; apply l6_6, bet_out; Between.
  }
  assert (HNTS : forall X Y, Bet P Y Q -> Bet P X Y -> ~ TS A C X Y).
  { intros X Y HX HY HTS.
    absurd (TS A C P Q).
    - destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]]; [apply l9_9_bis; trivial|intro..].
        apply (two_sides_not_col A C P Q); Col.
        apply (two_sides_not_col A C Q P); Col; Side.
    - destruct (eq_dec_points P X); destruct (eq_dec_points Q Y); treat_equalities; trivial.
        apply bet_ts__ts with Y; trivial.
        apply l9_2, bet_ts__ts with X; Side; Between.
        apply bet_ts__ts with Y; trivial; apply l9_2, bet_ts__ts with X; Side; Between.
  }
  assert (HLta : LtA A C P A C Q).
  { apply t18_19; Cong.
      intro; treat_equalities; auto.
      apply cong_transitivity with C D; Cong.
      apply lt_comm, lt_transitivity with A B; trivial.
  }
  assert (HNCol1 : ~ Col P Q C).
  { intro.
    destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]];
      [|apply HNCol; assert_diffs; ColR..].
    destruct HLta as [_ HNCongA].
    apply HNCongA, out2__conga.
      apply out_trivial; auto.
    apply col_one_side_out with A; Col; Side.
  }

  assert (Haux : forall X Y X0 Y0, Bet P Y Q -> X <> Y ->
    OnCircle X0 C D -> Out C X X0 -> OnCircle Y0 C D -> Out C Y Y0 -> Bet P X Y -> Lt A X0 A Y0).
  { intros X Y X0 Y0; intros.
    apply t18_18 with C C; Cong.
      apply cong_transitivity with C D; Cong.
    apply lta_comm, (conga_preserves_lta A C X A C Y).
      apply out2__conga; [apply out_trivial|apply l6_6]; auto.
      apply out2__conga; [apply out_trivial|apply l6_6]; auto.
    split.
    { apply inangle__lea.
      assert_diffs.
      apply l11_24, in_angle_trans with P.
        repeat split; auto; exists X; split; Between; right; apply out_trivial; auto.
      apply in_angle_trans2 with Q.
        repeat split; auto.
        exists Y; split; Between.
        right; apply out_trivial; auto.
      destruct HDij as [HOS'|[[HCol HNCol]|[HNCol HCol]]].
      - apply l11_24, lea_in_angle; Lea; Side.
      - apply out341__inangle; auto.
        apply not_bet_out; Col.
        intro; apply (lta__nlea A C P A C Q); trivial.
        apply l11_31_2; auto.
      - apply in_angle_line; auto.
        apply between_symmetry, not_out_bet; Col.
        intro; apply (lta__nlea A C P A C Q); trivial.
        apply l11_31_1; auto.
    }
    intro.
    destruct (conga_cop__or_out_ts A C X Y); trivial.
    - assert (Col P Q X) by ColR.
      apply coplanar_pseudo_trans with P Q C; [assumption| |Cop..].
      destruct HDij as [|[[]|[]]]; Cop.
    - absurd (X = Y); trivial; apply (l6_21 P Q C X); ColR.
    - apply (HNTS X Y); trivial.
  }

  assert (HR : exists R, forall X Y,
    (Bet P X Q /\ (exists X0, OnCircle X0 C D /\ Out C X X0 /\ InCircle X0 A B)) ->
    (Bet P Y Q /\ (exists Y0, OnCircle Y0 C D /\ Out C Y Y0 /\ OutCircle Y0 A B)) ->
    Bet X R Y).
  { apply dedekind; [repeat constructor..|].
    exists P.
    intros X Y [HX [X0]] [HY [Y0]].
    destruct (l5_3 P X Y Q); trivial.
    destruct (eq_dec_points X Y).
      subst; Between.
    exfalso.
    spliter.
    apply (lt__nle A Y0 A X0).
      apply (Haux Y X); auto.
    apply le_transitivity with A B; trivial.
  }
  assert (HP : exists X0, OnCircle X0 C D /\ Out C P X0 /\ InCircle X0 A B).
    exists P; repeat (split; Circle); apply out_trivial; assert_diffs; auto.
  assert (HQ : exists Y0, OnCircle Y0 C D /\ Out C Q Y0 /\ OutCircle Y0 A B).
    exists Q; repeat (split; Circle); apply out_trivial; assert_diffs; auto.
  destruct HR as [R HR].
  assert (HBet : Bet P R Q) by (apply HR; split; Between).
  assert (R <> C) by (intro; subst; apply HNCol1; Col).
  destruct (onc_exists C D R) as [Z [HZ1 HZ2]]; auto.
  exists Z; split; trivial.
  assert (A <> B) by (apply (lt_diff A P), HPIn).
  destruct (circle_cases A B Z) as [|[Habs|Habs]]; trivial; exfalso.


  - assert (Q <> R).
    { intro; subst R.
      assert (Q = Z) by (apply (onc2_out__eq C D); trivial).
      subst.
      apply outcs__ninc in HQOut; Circle.
    }
    assert (HNCol2 : ~ Col C Q R) by (intro; apply HNCol1; ColR).
    assert (HT : exists T, OnCircle T A B /\ Bet A Z T).
    { destruct (eq_dec_points Z A).
        subst; exists B; split; Circle; Between.
      destruct (onc_exists A B Z) as [T [HT1 HT2]]; auto.
      exists T; split; trivial.
      apply l6_13_1; trivial.
      apply (l5_6 A Z A B); Cong; Le.
    }
    destruct HT as [T [HT1 HT2]].
    assert (T <> Z).
      intro; subst; apply incs__noutc in Habs; apply Habs; Circle.
    destruct (ex_per_cong C R Z Q T Z) as [I [HI1 [HI2 HI3]]]; Col.
    assert_diffs.
    assert (HNCol3 : ~ Col I Z C) by (apply per_not_col; auto).
    destruct (onc_exists C D I) as [X0 [HX0On HX0Out]]; auto.
    assert (HLt : Lt C X0 C I).
    { destruct (l11_46 I Z C) as [_ HLt]; auto.
        apply (cong2_lt__lt Z C I C); trivial.
          apply cong_transitivity with C D; Cong.
          Cong.
    }
    assert (X0 <> I) by (intro; apply (nlt C I); subst; assumption).
    assert (HNCol4 : ~ Col I X0 Z) by (intro; apply (one_side_not_col123 C R I Q); ColR).
    assert (HLt1 : Lt X0 Z I Z).
    { assert_diffs.
      destruct (l11_46 I X0 Z); auto.
      right.
      apply acute_bet__obtuse with C; auto.
        apply l6_13_1; [apply l6_6|]; Le.
      assert_diffs; apply cong__acute; auto.
      apply cong_transitivity with C D; Cong.
    }

    assert (HX0In : InCircleS X0 A B).
    { destruct (le_bet Z T Z X0) as [M [HM1 HM2]].
        apply (l5_6 X0 Z I Z); Cong; Le.
      assert (HMT : M <> T).
      { intro.
        apply (nlt Z M).
        apply (cong2_lt__lt X0 Z I Z); trivial; [|subst M; apply cong_transitivity with T Z]; Cong.
      }
      apply le1234_lt__lt with A M.
      - apply triangle_inequality with Z; Cong; eBetween.
      - apply (cong2_lt__lt A M A T); Cong.
        assert (Bet A M T) by eBetween.
        split; Le.
        intro.
        apply HMT, (between_cong A); assumption.
    }
    assert_diffs.
    assert (HX : InAngle X0 R C Q).
    { apply l11_25 with X0 Z Q; try (apply out_trivial); auto.
      apply lea_in_angle.
      - apply t18_19; auto.
          apply cong_transitivity with C D; Cong.
          Cong.
        apply le3456_lt__lt with I Z; trivial.
        apply (l5_6 T Z Q Z); Cong.
        assert (HLe : Le A T A Q) by (apply (l5_6 A B A Q); Cong; Le).
        destruct (eq_dec_points A Z).
          subst; Le.
        destruct (l5_5_1 A T A Q) as [M [HM1 HM2]]; trivial.
        assert (Bet A Z M) by eBetween.
        apply le_transitivity with M Z.
          apply bet__le2313; eBetween.
        apply le_comm, (triangle_reverse_inequality A); Cong.
        apply bet_out; auto.
      - apply invert_one_side, col_one_side with R; Col.
        apply one_side_transitivity with I; Side.
        apply out_one_side; trivial.
        left; apply one_side_not_col123 with Q; trivial.
    }
    destruct HX as [_ [_ [_ [X [HX1 [HX2|HX2]]]]]].
      subst; apply HNCol2; Col.
    assert (X = R).
      apply between_equality with Q; trivial.
      apply HR; split; [eBetween|..]; Between.
      exists X0; repeat (split; Circle).
    subst; apply HNCol4; ColR.


  - assert (P <> R).
    { intro; subst R.
      assert (P = Z) by (apply (onc2_out__eq C D); trivial).
      subst.
      apply incs__noutc in HPIn; Circle.
    }
    assert (HNCol2 : ~ Col C P R) by (intro; apply HNCol1; ColR).
    destruct (onc_exists A B Z) as [T [HT1 HT2]]; auto.
      apply (lt_diff A B), lt_right_comm, Habs.
    assert (HT3 : Bet A T Z).
    { apply l6_13_1.
        apply l6_6, HT2.
      apply (l5_6 A B A Z); Cong; Le.
    }
    assert (T <> Z).
      intro; subst; apply outcs__ninc in Habs; apply Habs; Circle.
    destruct (ex_per_cong C R Z P T Z) as [I [HI1 [HI2 HI3]]]; Col.
    assert_diffs.
    assert (HNCol3 : ~ Col I Z C) by (apply per_not_col; auto).

    destruct (onc_exists C D I) as [Y0 [HY0On HY0Out]]; auto.
    assert (HLt : Lt C Y0 C I).
    { destruct (l11_46 I Z C) as [_ HLt]; auto.
        apply (cong2_lt__lt Z C I C); trivial.
          apply cong_transitivity with C D; Cong.
          Cong.
    }
    assert (Y0 <> I) by (intro; apply (nlt C I); subst; assumption).
    assert (HNCol4 : ~ Col I Y0 Z) by (intro; apply (one_side_not_col123 C R I P); ColR).
    assert (HLt1 : Lt Y0 Z I Z).
    { assert_diffs.
      destruct (l11_46 I Y0 Z); auto.
      right.
      apply acute_bet__obtuse with C; auto.
        apply l6_13_1; [apply l6_6|]; Le.
      assert_diffs; apply cong__acute; auto.
      apply cong_transitivity with C D; Cong.
    }

    assert (HY0OutC : OutCircleS Y0 A B).
    { destruct (le_bet Z T Z Y0) as [M [HM1 HM2]].
        apply (l5_6 Y0 Z I Z); Cong; Le.
      assert (HTM : T <> M).
      { intro.
        apply (nlt Z M).
        apply (cong2_lt__lt Y0 Z I Z); trivial; [|subst M; apply cong_transitivity with T Z]; Cong.
      }
      apply le3456_lt__lt with A M.
      - apply (cong2_lt__lt A T A M); Cong.
        assert (Bet A T M) by eBetween.
        split; Le.
        intro.
        apply HTM, (between_cong A); assumption.
      - apply (triangle_reverse_inequality Z); Cong.
        assert_diffs; apply l6_6, bet_out; eBetween.
    }
    assert_diffs.
    assert (HY : InAngle Y0 P C R).
    { apply l11_25 with Y0 P Z; try (apply out_trivial); auto.
      apply l11_24, lea_in_angle.
      - apply t18_19; auto.
          apply cong_transitivity with C D; Cong.
          Cong.
        apply le3456_lt__lt with I Z; trivial.
        apply (l5_6 T Z P Z); Cong.
        destruct (le_bet A T A P) as [M [HM1 HM2]].
          apply (l5_6 A P A B); Cong; Le.
        assert (Bet A M Z) by eBetween.
        destruct (eq_dec_points M A).
          treat_equalities; Le.
        apply le_transitivity with M Z.
          apply bet__le2313; eBetween.
        apply le_comm, (triangle_reverse_inequality A); Cong.
        apply l6_6, bet_out; auto.
      - apply invert_one_side, col_one_side with R; Col.
        apply one_side_transitivity with I; Side.
        apply out_one_side; trivial.
        left; apply one_side_not_col123 with P; trivial.
    }
    destruct HY as [_ [_ [_ [Y [HY1 [HY2|HY2]]]]]].
      subst; apply HNCol2; Col.
    assert (Y = R).
      apply between_equality with P; apply between_symmetry; trivial.
      apply HR; split; [Between..| |]; [eBetween|].
      exists Y0; repeat (split; Circle).
    subst; apply HNCol4; ColR.
Qed.

End Dedekind_circle_circle.