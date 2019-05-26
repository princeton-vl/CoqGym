Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section Aristotle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma aristotle__greenberg : aristotle_s_axiom -> greenberg_s_axiom.
Proof.
  intros aristotle P Q R A B C.
  intros HNColB HABCacute HQRdiff HQright.
  elim (eq_dec_points P Q); intro HPQdiff.
  { treat_equalities.
    assert_diffs.
    exists R.
    split; [|apply out_trivial; auto].
    split.
    apply lea121345; auto.
    intro.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (eq_conga_out P R); auto.
  }
  assert (HXY : (exists X Y, Out B A X /\ Out B C Y /\ Per B X Y /\ Lt P Q X Y)) by (apply aristotle; assumption).
  destruct HXY as [X [Y [PX [PY [HXright [Hle HNcong]]]]]].
  assert_diffs.
  assert (HXYdiff : X <> Y) by (intro; treat_equalities; auto).
  assert (HT : (exists T, Out Q T P /\ Cong Q T X Y)) by (apply l6_11_existence; auto).
  destruct HT as [T []].
  assert (HS : (exists S, Out Q S R /\ Cong Q S X B)) by (apply l6_11_existence; auto).
  destruct HS as [S []].
  assert_diffs.
  exists S.
  split; auto.
  assert_cols.
  assert (Per S Q P) by (apply (l8_3 R); Perp; Col).
  assert (Per T Q S) by (apply (l8_3 P); Perp; Col).
  assert (P<>S).
  { intro; treat_equalities.
    assert (P=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  assert (T<>S).
  { intro; treat_equalities.
    assert (T=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  apply conga_preserves_lta with P S Q T S Q; try (apply conga_refl; auto); [|split].
  - apply conga_trans with X B Y.
    2: apply (out_conga A B C A B C); CongA; apply out_trivial; auto.
    assert (HInter : (Cong T S Y B /\ (T <> S -> CongA Q T S X Y B /\ CongA Q S T X B Y))).
    { apply (l11_49 T Q S Y X B); Cong.
      apply l11_16; Perp.
    }
    destruct HInter as [_ [_ HConga]]; auto.
    apply conga_left_comm; auto.

  - apply lea_comm.
    apply (l11_29_b Q S P Q S T).
    exists T.
    split; CongA.
    repeat split; auto.
    exists P.
    split; [|right; apply out_trivial; auto].
    apply l6_13_1.
    apply l6_6; auto.
    apply (le_transitivity Q P X Y).
    apply (le_transitivity Q P P Q); Le.
    apply (cong__le); Cong.

  - intro HConga.
    assert (HInter : Cong Q P Q T /\ Cong S P S T /\ CongA Q P S Q T S).
    { apply l11_50_1; Cong.
      { intro.
        assert (HUn : S=Q\/P=Q) by (apply l8_9; Col).
        destruct HUn; treat_equalities; absurde.
      }
      apply l11_16; Perp.
      CongA.
    }
    destruct HInter as [HCong _].
    apply HNcong.
    apply (cong_transitivity P Q T Q); Cong.
Qed.

(** This proof is inspired by Several topics from geometry, by Franz Rothe *)

Lemma aristotle__obtuse_case_elimination :
  aristotle_s_axiom ->
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  intros aristotle obtuse.
  destruct ex_lambert as [Q' [C' [P [Q HLam]]]].
  assert (HObtuse : Obtuse C' P Q) by (apply <- (lam_obtuse__oah Q'); trivial).
  assert (HPar : Par_strict Q' Q C' P) by (apply lam__par_strict1423, HLam).
  destruct HLam; spliter.
  destruct (l10_15 P Q P C') as [A' [HPerp HOS]]; Col.
    apply not_col_permutation_1.
    apply par_strict_not_col_1 with Q'; Par.
  assert_diffs.
  assert (HLtA : LtA Q P A' C' P Q) by (apply obtuse_per__lta; Perp).
  destruct HLtA as [HLeA HNCongA].
  assert (HInAngle : InAngle A' Q P C').
    apply lea_in_angle; Side; apply lea_right_comm; trivial.
  destruct (segment_construction C' P C' P) as [C [HC1 HC2]].
  destruct (segment_construction A' P A' P) as [A [HA1 HA2]].
  assert_diffs.
  assert (HInAngle1 : InAngle C A P Q).
    apply in_angle_reverse with A'; auto.
    apply l11_24, in_angle_reverse with C'; auto.
    apply l11_24; trivial.
  assert (HNCol : ~ Col P C' A').
  { intro Habs.
    apply HNCongA, conga_right_comm, out2__conga.
      apply out_trivial; auto.
    apply col_one_side_out with Q; trivial.
  }
  assert (HNCol1 : ~ Col P C A) by (intro; apply HNCol; ColR).
  assert (HNCol2 : ~ Col P Q C) by (intro; apply (par_strict_not_col_2 Q' Q C' P); ColR).
  assert (HPer : Per A P Q) by (apply l8_2, per_col with A'; Perp; Col).
  assert (HOS1 : OS A P C Q).
    apply in_angle_one_side; Col.
    apply per_not_col; auto.
  destruct (aristotle P Q A P C) as [X [Y]]; Col.
  { exists A, P, Q; split; Perp; split.
      apply inangle__lea; trivial.
    intro HCongA.
    destruct (conga_cop__or_out_ts A P C Q); CongA; Cop.
      assert_cols; Col.
      apply (l9_9 A P C Q); trivial.
  }

  spliter.
  apply (not_and_lt P Q X Y).
  split; trivial.
  destruct (l8_18_existence P Q Y) as [Z [HZ1 HZ2]].
    intro; assert_diffs; apply HNCol2; ColR.
  apply lt_transitivity with P Z.

  - assert (P <> Z).
    { intro; subst Z.
      assert_diffs.
      assert (Per Q P C) by (apply per_col with Y; Col; Perp).
      apply HNCol1, cop_perp2__col with P Q; Perp; Cop.
    }
    assert (HLam : Lambert P X Y Z).
    { assert_diffs.
      repeat split; auto.
        apply per_col with Q; Col.
        apply l8_2, per_col with A; Perp; Col.
        apply perp_per_1, perp_left_comm, perp_col with Q; auto.
        assert (InAngle Y X P Q).
          apply l11_25 with C A Q; try (apply l6_6); trivial; apply out_trivial; auto.
        apply coplanar_perm_12, col_cop__cop with Q; Col; Cop.
    }
    apply lam_obtuse__lt; trivial.
    apply <- (lam_obtuse__oah P); trivial.

  - assert (HOut : Out Q P Z).
    { apply col_one_side_out with Q'; Col.
      apply one_side_transitivity with Y.
        apply l12_6, par_strict_col_par_strict with C'; Par; ColR.
      apply l12_6, par_not_col_strict with Y; Col.
      { apply l12_9 with P Q; Perp; [Cop..| |Cop].
        apply coplanar_perm_12, col_cop__cop with C; Col.
        apply  col_cop__cop with C'; Col; Cop.
      }
      apply not_col_permutation_1, par_not_col with P C'; Par; ColR.
    }
    assert_diffs.
    apply bet__lt1213; auto.
    apply out2__bet; trivial.
    apply col_one_side_out with A; Col.
    apply one_side_transitivity with Y.
    { apply l12_6, par_not_col_strict with Y; Col.
        apply l12_9 with P Q; Perp; [Cop..|].
        apply coplanar_perm_12, col_cop__cop with C; Col; Cop.
      intro; apply HNCol1; ColR.
    }
    apply one_side_symmetry, out_out_one_side with C; Side.
Qed.

Lemma aristotle__acute_or_right :
  aristotle_s_axiom ->
  hypothesis_of_acute_saccheri_quadrilaterals \/ hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros aristotle.
  destruct saccheri_s_three_hypotheses as [Ha|[Hr|Ho]]; auto.
  exfalso; apply aristotle__obtuse_case_elimination in aristotle; auto.
Qed.

End Aristotle.