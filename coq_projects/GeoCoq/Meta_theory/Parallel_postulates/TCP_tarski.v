Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.tarski_s_euclid_remove_degenerated_cases.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section TCP_tarski.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma impossible_case_1 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet A B x ->
  Bet C y A ->
  Bet x T y ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HADT HBCT HBDC HABx HACy HxTy HPar.
apply between_symmetry in HABx.
assert (HI := inner_pasch x C A B y HABx HACy); destruct HI as [I [HBCI HIxy]].
apply HPar; exists I; assert_cols; Col.
Qed.

Lemma impossible_case_2 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Col A B x ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet y A C ->
  Bet x T y ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HABx HADT HBCT HBDC HACy HxTy.
apply between_symmetry in HACy.
assert (HI := inner_pasch C x y A T HACy HxTy); destruct HI as [I [HAIx HICT]].
assert (HAx : A <> x) by (intro; treat_equalities; apply HABC; assert_cols; ColR).
assert (HTS : TS A B C T) by (repeat (split; Col); try (intro; apply HBCT; assert_cols; ColR);
exists I; split; Between; assert_cols; ColR); apply l9_9 in HTS.
apply HTS; apply one_side_transitivity with D.

  assert (HABB : Col A B B) by Col.
  assert (HBDC' : Col C D B) by (assert_cols; Col).
  assert (H := l9_19 A B C D B HABB HBDC'); rewrite H.
  split; try (intro; apply HABC; Col).
  repeat (split; Between).

  assert (HABA : Col A B A) by Col.
  assert (HDTA : Col D T A) by (assert_cols; Col).
  assert (H := l9_19 A B D T A HABA HDTA); rewrite H.
  split; try (intro; apply HABC; assert_cols; ColR).
  repeat (split; Between).
Qed.

Lemma impossible_case_3 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B x A ->
  Bet x T y ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HADT HBCT HBDC HABx HxTy HPar.
apply between_symmetry in HADT.
assert (HI := inner_pasch B T A x D HABx HADT); destruct HI as [I [HITx HBDI]].
assert (HTx : T <> x) by (intro; subst; apply HABC; assert_cols; ColR).
assert (HPar' : Par_strict B D x T) by (apply par_strict_col_par_strict with y; assert_cols; Col;
apply par_strict_symmetry; apply par_strict_col_par_strict with C; Col; Par).
apply HPar'; exists I; assert_cols; Col.
Qed.

Lemma impossible_case_4_1 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet A x B \/ Bet A B x ->
  Bet T y x ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HACy HADT HBCT HBDC HABx HTyx.
assert (HTS : TS A C x T) by (repeat (split; Col); try (intro; apply HBCT; assert_cols; ColR);
                                     exists y; split; assert_cols; Col; Between).
assert (HAx : A <> x) by (intro; subst; apply HABC; assert_cols; ColR).
assert (HOS : OS A C x B).
{
  assert (HACA : Col A C A) by Col.
  assert (HABx' : Col x B A) by (induction HABx; assert_cols; Col).
  assert (H := l9_19 A C x B A HACA HABx'); rewrite H.
  split; try (intro; apply HABC; assert_cols; ColR).
  repeat (split; auto).
}
assert (HTS' : TS A C B T) by (apply l9_8_2 with x; assumption);
clear HTS; clear HOS; rename HTS' into HTS; apply l9_9 in HTS.
apply HTS; apply one_side_transitivity with D.

  assert (HACC : Col A C C) by Col.
  assert (HBDC' : Col B D C) by (assert_cols; Col).
  assert (H := l9_19 A C B D C HACC HBDC'); rewrite H.
  split; try (intro; apply HABC; Col).
  repeat (split; Between).

  assert (HACA : Col A C A) by Col.
  assert (HDTA : Col D T A) by (assert_cols; Col).
  assert (H := l9_19 A C D T A HACA HDTA); rewrite H.
  split; try (intro; apply HABC; assert_cols; ColR).
  repeat (split; Between).
Qed.

Lemma impossible_case_4_2 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B A x ->
  Bet T y x ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
assert (HTS : TS B C A T) by (repeat (split; Col); try (intro; apply HBCT; assert_cols; ColR);
                                     exists D; split; assert_cols; Col; Between).
assert (HOS : OS B C A x).
{
  assert (HBCB : Col B C B) by Col.
  assert (HABx' : Col A x B) by Col.
  assert (H := l9_19 B C A x B HBCB HABx'); rewrite H.
  split; try (intro; apply HABC; assert_cols; ColR).
  repeat (split; Between).
  intro; treat_equalities; intuition.
}
assert (HTS' : TS B C x T) by (apply l9_8_2 with A; assumption);
clear HTS; clear HOS; destruct HTS' as [Hclear [Hclear' [I [HBCI HITx]]]];
clear Hclear; clear Hclear'.
assert (HTx : T <> x) by (intro; subst; apply HABC; assert_cols; ColR).
assert (HPar' : Par_strict B C x T) by (apply par_strict_col_par_strict with y; assert_cols; Col).
apply HPar'; exists I; assert_cols; Col.
Qed.

Lemma impossible_case_4 :
  forall A B C D T x y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  B <> C ->
  B <> D ->
  B <> T ->
  C <> D ->
  C <> T ->
  D <> T ->
  x <> y ->
  ~ Col A B C ->
  Col A C y ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col A B x ->
  Bet T y x ->
  Par_strict B C x y ->
  False.
Proof.
intros A B C D T x y.
intros HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT Hxy.
intros HABC HACy HADT HBCT HBDC HABx HTyx HPar.
elim HABx; clear HABx; intro HABx.

  apply impossible_case_4_1 with A B C D T x y; Col.

  elim HABx; clear HABx; intro HABx.

    apply impossible_case_4_1 with A B C D T x y; Between.

    apply impossible_case_4_2 with A B C D T x y; Between.
Qed.

Lemma impossible_two_sides_not_col : forall A B C D T Y,
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  A <> Y ->
  B <> C ->
  B <> D ->
  B <> T ->
  B <> Y ->
  C <> D ->
  C <> T ->
  C <> Y ->
  D <> T ->
  T <> Y ->
  ~ Col A B C ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Bet B Y T ->
  ~ Col A C Y.
Proof.
intros A B C D T Y HAB HAC HAD HAT HAY HBC HBD HBT HBY HCD HCT HCY HDT HTY.
intros  HABC HADT HBCT HBDC HBYT.
intro HACY.
assert (HTS : TS A C B T)
  by (repeat (split; Col); try (intro; apply HABC; assert_cols; ColR); exists Y; split; Col; Between).
apply l9_9 in HTS; apply HTS; apply one_side_transitivity with D.

  assert (HACC : Col A C C) by Col.
  assert (HBDC' : Col B D C) by (assert_cols; Col).
  assert (H := l9_19 A C B D C HACC HBDC'); rewrite H.
  split; try (intro; apply HABC; Col).
  repeat (split; Between).

  assert (HACA : Col A C A) by Col.
  assert (HDTA : Col D T A) by (assert_cols; Col).
  assert (H := l9_19 A C D T A HACA HDTA); rewrite H.
  split; try (intro; apply HABC; assert_cols; ColR).
  repeat (split; Between).
Qed.

(*
Lemma triangle_circumscription_aux : forall A B C P,
  Cong A P B P -> Cong A P C P -> exists CC, Cong A CC B CC /\ Cong A CC C CC /\ Coplanar A B C CC.
Proof.
  intros A B C D HCong1 HCong2.
  destruct (cop_dec A B C D).
    exists D; repeat split; assumption.
  destruct (l11_62_existence A B C D) as [CC [HCop HCC]].
  exists CC.
  assert (CC <> D) by (intro; subst; Cop).
  assert (Per B CC D) by Cop.
  assert (A <> CC).
  { intro; subst CC.
    destruct (l11_46 B A D) as [_ []]; auto.
    assert_diffs; apply per_not_col; auto.
  }
  assert (Per A CC D) by Cop.
  repeat split; trivial.
  - destruct (cong2_per2__cong_conga2 A CC D B CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A B D) as [_ []]; Cong.
    assert_diffs; apply per_not_col; auto.
  - assert (Per C CC D) by Cop.
    destruct (cong2_per2__cong_conga2 A CC D C CC D); Cong.
    intro; subst CC.
    destruct (l11_46 A C D) as [_ []]; Cong.
    apply per_not_col; auto.
Qed.
*)

Lemma triangle_circumscription_implies_tarski_s_euclid_aux :
  forall A B C D T X Y Z M1 Z1 M2 Z2,
  triangle_circumscription_principle ->
  A <> B ->
  A <> C ->
  A <> D ->
  A <> T ->
  A <> Y ->
  B <> C ->
  B <> D ->
  B <> T ->
  B <> Y ->
  C <> D ->
  C <> T ->
  C <> Y ->
  D <> T ->
  T <> X ->
  T <> Y ->
  X <> Y ->
  Y <> Z1 ->
  Y <> Z2 ->
  ~ Col A B C ->
  Col A B M1 ->
  Col A C M2 ->
  Bet A D T ->
  ~ Col B C T ->
  Bet B D C ->
  Col T Y Z ->
  Bet Y T X ->
  Bet Y M1 Z1 ->
  Bet Y M2 Z2 ->
  Cong Y T T X ->
  Cong Y M1 M1 Z1 ->
  Cong Y M2 M2 Z2 ->
  Perp B C T Z ->
  Perp A B Y Z1 ->
  Perp A C Y Z2 ->
  exists x, exists y, Bet A B x /\ Bet A C y /\ Bet x T y.
Proof.
intros A B C D T X Y Z M1 Z1 M2 Z2; intro HTC.
intros HAB HAC HAD HAT HAY HBC HBD HBT HBY HCD HCT HCY HDT HTX HTY HXY HYZ1 HYZ2.
intros HABC HABM1 HACM2 HADT HBCT HBDC HTYZ HYTX HYM1Z1.
intros HYM2Z2 HCong5 HCong6 HCong7 HPerp1 HPerp2 HPerp3.
elim (col_dec X Y Z1); intro HXYZ1; elim (col_dec X Y Z2); intro HXYZ2.

  exfalso; apply HABC; apply par_id.
  apply l12_9 with Y Z1; Perp.
    exists A; right; left; split; Col.
    apply coplanar_perm_16, col_cop__cop with Z2; Cop; ColR.
    Cop.
    assert_diffs; apply coplanar_perm_16, col2_cop__cop with T Z; Cop; ColR.
  apply perp_col1 with Z2; assert_diffs; Perp; ColR.

  exfalso; apply HABC; apply par_id_1.
  assert (Coplanar B C Y Z1) by (assert_diffs; apply col2_cop__cop with T Z; Cop; ColR).
  apply l12_9 with Y Z1; [Cop..| |Perp|].
    apply coplanar_pseudo_trans with B C T; [assumption|..|Cop].
    assert_diffs; apply col_cop__cop with Z; Col; Cop.
    assert_diffs; apply col_cop__cop with Z; Cop; ColR.
    exists D; left; split; Col.
  apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

  exfalso; apply HABC; apply par_id_2.
  assert (Coplanar B C Y Z2) by (assert_diffs; apply col2_cop__cop with T Z; Cop; ColR).
  apply l12_9 with Y Z2; [Cop..| |Perp|].
    apply coplanar_pseudo_trans with B C T; [assumption|..|Cop].
    assert_diffs; apply col_cop__cop with Z; Col; Cop.
    assert_diffs; apply col_cop__cop with Z; Cop; ColR.
    exists D; left; split; Col.
  apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

  assert (H := HXYZ1); apply HTC in H;
  destruct H as [x [HCong1 [HCong2 HCop1]]]; exists x;
  assert (H := HXYZ2); apply HTC in H;
  destruct H as [y [HCong3 [HCong4 HCop2]]]; exists y.
  assert (HYM1 : Y <> M1) by (intro; treat_equalities; auto).
  assert (HYM2 : Y <> M2) by (intro; treat_equalities; auto).
  assert (HCopA : Coplanar B C T A) by (exists D; left; split; Col).
  assert (HCopB : Coplanar B C T B) by Cop.
  assert (HCopC : Coplanar B C T C) by Cop.
  assert (HCopT : Coplanar B C T T) by Cop.
  assert (HCopZ : Coplanar B C T Z) by Cop.
  assert (HCopY : Coplanar B C T Y) by (assert_diffs; apply col_cop__cop with Z; Col).
  assert (HCopX : Coplanar B C T X) by (apply col_cop__cop with Y; Col).
  assert (HCopZ1 : Coplanar B C T Z1).
  { assert (~ Col A B Y).
      intro; destruct (perp_not_col2 A B Y Z1) as [|HNCol]; Perp; apply HNCol; ColR.
    apply coplanar_pseudo_trans with A B Y; [| |apply coplanar_pseudo_trans with B C T..|]; Cop.
  }
  assert (HCopZ2 : Coplanar B C T Z2).
  { assert (~ Col A C Y).
      intro; destruct (perp_not_col2 A C Y Z2) as [|HNCol]; Perp; apply HNCol; ColR.
    apply coplanar_pseudo_trans with A C Y;
    [|apply coplanar_pseudo_trans with B C T| |apply coplanar_pseudo_trans with B C T|]; Cop.
  }
  assert (HCopx : Coplanar B C T x).
    apply coplanar_pseudo_trans with X Y Z1; trivial; apply coplanar_pseudo_trans with B C T; assumption.
  assert (HCopy : Coplanar B C T y).
    apply coplanar_pseudo_trans with X Y Z2; trivial; apply coplanar_pseudo_trans with B C T; assumption.
  assert (HCop : Coplanar X Y x y).
    apply coplanar_pseudo_trans with B C T; assumption.
  assert (HxTy : Col x T y) by (elim (eq_dec_points T x); intro; elim (eq_dec_points T y);
                                intro; try (subst; Col); apply col_permutation_4;
                                apply cop_perp2__col with X Y; trivial; apply perp_bisect_perp;
                                apply cong_cop_perp_bisect; Cong; Cop).
  assert (HABx : Col A B x).
    {
    elim (eq_dec_points A M1); intro HAM1; subst.

      {
      apply cong_cop2_perp_bisect_col with Y Z1; trivial.
        exists M1; left; split; Col.
        apply coplanar_pseudo_trans with B C T; assumption.
        apply cong_transitivity with X x; Cong.
      apply perp_mid_perp_bisect; try split; Cong.
      }

      {
      assert (Col M1 A x).
        {
        apply cong_cop2_perp_bisect_col with Y Z1; trivial.
          exists M1; left; split; Col.
          apply coplanar_pseudo_trans with B C T; assumption.
          apply cong_transitivity with X x; Cong.
        apply perp_mid_perp_bisect; try split; Cong.
        apply perp_left_comm; apply perp_col with B; Col.
        }
      ColR.
      }
    }

  assert (HACy : Col A C y).
    {
    elim (eq_dec_points A M2); intro HAM1; subst.

      {
      apply cong_cop2_perp_bisect_col with Y Z2; trivial.
        exists M2; left; split; Col.
        apply coplanar_pseudo_trans with B C T; assumption.
        apply cong_transitivity with X y; Cong.
      apply perp_mid_perp_bisect; try split; Cong.
      }

      {
      assert (Col M2 A y).
        {
        apply cong_cop2_perp_bisect_col with Y Z2; trivial.
          exists M2; left; split; Col.
          apply coplanar_pseudo_trans with B C T; assumption.
          apply cong_transitivity with X y; Cong.
        apply perp_mid_perp_bisect; try split; Cong.
        apply perp_left_comm; apply perp_col with C; Col.
        }
      ColR.
      }
    }
  assert (Hxy : x <> y).
  {
    intro; treat_equalities.
    assert (A = x) by (apply l6_21 with A B C A; Col); treat_equalities.
    assert (H : Par B C A T).
    {
      apply l12_9 with X Y; try (apply coplanar_pseudo_trans with B C T; assumption).

        apply perp_sym; apply perp_col2 with Z T; Perp; assert_cols; ColR.
        apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong.
        exists T; left; split; Col.
    }
    elim H; clear H; intro H.

      apply H; exists D; assert_cols; Col.

      spliter; apply HABC; assert_cols; ColR.
  }
  assert (HPar : Par B C x y).
  {
    apply l12_9 with X Y; try (apply coplanar_pseudo_trans with B C T; assumption).

      apply perp_sym; apply perp_col2 with T Z; Perp; assert_cols; ColR.

      apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong; Cop.
  }
  clear HPerp1; clear HPerp2; clear HPerp3.
  clear HCong1; clear HCong2; clear HCong3; clear HCong4.
  assert (HPar' : Par_strict B C x y)
    by (elim HPar; clear HPar; intro HPar; try assumption; spliter; exfalso; apply HABC; assert_cols; ColR);
  clear HPar; rename HPar' into HPar.
  elim HxTy; clear HxTy; intro HxTy.

    elim HABx; clear HABx; intro HABx.

      elim HACy; clear HACy; intro HACy; auto.
      elim HACy; clear HACy; intro HACy.

        exfalso; apply impossible_case_1 with A B C D T x y; assumption.

        exfalso; apply impossible_case_2 with A B C D T x y; assert_cols; Col.

      elim HABx; clear HABx; intro HABx.

        exfalso; apply impossible_case_3 with A B C D T x y; assumption.

        exfalso; apply impossible_case_2 with A C B D T y x; assert_cols; Col; Between.

    elim HxTy; clear HxTy; intro HxTy.

      exfalso; apply impossible_case_4 with A B C D T x y; assumption.

      exfalso; apply impossible_case_4 with A C B D T y x; Between; Col; Par.
Qed.

Lemma triangle_circumscription_implies_tarski_s_euclid :
  triangle_circumscription_principle ->
  tarski_s_parallel_postulate.
Proof.
unfold tarski_s_parallel_postulate.
intro HTC; apply tarski_s_euclid_remove_degenerated_cases.
intros A B C D T HAB HAC HAD HAT HBC HBD HBT HCD HCT HDT HABC HADT HBDC;
assert (HBCT : ~ Col B C T) by (intro; apply HABC; assert_cols; ColR).
assert (HY := l8_18_existence B C T HBCT); destruct HY as [Y [HBCY HPerp]].
elim (eq_dec_points B Y); intro HBY; elim (eq_dec_points C Y); intro HCY; treat_equalities.

  {
  exfalso; apply HBCT; Col.
  }

  {
  assert (HY := midpoint_existence B T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (H := midpoint_distinct_1 Y B T HBT HY); destruct H as [HBY HTY];
  apply not_eq_sym in HBY; apply not_eq_sym in HTY.
  assert (HCY : C <> Y) by (intro; subst; apply HBCT; assert_cols; Col).
  destruct HY as [HBTY HBYTY].
  assert (HACY : ~ Col A C Y) by (apply impossible_two_sides_not_col with B D T; assumption).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities.

    {
    assert (HFalse : Col A B C) by (assert_cols; ColR); contradiction.
    }

    {
    elim HZ1; clear HZ1; intro HZ1; try contradiction.
    elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities; try contradiction.
    elim HZ2; clear HZ2; intro HZ2; try contradiction.
    apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y B M1 Z1 M2 Z2; try assumption.
    assert_cols; Col.
    }
  }

  {
  assert (HY := midpoint_existence C T); destruct HY as [Y HY].
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (H := midpoint_distinct_1 Y C T HCT HY); destruct H as [HCY HTY];
  apply not_eq_sym in HCY; apply not_eq_sym in HTY.
  assert (HBY : B <> Y) by (intro; subst; apply HBCT; assert_cols; Col).
  destruct HY as [HCTY HCYTY].
  assert (HACY : ~ Col A B Y) by (apply impossible_two_sides_not_col with C D T; Between; Col).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities.

    {
    assert (HFalse : Col A B C) by (assert_cols; ColR); contradiction.
    }

    {
    elim HZ2; clear HZ2; intro HZ2; try contradiction.
    elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities; try contradiction.
    elim HZ1; clear HZ1; intro HZ1; try contradiction.
    apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y C M1 Z1 M2 Z2; try assumption.
    assert_cols; Col.
    }
  }

  {
  assert (HAY : A <> Y) by (intro; treat_equalities; assert_cols; apply HABC; ColR).
  assert (HX := symmetric_point_construction Y T); destruct HX as [X HX].
  assert (H := perp_distinct B C T Y HPerp); destruct H as [Hclear HTY]; clear Hclear.
  assert (H := midpoint_distinct_2 T Y X HTY HX); destruct H as [HTX HXY]; apply not_eq_sym in HTX.
  destruct HX as [HXTY HXTYT].
  assert (HZ1 := l10_2_existence A B Y); destruct HZ1 as [Z1 HZ1].
  elim HZ1; clear HZ1; intro HZ1; destruct HZ1 as [Hclear HZ1]; try contradiction; clear Hclear.
  destruct HZ1 as [[M1 [[HXM1Z1 HM1XM1Z1] HABM1]] HZ1].
  assert (HZ2 := l10_2_existence A C Y); destruct HZ2 as [Z2 HZ2].
  elim HZ2; clear HZ2; intro HZ2; destruct HZ2 as [Hclear HZ2]; try contradiction; clear Hclear.
  destruct HZ2 as [[M2 [[HXM2Z2 HM2XM2Z2] HACM2]] HZ2].
  assert (HABY : ~ Col A B Y) by (intro; apply HBY; apply l6_21 with A B C B; assert_cols; Col).
  assert (HACY : ~ Col A C Y) by (intro; apply HCY; apply l6_21 with A C B C; assert_cols; Col).
  elim (eq_dec_points Y Z1); intro HYZ1; treat_equalities; try contradiction.
  elim HZ1; clear HZ1; intro HZ1; try contradiction.
  elim (eq_dec_points Y Z2); intro HYZ2; treat_equalities; try contradiction.
  elim HZ2; clear HZ2; intro HZ2; try contradiction.
  apply triangle_circumscription_implies_tarski_s_euclid_aux with D X Y Y M1 Z1 M2 Z2; Col.
  }
Qed.

End TCP_tarski.