Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Annexes.perp_bisect.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section existential_playfair_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma existential_playfair__rah :
  existential_playfair_s_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
intro HP; destruct HP as [A1 [A2 [P [HNC1 HP]]]].
destruct (l8_18_existence A1 A2 P) as [Q [HCcol1 HPerp1]]; Col.
assert (HA3 : exists A3, Col A1 A2 A3 /\ A3 <> Q).
{
  destruct (eq_dec_points A1 Q).
    subst; exists A2; assert_diffs; split; Col.
    exists A1; split; Col.
}
destruct HA3 as [A3 []].
destruct (ex_perp_cop P Q P A3) as [R [HPerp2 HCop]].
  assert_diffs; auto.
assert (HPar1 : Par A1 A2 P R).
{
  assert_diffs.
  apply l12_9 with P Q; Perp.
    Cop.
    apply coplanar_perm_3, col_cop__cop with A3; Cop; ColR.
    Cop.
    apply coplanar_perm_3, col_cop__cop with A3; Cop; ColR.
}
assert (HCop1 : Coplanar A1 A2 P R) by (apply par__coplanar, HPar1).
assert (HNC2 : Par_strict A1 A2 P R)
  by (apply par_not_col_strict with P; Col).
apply par_strict_not_col_4 in HNC2.
destruct (l8_18_existence A1 A2 R) as [S [HCcol2 HPerp3]]; Col.
assert (HPar2 : Par P Q R S) by (apply l12_9 with A1 A2; Perp; Cop).
assert (HNC3 : ~ Col P Q R) by (apply perp_not_col; Perp).
assert (HNC4 : Par_strict P Q R S) by (apply par_not_col_strict with R; Col).
apply par_strict_not_col_3 in HNC4.
destruct (l8_18_existence R S P) as [R' [HCcol3 HPerp4]]; Col.
assert (HPar3 : Par A1 A2 P R').
{
  assert_diffs.
  apply l12_9 with R S; Perp.
    apply coplanar_perm_5, col_cop__cop with A2; Col; Cop.
    exists R'; left; split; Col.
    apply coplanar_perm_5, col_cop__cop with A1; Col; Cop.
    exists R'; left; split; Col.
}
destruct (HP P R P R') as [_ HCol4]; Col.
assert (R = R') by (apply l6_21 with P R S R; assert_diffs; Col).
treat_equalities; rewrite <- (lam_per__rah P Q S R).

  {
  apply perp_in_per_1 with S S; apply l8_14_2_1b_bis; Col.
  apply perp_sym; apply perp_col0 with A1 A2; Col.
  assert (HPs : Par_strict P Q R S) by (apply par_not_col_strict with R; Col).
  apply par_strict_not_col_2 in HPs; assert_diffs; auto.
  }

  {
  assert (HPs : Par_strict P Q R S) by (apply par_not_col_strict with R; Col).
  apply par_strict_not_col_2 in HPs.
  repeat try (split; [intro; treat_equalities; assert_diffs; intuition|]).
  apply par__coplanar in HPar2.
  repeat split; Cop.
  - apply perp_in_per_1 with P P; apply l8_14_2_1b_bis; Col; Perp.
  - apply perp_in_per_1 with R R; apply l8_14_2_1b_bis; Col; Perp.
  - apply perp_in_per_1 with Q Q; apply l8_14_2_1b_bis; Col.
    apply perp_col0 with A1 A2; assert_diffs; Col.
  }
Qed.

End existential_playfair_rah.