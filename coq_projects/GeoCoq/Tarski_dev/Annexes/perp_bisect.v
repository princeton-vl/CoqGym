Require Export GeoCoq.Tarski_dev.Ch10_line_reflexivity_2.

Section PerpBisect_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_bisect_equiv_def :
  forall P Q A B, Perp_bisect P Q A B <-> Perp_bisect_bis P Q A B.
Proof.
intros; unfold Perp_bisect; unfold Perp_bisect_bis; unfold ReflectL; split.

  {
  intro H; destruct H as [[[X [HMid HCol]] HPerp] HDiff].
  exists X; split; Midpoint.
  elim HPerp; clear HPerp; intro HPerp; intuition.
  apply l8_14_2_1b_bis; assert_cols; Col; Perp.
  }

  {
  intro H; destruct H as [I [HPerp HMid]].
  assert_diffs; split; Col.
  split; try (left; apply l8_14_2_1a with I); Perp.
  exists I; split; Midpoint.
  unfold Perp_at in *; spliter; Col.
  }
Qed.

Lemma perp_bisect_sym_1 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect Q P A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_2 :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp_bisect P Q B A.
Proof.
intros.
apply perp_bisect_equiv_def in H.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
elim H;intros.
exists x.
intuition; Perp.
Qed.

Lemma perp_bisect_sym_3 : forall A B C D,
 Perp_bisect A B C D ->
 Perp_bisect B A D C.
Proof.
intros.
apply perp_bisect_sym_1.
apply perp_bisect_sym_2.
trivial.
Qed.

Lemma perp_bisect_perp :
 forall P Q A B,
  Perp_bisect P Q A B ->
  Perp P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
decompose [and ex] H;clear H.
unfold Perp.
exists x.
assumption.
Qed.

End PerpBisect_1.

Hint Resolve perp_bisect_perp : perp.

Section PerpBisect_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_bisect_cong_1 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong P A P B).
apply (per_double_cong P I A B);
eauto with perp.
Cong.
Qed.

Lemma perp_bisect_cong_2 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A Q B Q.
Proof.
intros.
apply perp_bisect_equiv_def in H.
unfold Perp_bisect_bis in *.
elim H;intros I;intros;clear H.
decompose [and] H0;clear H0.
assert (Cong Q A Q B).
apply (per_double_cong Q I A B);
eauto with perp.
Cong.
Qed.

End PerpBisect_2.

Hint Resolve perp_bisect_cong_1 perp_bisect_cong_2 : cong.

Section PerpBisect_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_bisect_cong2 :
 forall P Q A B,
 Perp_bisect P Q A B ->
 Cong A P B P /\ Cong A Q B Q.
Proof.
intros.
split.
eauto using perp_bisect_cong_1.
eauto using perp_bisect_cong_2.
Qed.

Lemma perp_bisect_cong :
 forall A A1 B B1 C C1 O: Tpoint,
 ~ Col A B C ->
 Perp_bisect O A1 B C -> Perp_bisect O B1 A C -> Perp_bisect O C1 A B ->
 Cong A O B O -> Cong B O C O ->
 Cong A O C O.
Proof.
intros.
apply (cong_transitivity A O B O C O); assumption.
Qed.

Lemma cong_cop_perp_bisect :
 forall P Q A B,
 P <> Q -> A <> B ->
 Coplanar P Q A B ->
 Cong A P B P ->
 Cong A Q B Q ->
 Perp_bisect P Q A B.
Proof.
intros.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis.
elim (midpoint_existence A B).
intros I HI.
exists I.
split;try assumption.
assert (Per P I A)
 by (unfold Per;exists B;eCong).

show_distinct A I.
unfold Midpoint in *.
spliter.
treat_equalities.
intuition.

show_distinct B I.
unfold Midpoint in *.
spliter.
treat_equalities.
intuition.

induction(eq_dec_points P I).
subst.
eapply l8_13_2;Col.
exists Q. exists B;repeat split;Col.
unfold Per.
exists A.
split.
Midpoint.
Cong.

eapply l8_13_2.
assumption.
assumption.

apply col_permutation_2.
apply cop_per2__col with A; Col.
destruct(col_dec B A P).
exists I.
left.
split; ColR.
apply coplanar_perm_12, col_cop__cop with B; Col; Cop.
exists B; split; Cong.

apply midpoint_col;auto.
exists P.
exists A.
repeat split;Col.
Qed.

Lemma perp_bisect_is_on_perp_bisect :
 forall A B C P,
  Is_on_perp_bisect P A B ->
  Is_on_perp_bisect P B C ->
  Is_on_perp_bisect P A C.
Proof.
intros.
unfold Is_on_perp_bisect in *.
eCong.
Qed.

Lemma perp_mid_perp_bisect : forall A B C D,
 Midpoint C A B -> Perp C D A B ->
 Perp_bisect C D A B.
Proof with finish.
intros.
apply perp_bisect_equiv_def.
unfold Perp_bisect_bis in *.
exists C...
split...
assert_cols; apply l8_14_2_1b_bis...
Qed.

Lemma cong_cop2_perp_bisect_col : forall A B C D E,
  Coplanar A C D E ->
  Coplanar B C D E ->
  Cong C D C E ->
  Perp_bisect A B D E ->
  Col A B C.
Proof.
intros A B C D E HCop1 HCop2 HCong1 HPerp.
assert (HCong2 := HPerp); apply perp_bisect_cong2 in HCong2; destruct HCong2 as [HCong2 Hc]; clear Hc.
apply perp_bisect_equiv_def in HPerp.
destruct HPerp as [F [HPerp [HBet HCong3]]].
assert (HDE : D <> E) by (assert_diffs; auto).
assert (HCol := HPerp); apply perp_in_col in HCol; destruct HCol as [HCol Hc]; clear Hc.
apply l8_14_2_1a in HPerp.
elim (eq_dec_points A C); intro; try (subst; Col).
apply cop_perp2__col with D E; Perp; Cop.
apply perp_bisect_perp; apply cong_cop_perp_bisect; Cong.
Qed.

Lemma perp_bisect_cop2_existence : forall A B C,
  A <> B -> exists P, exists Q, Perp_bisect P Q A B /\ Coplanar A B C P /\ Coplanar A B C Q.
Proof.
intros A B C HDiff.
destruct (midpoint_existence A B) as [M HM].
destruct (ex_perp_cop A B M C HDiff) as [Q []].
exists M; exists Q; unfold Perp_bisect.
repeat split; Cop.
  exists M; split; Col; Midpoint.
  left; Perp.
Qed.

Lemma perp_bisect_existence :
  forall A B, A <> B -> exists P, exists Q, Perp_bisect P Q A B.
Proof.
intros A B HDiff.
destruct (perp_bisect_cop2_existence A B A HDiff) as [P [Q []]].
exists P; exists Q; assumption.
Qed.

Lemma perp_bisect_existence_cop : forall A B C,
  A <> B -> exists P, exists Q, Perp_bisect P Q A B /\ Coplanar A B C P /\
                                Coplanar A B C Q.
Proof.
intros A B C HDiff.
destruct (midpoint_existence A B) as [M HM].
destruct (ex_perp_cop A B M C) as [Q [HQ HCop]]; auto.
exists M; exists Q; unfold Perp_bisect.
split.

  {
  split; Col.
  split; Perp.
  exists M; split; Col; Midpoint.
  }

  {
  split; auto.
  assert (Coplanar A B Q M) by Cop.
  apply perp_not_col2 in HQ.
  elim HQ; clear HQ; intro; [CopR|].
  assert_cols; exfalso; Col.
  }
Qed.

End PerpBisect_3.

Section PerpBisect_2D.

Context `{T2D:Tarski_2D}.

Lemma cong_perp_bisect :
 forall P Q A B,
 P <> Q -> A <> B ->
 Cong A P B P ->
 Cong A Q B Q ->
 Perp_bisect P Q A B.
Proof.
intros P Q A B HPQ HAB.
assert (HCop := all_coplanar P Q A B).
apply cong_cop_perp_bisect; assumption.
Qed.

Lemma cong_perp_bisect_col : forall A B C D E,
  Cong C D C E ->
  Perp_bisect A B D E ->
  Col A B C.
Proof.
intros A B C D E.
apply cong_cop2_perp_bisect_col; apply all_coplanar.
Qed.

End PerpBisect_2D.