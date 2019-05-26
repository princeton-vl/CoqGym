Require Export GeoCoq.Tarski_dev.Ch09_plane.

Section Upper_dim.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition upper_dim_axiom := forall A B C P Q : Tpoint,
  P <> Q -> Cong A P A Q -> Cong B P B Q -> Cong C P C Q ->
  (Bet A B C \/ Bet B C A \/ Bet C A B).

Definition all_coplanar_axiom := forall A B C D, Coplanar A B C D.

Lemma upper_dim_implies_per2__col :
  upper_dim_axiom ->
  (forall A B C X, Per A X C -> X <> C -> Per B X C -> Col A B X).
Proof.
intros HUD A B C X HPer1 HDiff HPer2.
destruct HPer1 as [C' HPer1].
destruct HPer2 as [C'' HPer2].
assert (C' = C'') by (apply symmetric_point_uniqueness with C X; spliter; auto); treat_equalities.
unfold upper_dim_axiom in HUD.
spliter; assert_diffs; unfold Midpoint in *; spliter; apply HUD with C C'; Cong.
Qed.

Lemma upper_dim_implies_col_perp2__col :
  upper_dim_axiom ->
  (forall A B X Y P,
   Col A B P ->
   Perp A B X P ->
   Perp P A Y P ->
   Col Y X P).
Proof.
intro HUP; intros.
assert (P <> A).
eapply perp_not_eq_1.
apply H1.
eapply upper_dim_implies_per2__col; auto.
apply perp_in_per.
apply perp_in_sym.
apply perp_perp_in.
apply H1.
assumption.
apply perp_in_per.
apply perp_in_sym.
apply perp_perp_in.
apply perp_left_comm.
eapply perp_col.
auto.
apply H0.
assumption.
Qed.

Lemma upper_dim_implies_perp2__col :
  upper_dim_axiom ->
  (forall X Y Z A B,
   Perp X Y A B ->
   Perp X Z A B ->
   Col X Y Z).
Proof.
intro HUP; intros.
induction(col_dec A B X).
  induction(eq_dec_points X A).
    subst A.
    assert(X <> B).
      apply perp_distinct in H.
      spliter.
      assumption.
    apply perp_right_comm in H.
    apply perp_perp_in in H.
    apply perp_in_comm in H.
    apply perp_in_per in H.
    apply perp_right_comm in H0.
    apply perp_perp_in in H0.
    apply perp_in_comm in H0.
    apply perp_in_per in H0.
    apply col_permutation_2.
    eapply (upper_dim_implies_per2__col).
      assumption.
      apply H.
      assumption.
    assumption.
  assert(Perp A X X Y ).
    eapply perp_col.
      auto.
      apply perp_sym.
      apply H.
    assumption.
  assert(Perp A X X Z).
    eapply perp_col.
      auto.
      apply perp_sym.
      apply H0.
    assumption.
  apply col_permutation_2.
  apply upper_dim_implies_per2__col with A.
    assumption.
    apply perp_in_per.
    apply perp_in_comm.
    apply perp_perp_in.
    apply perp_sym.
    eapply perp_col.
      auto.
      apply perp_sym.
      apply H.
    assumption.
    assumption.
  apply perp_in_per.
  apply perp_in_comm.
  apply perp_perp_in.
  apply perp_sym.
  eapply perp_col.
    auto.
    apply perp_sym.
    apply H0.
  assumption.
assert(HH0:=H).
assert(HH1:=H0).
unfold Perp in H.
unfold Perp in H0.
ex_and H Y0.
ex_and H0 Z0.
assert(HH2:=H).
assert(HH3:=H2).
apply perp_in_col in H.
apply perp_in_col in H2.
spliter.
assert(Perp X Y0 A B).
  eapply perp_col.
    intro.
    subst Y0.
    contradiction.
    apply HH0.
  assumption.
assert(Perp X Z0 A B).
  eapply perp_col.
    intro.
    subst Z0.
    contradiction.
    apply HH1.
  assumption.
assert(Y0 = Z0).
  eapply l8_18_uniqueness.
    apply H1.
    assumption.
    apply perp_sym.
    assumption.
    assumption.
  apply perp_sym.
  assumption.
subst Z0.
eapply (col_transitivity_1 _ Y0).
  intro.
  subst Y0.
  contradiction.
  Col.
Col.
Qed.

Lemma upper_dim_implies_not_two_sides_one_side_aux :
  upper_dim_axiom ->
  (forall A B X Y PX,
   A <> B -> PX <> A ->
   Perp A B X PX ->
   Col A B PX ->
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
intro HUD; intros.
assert(exists P, exists T, Perp PX A P PX /\ Col PX A T /\ Bet Y T P).
apply l8_21.
assumption.
ex_elim H6 P.
ex_and H7 T.
assert(HH:= upper_dim_implies_col_perp2__col HUD A B X P PX H2 H1 H6).
assert(~Col P A B).
apply perp_not_col in H6.
intro.
apply H6.
ColR.
assert(TS PX A P Y).
repeat split.
intro.
apply H9.
ColR.
intro.
apply H4.
ColR.
exists T.
split.
apply col_permutation_2.
assumption.
apply between_symmetry.
assumption.
assert(X <> PX).
apply perp_not_eq_2 in H1.
assumption.
assert(P <> PX).
apply perp_not_eq_2 in H6.
assumption.
assert(HA:= (or_bet_out X PX P)).
induction HA.
assert(TS PX A P X).
repeat split; try assumption.
intro.
apply H9.
ColR.
intro.
apply H3.
ColR.
exists PX.
split.
apply col_trivial_1.
apply between_symmetry.
assumption.
eapply l9_8_1.
apply l9_2.
eapply (col_two_sides _ PX).
apply col_permutation_5.
assumption.
assumption.
apply invert_two_sides.
apply H14.
eapply (col_two_sides _ PX).
apply col_permutation_5.
assumption.
assumption.
apply invert_two_sides.
apply l9_2.
assumption.
induction H13.
assert(TS A B P Y).
eapply (col_two_sides _ PX).
Col.
assumption.
apply  invert_two_sides.
assumption.
assert(HO:= out_two_sides_two_sides A B X Y P PX (sym_not_eq H0) H2 H13 H14).
contradiction.
apply col_permutation_1 in HH.
contradiction.
Qed.

Lemma upper_dim_implies_not_two_sides_one_side :
  upper_dim_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ TS A B X Y ->
   OS A B X Y).
Proof.
    intro HUD; intros.
    assert (A <> B) by (intro; subst; Col).
    assert(exists PX, Col A B PX /\ Perp A B X PX).
      apply l8_18_existence.
      intro.
      apply H.
      apply col_permutation_2.
      assumption.
    ex_and H3 PX.
    induction(eq_dec_points PX A).
      subst PX.
      apply invert_one_side.
      eapply (upper_dim_implies_not_two_sides_one_side_aux HUD _ _ _ _ A); auto.
        apply perp_left_comm.
        assumption.
        Col.
        intro.
        apply H.
        Col.
        intro.
        apply H0.
        Col.
      intro.
      apply H1.
      apply invert_two_sides.
      assumption.
    apply (upper_dim_implies_not_two_sides_one_side_aux HUD _ _ _ _ PX); auto.
Qed.

Lemma upper_dim_implies_not_one_side_two_sides :
  upper_dim_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   ~ OS A B X Y ->
   TS A B X Y).
Proof.
    intro HUD; intros.
    intros.
    induction(two_sides_dec A B X Y).
      assumption.
    apply upper_dim_implies_not_two_sides_one_side in H2; try assumption.
    contradiction.
Qed.

Lemma upper_dim_implies_one_or_two_sides :
  upper_dim_axiom ->
  (forall A B X Y,
   ~ Col X A B ->
   ~ Col Y A B ->
   TS A B X Y \/ OS A B X Y).
Proof.
intro HUD; intros.
induction(two_sides_dec A B X Y).
left.
assumption.
right.
apply upper_dim_implies_not_two_sides_one_side in H1; try assumption.
Qed.

Lemma upper_dim_implies_all_coplanar : upper_dim_axiom -> all_coplanar_axiom.
Proof.
intro HUD; unfold all_coplanar_axiom; intros.
elim (col_dec A B C); Cop; intro HABC.
elim (col_dec A B D); Cop; intro HABD.
elim (col_dec A C D); Cop; intro HACD.
elim (upper_dim_implies_one_or_two_sides HUD A B C D); Col;
elim (upper_dim_implies_one_or_two_sides HUD A C B D); Col.

  {
  intros HTS1 HTS2; destruct HTS1 as [Hc1 [Hc2 [I [HCol HBet]]]].
  clear Hc1; clear Hc2; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS HTS; destruct HTS as [Hc1 [Hc2 [I [HCol HBet]]]].
  clear Hc1; clear Hc2; exists I; left; assert_cols; Col.
  }

  {
  intros HTS HOS; destruct HTS as [Hc1 [Hc2 [I [HCol HBet]]]].
  clear Hc1; clear Hc2; exists I; right; left; assert_cols; Col.
  }

  {
  intros HOS1 HOS2; destruct (l9_31 A B D C) as [Hc1 [Hc2 [I [HCol HBet]]]];
  try (apply one_side_symmetry; auto); clear Hc1; clear Hc2;
  exists I; right; right; assert_cols; Col.
  }
Qed.

Lemma all_coplanar_implies_upper_dim : all_coplanar_axiom -> upper_dim_axiom.
Proof.
intros HAC A B C P Q.
apply cong3_cop2__col; apply HAC.
Qed.

Lemma all_coplanar_upper_dim : all_coplanar_axiom <-> upper_dim_axiom.
Proof.
split;
try apply all_coplanar_implies_upper_dim;
apply upper_dim_implies_all_coplanar.
Qed.

Lemma upper_dim_stab : ~ ~ upper_dim_axiom -> upper_dim_axiom.
Proof.
  intros nnupper A B C P Q HPQ H1 H2 H3.
  destruct (col_dec A B C) as [|HNCol]; auto.
  exfalso.
  apply nnupper.
  intro upper.
  apply HNCol.
  apply upper with P Q; auto.
Qed.

End Upper_dim.