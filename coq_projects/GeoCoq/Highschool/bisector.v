Require Export GeoCoq.Tarski_dev.Ch13_1.
Require Export GeoCoq.Highschool.triangles.

Section Bisector.

Context `{TE:Tarski_euclidean}.

(** Existence of the interior bisector of an angle. *)

Lemma bisector_existence : forall A B C,  A <> B -> B <> C ->
exists E,  InAngle E A B C /\ CongA A B E E B C.
Proof.
intros A B C HAB HBC.
destruct (col_dec A B C) as [HCOL | HNCOL].
(*case 1: Out B A C*)
destruct (out_dec B A C) as [HOUT | HNOUT].
exists C.
split.
apply (out_in_angle A B C C);auto.
apply (l6_6 B A C);auto.
apply (l11_21_b A B C C B C);auto.
apply (out_trivial B C);auto.
(*Case 2 Bet A B C*)
assert (Bet A B C) by(apply (not_out_bet A B C);auto).
destruct (perp_exists B A C) as [E HPerp].
intro HEQAC.
subst.
elim HAB.
apply (between_identity C B); auto.
exists E.
split.
unfold InAngle.
repeat split.
assert_diffs;auto.
assert_diffs; auto.
assert_diffs;auto.
exists B.
split;auto.
assert (Perp B E A B) by (apply (perp_col1 B E A C B);auto;Col).
assert (Perp B E C B) by (apply (perp_col1 B E C A B);assert_diffs;auto;Perp;Col).
assert (Per E B A) by (apply (perp_per_1 B E A);assert_diffs;auto;assumption).
assert (Per E B C) by (apply (perp_per_2 B E C);assert_diffs;auto;Perp;Perp).
assert (CongA E B A E B C) by (apply (l11_16 E B A E B C);auto;assert_diffs;auto; assert_diffs;auto).
CongA.
(*case 3: ~ Col A B C. *)
destruct (segment_construction B A B C ) as [C'[ HC'1 HC'2]].
destruct (segment_construction B C B A ) as [A' [HA'1 HA'2]].
destruct (midpoint_existence A' C') as [I HI].
assert (Cong B C' A' B) by (apply l2_11 with A C;Cong;Between).
assert_diffs.
assert (CongA A' C' B C' A' B).
 {
 apply  (isosceles_conga C' B A');auto.
 {
 intro.
 subst.
 treat_equalities.
 assert_cols.
 apply HNCOL.
  ColR. }
  unfold isosceles. Cong.
 }
unfold Midpoint in *;Cong.
destruct HI as [HBET HCONG].
assert (HTRI : Cong I B I B /\ (I <> B -> CongA C' I B A' I B /\ CongA C' B I A' B I)).
{ apply  (l11_49 I C' B I A' B).
 apply (out_conga A' C' B C' A' B I B I B);auto.
 apply (l6_6 C' I A');auto.
 apply (bet_out C' I A'); auto.
 assert_diffs.
 intro.
 subst;treat_equalities.
 elim H6; auto.
 assert_diffs;auto.
 Between.
 apply (out_trivial C' B);auto.
 apply (l6_6 A' I C');auto.
 apply (bet_out A' I C'); auto.
 assert_diffs.
 intro; subst;treat_equalities.
 elim H6; auto.
 assert_diffs;auto.
 apply (out_trivial A' B); auto.
 Cong.
 Cong. 
}
exists I.
destruct HTRI as [HCONGIB HIBO].
assert (I <> B) by (intro;elim HNCOL;ColR).
assert (CongA A B I I B C).
{ apply (out_conga C' B I I B A' A I I C).
  apply (conga_right_comm C' B I A' B I).
  apply HIBO;auto.
  apply (l6_6 B A C').
  apply (bet_out B A C').
  intuition.
  assumption.
  apply (out_trivial B I);auto.
  apply (out_trivial B I);auto.
  apply (l6_6 B C A').
  apply (bet_out B C A').
  intuition.
  assumption.
}
split.
unfold InAngle.
repeat split.
assert_diffs;auto.
assert_diffs;auto.
assumption.
destruct (inner_pasch A' B C' I A) as [x1 HIN1].
apply (midpoint_bet A' I C');auto.
split;auto.
Between.
destruct HIN1 as [HIN11 HIN12].
destruct (inner_pasch A B A' x1 C) as [x2 HIN2];auto.
exists x2.
destruct HIN2 as [HIN21 HIN22].
split.
apply (Bet_cases A x2 C).
right;auto.
right.
apply (bet_out B x2 I).
intro.
elim HNCOL;ColR.
bet.
assumption.
Qed.

Lemma not_col_bfoot_not_equality : forall A B C I H1 H2, ~ Col A B C -> Coplanar A B C I ->
Col A B H1 -> Col B C H2 -> CongA A B I I B C->
Perp A B I H1 -> Perp B C I H2 -> H1 <> B /\ H2 <> B.
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOL1 HCOL2 HCONGA HORTHA HORTHC.
split.
intro.
subst.
assert (Per A B I) by (apply (perp_per_1 B A I);auto;assert_diffs;auto;Perp).
assert (Col A C B).
{  apply cop_per2__col with I;Cop.
  assert_diffs;auto.
  apply (l8_2 I B C);auto.
  apply (l11_17 A B I I B C);auto. }
elim HNCOL;Col.
intro;subst.
assert (Per C B I) by (apply (perp_per_1 B C I);auto;assert_diffs;auto).
assert (Per I B C) by (apply (l8_2 C B I);auto).
assert (Col A C B).
{ apply cop_per2__col with I;Cop.
  assert_diffs; auto.
 apply (l11_17 I B C A B I);auto.
 CongA. }
elim HNCOL; Col.
Qed.

Lemma bisector_foot_out_out : forall A B C I H1 H2, ~ Col A B C ->
Coplanar A B C I -> Col A B H1 -> Col B C H2-> CongA A B I I B C->
Perp A B I H1 -> Perp B C I H2 -> (Out B H1 A -> Out B H2 C).
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOL1 HCOL2 HCONGA HORTHA HORTHC HOUT1.
destruct (not_col_bfoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
assert (Acute H1 B I). 
{ apply (perp_out_acute H1 B I H1);auto. 
  apply (out_trivial B H1);auto.
  apply (perp_col2 A B H1 B I H1);auto.
  Col. }
assert (CongA H1 B I I B C).
{ apply (out_conga A B I I B C H1 I I C);auto.
  apply (l6_6 B H1 A);auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (out_trivial B C);auto.
  assert_diffs;auto. }
assert (Acute I B C) by (apply (acute_conga__acute H1 B I I B C);auto).
apply (acute_col_perp__out I B C H2);auto.
Qed.

Lemma not_col_efoot_not_equality : forall A B C I H1 H2, ~ Col A B C -> Coplanar A B C I ->
Col A B H1 -> Col B C H2-> Cong I H1 I H2->
Perp A B I H1 -> Perp B C I H2 -> H1 <> B /\ H2 <> B.
Proof.
intros A B C I H1 H2 HNCOL HCOP HCOLH1 HCOLH2 HCONG HPERH1 HPERH2.
assert (H1 <> B).
intro.
subst.
assert (H2 <> B).
{  intro.
  subst.
  assert (Col B A C).
   apply (cop_perp2__col B A C I B);auto.
  Cop.
  Perp.
  elim HNCOL.
  Col.
}
assert (Perp B H2 I H2).
  apply (perp_col B C I H2 H2);auto.
assert (Per B H2 I).
{  apply (perp_per_1 H2 B I);auto.
   Perp.
}
assert (Per H2 B I).
{
  apply (l11_17 B H2 I H2 B I);auto.
  apply (isosceles_conga H2 I B);auto.
  assert_diffs;auto.
  unfold isosceles;Cong.
}
assert (H2 = B).
{
  apply (l8_7 I H2 B);auto.
  apply (l8_2 B H2 I);auto.
  apply (l8_2 H2 B I);auto.
}
contradiction.
split;auto.
intro.
subst.
assert (Perp B H1 I H1) by (apply (perp_col B A I H1 H1);auto;Perp;Col).
assert (Per B H1 I) by (apply (perp_per_1 H1 B I);auto;Perp).
assert (Per H1 B I).
{
  apply (l11_17 B H1 I H1 B I);auto.
  apply (isosceles_conga H1 I B);auto.
  assert_diffs;auto.
  unfold isosceles;Cong.
}
assert (H1 = B).
{
  apply (l8_7 I H1 B);auto.
  apply (l8_2 B H1 I);auto.
  apply (l8_2 H1 B I);auto.
}
contradiction.
Qed.

End Bisector.


Ltac col_with_conga := 
match goal with
   | H: (CongA ?A ?B ?I ?I ?B ?C) |- Col ?A ?B ?C => 
      assert (Col A B I) by (assert_diffs;ColR); assert (HH : Col I B C) by (apply (col_conga_col A B I I B C);assumption);
      assert_diffs;ColR
   | H :(CongA ?A ?B ?I ?C ?B ?I) |- Col ?A ?B ?C => 
      assert (CongA A B I I B C) by (apply (conga_right_comm A B I C B I);assumption); col_with_conga
   | H :(CongA ?I ?B ?A ?I ?B ?C) |- Col ?A ?B ?C => 
      assert (CongA A B I I B C) by (apply (conga_left_comm I B A I B C);assumption); col_with_conga
   | H :(CongA ?I ?B ?A ?C ?B ?I) |- Col ?A ?B ?C => 
      assert (CongA A B I C B I) by (apply (conga_left_comm I B A C B I);assumption); col_with_conga
   | H :(CongA ?I ?B ?C ?A ?B ?I) |- Col ?A ?B ?C =>
      assert (CongA A B I I B C) by (apply (conga_sym I B C A B I);assumption); col_with_conga
   | H :(CongA ?C ?B ?I ?A ?B ?I) |- Col ?A ?B ?C =>
      assert (CongA A B I C B I) by (apply (conga_sym C B I A B I);assumption); col_with_conga
   | H :(CongA ?I ?B ?C ?I ?B ?A) |- Col ?A ?B ?C =>
      assert (CongA I B A I B C) by (apply (conga_sym I B C I B A);assumption); col_with_conga
   | H: (CongA ?C ?B ?I ?I ?B ?A) |- Col ?A ?B ?C =>
      assert (CongA I B A C B I) by (apply (conga_sym C B I I B A);assumption); col_with_conga
   | H: (CongA ?A ?B ?I ?I ?B ?C) |- Col ?C ?B ?A => 
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?A ?B ?I ?C ?B ?I) |- Col ?C ?B ?A => 
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?I ?B ?A ?I ?B ?C) |- Col ?C ?B ?A => 
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?I ?B ?A ?C ?B ?I) |- Col ?C ?B ?A => 
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?I ?B ?C ?A ?B ?I) |- Col ?C ?B ?A =>
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?C ?B ?I ?A ?B ?I) |- Col ?C ?B ?A =>
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H :(CongA ?I ?B ?C ?I ?B ?A) |- Col ?C ?B ?A =>
      apply (col_permutation_3 A B C);auto;col_with_conga
   | H: (CongA ?C ?B ?I ?I ?B ?A) |- Col ?C ?B ?A =>
      apply (col_permutation_3 A B C);auto;col_with_conga
end.

Section Bisector_2.

Context `{TE:Tarski_euclidean}.

Lemma equality_foot_out_out : forall A B C I H1 H2, 
 ~ Col A B C -> InAngle I A B C ->
 Col A B H1 -> Col B C H2-> Cong I H1 I H2->
 Perp A B I H1 -> Perp B C I H2 -> 
 (Out B H1 A -> Out B H2 C).
Proof.
intros A B C I H1 H2 HNCOL HINANGLE HCOLH1 HCOLH2 HCONG HPERH1 HPERH2 HOUTH1.
destruct (not_col_efoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
 Cop.
assert(HMY : Cong H1 B H2 B /\ CongA H1 B I H2 B I /\ CongA H1 I B H2 I B).
{  apply (l11_52 B H1 I B H2 I).
   apply (l11_16 B H1 I B H2 I).
   apply (perp_per_1 H1 B I).
   assert_diffs;auto.
   assert (Perp B H1 I H1) by (apply (perp_col B A I H1 H1);auto;Perp;Col).
   Perp.
   assert_diffs;auto.
   assert_diffs;auto.
   apply (perp_per_1 H2 B I).
   assert_diffs;auto.
   assert (Perp B H2 I H2) by (apply (perp_col B C I H2 H2);auto;Perp;Col).
   Perp.
   assert_diffs;auto.
   assert_diffs;auto.
   Cong.
   Cong.
   assert_diffs.
   apply (l11_46 B H1 I); auto.
   left.
   apply (perp_per_1 H1 B I).
   assert_diffs;auto.
   assert (Perp B H1 I H1) by (apply (perp_col B A I H1 H1);auto;Perp;Col).
   Perp.  }
destruct HMY as [HSH1BH2B [HAH1BI HAH1IB]].
assert (TS I B A C).
{  apply (in_angle_two_sides A B C I);auto.
   intro.
   assert (Col H1 B H2) by (col_with_conga).
   elim HNCOL; ColR.
   intro.
   assert (Col H2 B H1) by (col_with_conga).
   elim HNCOL;ColR. }
destruct (conga_cop__or_out_ts I B H1 H2) as [HOUTH1H2 | HTSH1H2].
assert_diffs.
apply coplanar_perm_2, col_cop__cop with C; Col.
apply coplanar_perm_5, col_cop__cop with A; Col; Cop.
CongA.
elim HNCOL;ColR.
assert (TS I B A H2) by (apply (l9_5 I B H1 H2 B A);auto;Col).
assert (OS I B H2 C).
{ apply (l9_8_1 I B H2 C A);auto.
 apply (l9_2 I B A H2);auto.
 apply (l9_2 I B A C);auto. }
apply (col_one_side_out B I H2 C);auto.
Col.
apply (invert_one_side I B H2 C);auto.
Qed.

(** The points on the bisector of an angle are at equal distances of the two sides. *)

Lemma bisector_perp_equality : forall A B C I H1 H2, Coplanar A B C I ->
 Col B H1 A -> Col B H2 C ->
 Perp A B I H1 -> Perp B C I H2 ->
 CongA A B I I B C ->  Cong I H1 I H2.
Proof.
intros A B C I H1 H2 HCOP HCABH HCCBH HPH1 HPH2 HCONGA.
destruct (col_dec A B C) as [HCOL | HNCOL].
assert (Perp A B I H2) by(apply (perp_col2 B C A B I H2);auto;assert_diffs;auto;Col;Col).
assert (H1 = H2).
{ apply (l8_14_2_1b H1 A B I H1 H2);auto.
 apply (l8_14_2_1b_bis A B I H1 H1);auto.
 Col.
 Col.
 assert_diffs; ColR.
 assert (Perp I H1 A B) by (Perp).
 assert (Perp I H2 A B) by (Perp).
 assert (Col I H1 H2) by (apply (cop_perp2__col I H1 H2 A B); Cop).
 Col. }
subst;Cong.
(*for Col A B C End*)
destruct (not_col_bfoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
 Col.
 Col.
destruct (out_dec B H1 A) as [HOUT | HNOUT].
assert (Out B H2 C) by (apply (bisector_foot_out_out A B C I H1 H2);auto;Col;Col).
apply (l11_50_2 I B H1 I B H2).
{ intro.
  elim HNCOL.
  col_with_conga. }
{ apply (l11_16 B H1 I B H2 I);auto.
  apply (perp_per_1 H1 B I);auto.
  apply (perp_col2 A B H1 B I H1);auto.
  Col.
  Col.
  assert_diffs;auto.
  assert (Perp B H2 I H2) by (apply (perp_col B C I H2 H2);auto;Col).
  assert (Perp H2 B I H2) by (Perp).
  apply (perp_per_1 H2 B I);auto.
  assert_diffs;auto. }
assert (CongA H1 B I I B H2).
{ apply (out_conga A B I I B C H1 I I H2);auto.
  apply (l6_6 B H1 A);auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (l6_6 B H2 C);auto.
}
CongA.
Cong.

destruct (symmetric_point_construction A B) as [A' HCONHA'].
destruct (symmetric_point_construction C B) as [C' HCONHC'].
assert (Bet A B A') by (apply (midpoint_bet A B A');auto).
assert (Bet C B C') by (apply (midpoint_bet C B C');auto).
assert (Out B H1 A').
{
  assert (Bet A B H1).
   apply (not_out_bet A B H1);auto.
   Col.
  intro.
  elim HNOUT.
  apply (l6_6 B A H1);auto.
  apply (l6_3_2 H1 A' B);auto.
  repeat split.
  assert_diffs;auto.
  assert_diffs;auto.
  exists A.
  repeat split.
  assert_diffs;auto.
  Between.
  Between. }
assert (Out B H2 C').
{
  apply (bisector_foot_out_out A' B C' I H1 H2);auto.
  intro.
  elim HNCOL.
  assert_diffs;auto.
  ColR.
  assert_diffs.
  apply coplanar_perm_3, col_cop__cop with C; Col.
  apply coplanar_perm_19, col_cop__cop with A; Col; Cop.
  Col.
  assert_diffs;auto.
  ColR.
  apply (conga_right_comm A' B I C' B I);auto.
  apply (l11_13 A B I C B I A' C');auto.
  CongA.
  assert_diffs;auto.
  assert_diffs;auto.
  apply (perp_col2 A B A' B I H1);auto.
  assert_diffs;auto.
  Col.
  Col.
  apply (perp_col2 B C B C' I H2);auto.
  assert_diffs;auto.
  Col.
  Col. }
apply (l11_50_2 I B H1 I B H2).
{ intro;elim HNCOL.
  col_with_conga. }
assert (Per B H1 I).
{  apply (perp_per_1 H1 B I);auto.
   apply (perp_col2 A B H1 B I H1);auto.
   Col.
   Col. }
assert (Per B H2 I) by (apply (perp_per_1 H2 B I);auto;
    assert (Perp B H2 I H2) by (apply (perp_col B C I H2 H2);auto;Col);Perp).
apply (l11_16 B H1 I B H2 I);auto.
 assert_diffs;auto.
 assert_diffs;auto.
assert (CongA H1 B I I B H2).
{ apply (out_conga A' B I I B C' H1 I I H2);auto.
  assert (CongA A' B I C' B I) by (apply (l11_13 A B I C B I A' C');auto;
          CongA;assert_diffs;auto; assert_diffs;auto).
  CongA.
  apply (l6_6 B H1 A');auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (out_trivial B I);auto.
  assert_diffs;auto.
  apply (l6_6 B H2 C');auto. }
CongA.
Cong.
Qed.


(** The points which are at equal distance of the two side of an angle are on the bisector. *)

Lemma perp_equality_bisector : forall A B C I H1 H2,  ~ Col A B C ->
 InAngle I A B C -> Col B H1 A -> 
 Col B H2 C -> Perp A B I H1 -> Perp B C I H2 -> Cong I H1 I H2 ->
 CongA A B I I B C.
Proof.
intros A B C I H1 H2 HNCOL HINANGLE HCOLH1 HCOLH2 HPERPH1 HPERPH2 HCONG.
destruct (not_col_efoot_not_equality A B C I H1 H2) as [HNEQH1 HNEQH2];auto.
 Cop.
 Col.
 Col.
assert(HMY : Cong H1 B H2 B /\ CongA H1 B I H2 B I /\ CongA H1 I B H2 I B).
 apply (l11_52 B H1 I B H2 I).
{ apply (l11_16 B H1 I B H2 I).
  apply (perp_per_1 H1 B I).
  assert_diffs;auto.
  assert (Perp B H1 I H1) . ( apply (perp_col B A I H1 H1);auto;Perp;Col).
  Perp.
  assert_diffs;auto.
  assert_diffs;auto.
  apply (perp_per_1 H2 B I).
  assert_diffs;auto.
  assert (Perp B H2 I H2) by (apply (perp_col B C I H2 H2);auto;Perp;Col).
  Perp.
  assert_diffs;auto.
  assert_diffs;auto. }
Cong.
Cong.
{  assert_diffs.
   apply (l11_46 B H1 I); auto.
   left.
   apply (perp_per_1 H1 B I).
   assert_diffs;auto.
   assert (Perp B H1 I H1) by ( apply (perp_col B A I H1 H1);auto;Perp;Col).
   Perp. }
destruct HMY as [HSH1BH2B [HAH1BI HAH1IB]].
destruct (out_dec B A H1) as [HOUT | HBET].
assert (Out B H2 C) by (apply (equality_foot_out_out A B C I H1 H2);auto;Col;Col;apply (l6_6 B A H1);auto).
assert (CongA A B I C B I).
{ apply (out_conga H1 B I H2 B I A I C I);auto.
 apply (l6_6 B A H1);auto.
 apply (out_trivial B I);auto.
 assert_diffs;auto.
 apply (out_trivial B I);auto.
 assert_diffs;auto. }
CongA.
assert (~ Out B C H2).
{  intro.
   assert (Out B H1 A).
   { apply (equality_foot_out_out C B A I H2 H1);auto.
     intro.
     elim HNCOL;Col.
     apply (l11_24 I A B C);auto.
     Col.
     Col.
     Cong.
     Perp.
     Perp.
     apply (l6_6 B C H2);auto. }
  elim HBET.
  apply (l6_6 B H1 A);auto.  }
assert (Bet A B H1) by (apply (not_out_bet A B H1);auto;Col).
assert (Bet C B H2) by (apply (not_out_bet C B H2);auto;Col).
assert (CongA A B I C B I) by (apply (l11_13 H1 B I H2 B I A C);auto;
      Between;assert_diffs;auto;Between;assert_diffs;auto).
CongA.
Qed.

End Bisector_2.
