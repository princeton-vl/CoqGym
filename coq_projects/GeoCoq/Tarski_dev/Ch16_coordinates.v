Require Export GeoCoq.Tarski_dev.Ch15_lengths.

Section T16.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma grid_exchange_axes : forall O E S U1 U2,
  Cs O E S U1 U2 -> Cs O E S U2 U1.
Proof.
intros O E S U1 U2 HCs.
destruct HCs as [HDiff [HCong1 [HCong2 HPer]]].
repeat (split; Perp).
Qed.

(** Lemma 16.2 in dimension 2. *)

Lemma Cs_not_Col : forall O E S U1 U2, Cs O E S U1 U2 -> ~ Col U1 S U2.
Proof.
unfold Cs; intros O E S U1 U2 HCs.
spliter; assert_diffs; apply per_not_col; Perp.
Qed.

(** As we are in dimension 2, we skip 16.3
    which is only needed to prove 16.4 in dimension n. *)

(** Lemma 16.4 in dimension 2. *)
Lemma exists_grid : exists O E E' S U1 U2, ~ Col O E E' /\ Cs O E S U1 U2.
Proof.
destruct lower_dim_ex as [O [I [X HNC]]].
assert (H : ~ Col O I X) by auto; clear HNC; rename H into HNC.
assert_diffs; destruct (ex_per_cong I O O X O I) as [J HJ]; Col; spliter.
exists O; exists I; exists X; exists O; exists I; exists J.
repeat (split; finish).
Qed.

Lemma exists_grid_spec : exists S U1 U2, Cs PA PB S U1 U2.
Proof.
assert (~ Col PA PB PC) by (apply lower_dim).
assert_diffs.
destruct (ex_per_cong PB PA PA PC PA PB) as [J HJ]; Col; spliter.
exists PA; exists PB; exists J.
repeat (split; finish).
Qed.

Lemma coord_exchange_axes : forall O E S U1 U2 P X Y,
  Cd O E S U1 U2 P X Y -> Cd O E S U2 U1 P Y X.
Proof.
intros O E S U1 U2 P X Y HCd.
destruct HCd as [HCs [H [HPX HPY]]]; clear H.
split; try (apply grid_exchange_axes; auto).
split; try apply all_coplanar.
split; auto.
Qed.

(** Lemma 16.6 in dimension 2. *)
Lemma Cd_Col : forall O E S U1 U2 P X Y,
  Cd O E S U1 U2 P X Y -> Col O E X /\ Col O E Y.
Proof.
unfold Cd; unfold Projp; intros O E S U1 U2 P X Y HCd.
destruct HCd as [HCs [HC [[PX HPX] [PY HPY]]]]; clear HC.
destruct HPX as [[HDiff1 HElim1] HCong1]; destruct HPY as [[HDiff2 HElim2] HCong2].
split; [apply l4_13 with S U1 PX|apply l4_13 with S U2 PY]; Cong;
[induction HElim1|induction HElim2]; spliter; treat_equalities; Col.
Qed.

Lemma exists_projp : forall A B P, A <> B -> exists P', Projp P P' A B.
Proof.
intros A B P HAB.
elim (col_dec A B P); intro HNC; [exists P; split; Col; right|].
destruct (l8_18_existence A B P HNC) as [P' HP'].
exists P'; split; Col.
Qed.

Lemma exists_coord : forall O E S U P,
  S <> U -> Cong O E S U ->
  exists PX, exists X, Projp P PX S U /\ Cong_3 O E X S U PX.
Proof.
intros O E S U P HSU HCong.
destruct (exists_projp S U P HSU) as [PX Hprojp].
assert (HCol : Col S U PX)
  by (destruct Hprojp as [H' H]; induction H; spliter; treat_equalities; Col).
destruct (l4_14 S U PX O E) as [X HCong']; Cong.
exists PX; exists X; auto with cong.
Qed.

(** Lemma 16.7 in dimension 2. *)
Lemma coordinates_of_point : forall O E S U1 U2 P,
  Cs O E S U1 U2 -> exists X, exists Y, Cd O E S U1 U2 P X Y.
Proof.
intros O E S U1 U2 P HCs.
assert (H := HCs); destruct H as [HDiff [HCong1 [HCong2 H]]]; clear H.
assert (HSU1 : S <> U1) by (assert_diffs; auto).
assert (HSU2 : S <> U2) by (assert_diffs; auto).
destruct (exists_coord O E S U1 P HSU1 HCong1) as [PX [X HX]].
destruct (exists_coord O E S U2 P HSU2 HCong2) as [PY [Y HY]].
exists X; exists Y; split; auto.
split; try (apply all_coplanar).
split; [exists PX|exists PY]; auto.
Qed.

Lemma point_of_coordinates_origin : forall O E S U1 U2,
  Cs O E S U1 U2 -> Cd O E S U1 U2 S O O.
Proof.
intros O E S U1 U2 HCs.
split; auto.
split; try apply all_coplanar.
destruct HCs as [HDiff [HCong1 [HCong2 H]]]; clear H.
assert_diffs; split; exists S; repeat (split; Col; Cong).
Qed.

Lemma point_of_coordinates_on_an_axis : forall O E S U1 U2 X,
  Cs O E S U1 U2 -> Col O E X -> O <> X -> exists P, Cd O E S U1 U2 P X O.
Proof.
intros O E S U1 U2 X HCs HCol HOX.
assert (H := HCs); destruct H as [HDiff [HCong1 [HCong2 H]]]; clear H.
destruct (l4_14 O E X S U1 HCol HCong1) as [P HP].
exists P; split; auto.
destruct HCs as [H [H' [H'' HPer]]]; clear H; clear H'; clear H''.
split; try apply all_coplanar.
assert_diffs; split; [exists P|exists S]; repeat (split; Cong);
[right; split; try apply l4_13 with O E X; Col|].
left; split; Col.
apply per_perp in HPer; auto.
apply perp_col0 with S U1; Col; Perp;
[unfold Cong_3 in *; spliter; assert_diffs|apply l4_13 with O E X]; Col.
Qed.

Lemma point_of_coordinates : forall O E S U1 U2 X Y,
  Cs O E S U1 U2 -> Col O E X -> Col O E Y -> exists P, Cd O E S U1 U2 P X Y.
Proof.
intros O E S U1 U2 X Y HCs HCol1 HCol2.
elim (eq_dec_points O X); intro HOX; elim (eq_dec_points O Y); intro HOY;
treat_equalities; [exists S; apply point_of_coordinates_origin|
                   destruct (point_of_coordinates_on_an_axis O E S U2 U1 Y) as [P HP];
                   try apply grid_exchange_axes;
                   try (exists P; apply coord_exchange_axes)|
                   apply point_of_coordinates_on_an_axis|]; auto.
assert (H := HCs); destruct H as [HDiff [HCong1 [HCong2 H]]]; clear H.
destruct (l4_14 O E X S U1 HCol1 HCong1) as [PX HPX].
destruct (l4_14 O E Y S U2 HCol2 HCong2) as [PY HPY].
destruct (perp_exists PX S U1) as [PX' HPerp1]; [assert_diffs; auto|].
destruct (perp_exists PY S U2) as [PY' HPerp2]; [assert_diffs; auto|].
assert (HPerp3 : Perp PX PX' PY PY').
  {
  apply par_perp__perp with S U2; Perp.
  apply l12_9_2D with S U1; Perp.
  destruct HCs as [H [H' [H'' HPer]]]; clear H; clear H'; clear H''.
  assert_diffs; apply per_perp in HPer; Perp.
  }
assert (H := HPerp3); destruct H as [P HP]; exists P; split; auto.
split; try apply all_coplanar.
split; [exists PX|exists PY]; split; Cong.

  {
  assert_diffs; split; auto.
  left; split; [apply l4_13 with O E X; Col|].
  unfold Perp_at in *; spliter; apply perp_col0 with PX PX'; Col.
  assert (HPYS : PY <> S) by (unfold Cong_3 in *; spliter; assert_diffs; auto).
  intro; treat_equalities; apply HPYS.
  apply l6_21 with S U1 U2 S; Col;
  [destruct HCs as [H' [H'' [H''' HPer]]]; apply perp_not_col;
   assert_diffs; apply per_perp in HPer; Perp|
  |apply l4_13 with E O Y; try apply cong_3_swap; Col].
  assert (HPar : Par S U1 PY PY')
    by (apply l12_9_2D with P PX'; Perp).
  elim HPar; clear HPar; intro HParS; [|spliter; ColR].
  exfalso; apply HParS; exists P; split; Col.
  apply l4_13 with X O E; try (apply cong_3_swap; apply cong_3_swap_2); Col.
  }

  {
  assert_diffs; split; auto.
  left; split; [apply l4_13 with O E Y; Col|].
  unfold Perp_at in *; spliter; apply perp_col0 with PY PY'; Col.
  assert (HPXS : PX <> S) by (unfold Cong_3 in *; spliter; assert_diffs; auto).
  intro; treat_equalities; apply HPXS.
  apply l6_21 with S U2 U1 S; Col;
  [destruct HCs as [H' [H'' [H''' HPer]]]; apply perp_not_col;
   assert_diffs; apply per_perp in HPer; Perp|
  |apply l4_13 with E O X; try apply cong_3_swap; Col].
  assert (HPar : Par S U2 PX PX')
    by (apply l12_9_2D with P PY'; Perp).
  elim HPar; clear HPar; intro HParS; [|spliter; ColR].
  exfalso; apply HParS; exists P; split; Col.
  apply l4_13 with Y O E; try (apply cong_3_swap; apply cong_3_swap_2); Col.
  }
Qed.

Lemma eq_points_coordinates : forall O E S U1 U2 P1 X1 Y1 P2 X2 Y2,
  Cd O E S U1 U2 P1 X1 Y1 -> Cd O E S U1 U2 P2 X2 Y2 ->
  (P1 = P2 <-> (X1 = X2 /\ Y1 = Y2)).
Proof.
intros O E S U1 U2 P1 X1 Y1 P2 X2 Y2 HCd1 HCd2.
split; intro; spliter; treat_equalities.

  {
  destruct HCd1 as [HCs [H [[PX HPX1] [PY HPY1]]]]; clear H.
  destruct HCd2 as [H [H' [[PX2 HPX2] [PY2 HPY2]]]]; clear H; clear H'.
  assert (PX = PX2) by (spliter; apply projp_id with P1 S U1; auto); treat_equalities;
  assert (PY = PY2) by (spliter; apply projp_id with P1 S U2; auto); treat_equalities.
  destruct HPX1 as [H HCong1]; assert (H' : Col PX S U1)
    by (destruct H as [H' H]; induction H; spliter; treat_equalities; Col).
  clear H; assert (HCol1 : Col O E X1) by (apply l4_13 with S U1 PX; Col; Cong).
  clear H'; destruct HPX2 as [H HCong3]; clear H.
  destruct HPY1 as [H HCong2]; assert (H' : Col PY S U2)
    by (destruct H as [H' H]; induction H; spliter; treat_equalities; Col).
  clear H; assert (HCol2 : Col O E Y1) by (apply l4_13 with S U2 PY; Col; Cong).
  clear H'; destruct HPY2 as [H HCong4]; clear H.
  split; apply l4_18 with O E; Col;
  try (intro; treat_equalities; unfold Cs in HCs; spliter; intuition);
  unfold Cong_3 in *; spliter; eapply cong_transitivity; eCong.
  }

  {
  destruct HCd1 as [HCs [H [[PX HPX1] [PY HPY1]]]]; clear H.
  destruct HCd2 as [H [H' [[PX2 HPX2] [PY2 HPY2]]]]; clear H; clear H'.
  assert (PX = PX2); treat_equalities.
    {
    destruct HPX1 as [[H HElim] H0]; unfold Cs in HCs; unfold Cong_3 in *;
    spliter; assert_diffs; apply l4_18 with S U1; auto.
    induction HElim; spliter; treat_equalities; Col.
    apply cong_transitivity with O X1; Cong.
    apply cong_transitivity with E X1; Cong.
    }
  assert (PY = PY2); treat_equalities.
    {
    destruct HPY1 as [[H HElim] H0]; unfold Cs in HCs; unfold Cong_3 in *;
    spliter; assert_diffs; apply l4_18 with S U2; auto.
    induction HElim; spliter; treat_equalities; Col.
    apply cong_transitivity with O Y1; Cong.
    apply cong_transitivity with E Y1; Cong.
    }
  destruct HPX1 as [HProjp1 H]; clear H; destruct HPX2 as [HProjp2 H]; clear H;
  destruct HPY1 as [HProjp3 H]; clear H; destruct HPY2 as [HProjp4 H]; clear H.
  assert (HCol1 : Col PX P1 P2) by (apply projp2_col with S U1; auto).
  assert (HCol2 : Col PY P1 P2) by (apply projp2_col with S U2; auto).
  elim (eq_dec_points P1 P2); intro HP1P2; treat_equalities; auto; exfalso.
  assert (HPar : Par S U1 S U2).
    {
    elim (eq_dec_points P1 PX); intro HP1PX;
    elim (eq_dec_points P1 PY); intro HP1PY; treat_equalities.

      {
      destruct HProjp2 as [H H1]; clear H; elim H1; clear H1; intro H1;
      [destruct H1 as [H1 HPerp1]|spliter; intuition].
      destruct HProjp4 as [H H2]; clear H; elim H2; clear H2; intro H2;
      [destruct H2 as [H2 HPerp2]|spliter; intuition].
      apply l12_9_2D with P2 P1; Perp.
      }

      {
      destruct HProjp2 as [H H1]; clear H; elim H1; clear H1; intro H1;
      [destruct H1 as [H1 HPerp1]|spliter; intuition].
      destruct HProjp3 as [H H2]; clear H; elim H2; clear H2; intro H2;
      [destruct H2 as [H2 HPerp2]|spliter; intuition].
      apply l12_9_2D with P2 P1; Perp.
      apply perp_col0 with P1 PY; Perp; Col.
      }

      {
      destruct HProjp1 as [H H1]; clear H; elim H1; clear H1; intro H1;
      [destruct H1 as [H1 HPerp1]|spliter; intuition].
      destruct HProjp4 as [H H2]; clear H; elim H2; clear H2; intro H2;
      [destruct H2 as [H2 HPerp2]|spliter; intuition].
      apply l12_9_2D with P2 P1; Perp.
      apply perp_col0 with P1 PX; Perp; Col.
      }

      {
      destruct HProjp1 as [H H1]; clear H; elim H1; clear H1; intro H1;
      [destruct H1 as [H1 HPerp1]|spliter; intuition].
      destruct HProjp3 as [H H2]; clear H; elim H2; clear H2; intro H2;
      [destruct H2 as [H2 HPerp2]|spliter; intuition].
      apply l12_9_2D with P2 P1;
      [apply perp_col0 with P1 PX|apply perp_col0 with P1 PY];Perp; Col.
      }
    }
  assert (HFalse : ~ ~ Col U1 S U2).
    {
    intro HF; apply HF;
    elim HPar; clear HPar; intro HPar; spliter; Col.
    exfalso; apply HPar; exists S; Col.
    }
  unfold Cs in HCs; spliter; assert_diffs; apply HFalse; apply per_not_col; Col.
  }
Qed.

(** As we are in dimension 2, we skip 16.8 which is only needed to prove 16.11 in dimension n. *)
Lemma l16_9_1 : forall O E E' X Y XY XMY,
  Col O E X -> Col O E Y -> Is_length O E E' X Y XY ->
  LeP O E E' Y X -> Diff O E E' X Y XMY ->
  XY = XMY.
Proof.
intros O E E' X Y XY XMY HCol1 HCol2 HXY HLe1 HXMY.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HXMY; unfold Ar2 in *; spliter; Col).
assert (HOE : O <> E) by (assert_diffs; auto).
assert (HCol3 : Col O E XMY).
  {
  unfold Diff, Opp, Sum, Ar2 in *;
  destruct HXMY as [MB [H1 [H2 [H3 H4]]]];
  spliter; Col.
  }
assert (HCong1 := HXMY); apply diff_sum in HCong1; apply l15_3 in HCong1.
elim HXY; clear HXY; intro HXY; [|spliter; intuition].
destruct HXY as [H [HCol4 [HLe2 HCong2]]].
elim (l7_20 O XY XMY); [auto|intro HMid; clear H|ColR|apply cong_transitivity with X Y; Cong].
elim HLe1; clear HLe1; intro HLt1; [clear HCong1|treat_equalities; auto].
elim HLe2; clear HLe2; intro HLt2; [clear HCong2|treat_equalities; auto].
exfalso; apply not_pos_and_neg with O E XMY;
split; [apply lt_diff_ps with E' X Y; auto|].
apply pos_opp_neg with E' XY; [apply ltP_pos with E'; auto|].
apply midpoint_opp; repeat (Col; split).
Qed.

Lemma length_eq_or_opp : forall O E E' A B L1 L2,
  Length O E E' A B L1 -> Diff O E E' A B L2 -> L1 = L2 \/ Opp O E E' L1 L2.
Proof.
intros O E E' A B L1 L2 HL1 HL2.
assert (HNC : ~ Col O E E') by (apply diff_ar2 in HL2; unfold Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (apply diff_ar2 in HL2; unfold Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (apply diff_ar2 in HL2; unfold Ar2 in *; spliter; Col).
elim (col_2_le_or_ge O E E' A B); auto; intro HLe;
[right|left; apply l16_9_1 with O E E' A B; auto; left; auto].
apply diff_opp with B A; auto.
destruct (diff_exists O E E' B A) as [D HD]; Col.
assert (L1 = D)
  by (apply l16_9_1 with O E E' B A; auto; left; apply length_sym; auto).
treat_equalities; auto.
Qed.

Lemma l16_9_2 : forall O E E' X Y XY XMY XY2 XMY2,
  Col O E X -> Col O E Y -> Is_length O E E' X Y XY ->
  Diff O E E' X Y XMY -> Prod O E E' XY XY XY2 -> Prod O E E' XMY XMY XMY2 ->
  XY2 = XMY2.
Proof.
intros O E E' X Y XY XMY XY2 XMY2 HCol1 HCol2 HXY HXMY HXY2 HXMY2.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HXMY; unfold Ar2 in *; spliter; Col).
assert (H:= HXY); elim H; clear H; intro HXY'; [|spliter; assert_diffs; intuition].
elim (length_eq_or_opp O E E' X Y XY XMY); auto; intro HOpp1; treat_equalities;
apply prod_uniqueness with O E E' XY XY; auto.
destruct (opp_exists O E E' HNC E) as [ME HOpp2]; Col.
apply prod_assoc1 with XMY ME XMY; auto; [|apply prod_comm];
apply opp_prod;auto; apply opp_comm; Col.
Qed.

(** Lemma 16.10 for k  = 2. *)
Lemma cong_3_2_cong_4 : forall O E I J S U X Y,
  O <> E -> Col O E I -> Col O E J ->
  Cong_3 O E I S U X -> Cong_3 O E J S U Y ->
  Cong_4 O E I J S U X Y.
Proof.
intros O E I J S U X Y HOE HCol1 HCol2 HCong1 HCong4.
destruct HCong1 as [HCong1 [HCong2 HCong3]].
destruct HCong4 as [HCong4 [HCong5 HCong6]].
repeat (split; Cong).
apply l4_16 with O E S U; Col.
repeat (split; Cong).
Qed.

(** Lemma 16.10 for k  = 3. *)
Lemma cong_3_3_cong_5: forall O E I J K S U X Y Z,
  O <> E -> Col O E I -> Col O E J -> Col O E K ->
  Cong_3 O E I S U X -> Cong_3 O E J S U Y -> Cong_3 O E K S U Z ->
  Cong_5 O E I J K S U X Y Z.
Proof.
intros O E I J K S U X Y Z HOE HCol1 HCol2 HCol3 HCong1 HCong4 HCong7.
destruct HCong1 as [HCong1 [HCong2 HCong3]].
destruct HCong4 as [HCong4 [HCong5 HCong6]].
destruct HCong7 as [HCong7 [HCong8 HCong9]].
repeat (split; Cong);
apply l4_16 with O E S U; Col; repeat (split; Cong).
Qed.

Lemma square_distance_formula_aux : forall O E E' S U1 U2 P PX PY Q QX PXQX,
  Cd O E S U1 U2 P PX PY -> Cd O E S U1 U2 Q QX PY ->
  P <> Q -> ~ Col O E E' -> Col O E PX -> Col O E QX -> Col O E PY ->
  Cs O E S U1 U2 -> Length O E E' PX QX PXQX ->
  Length O E E' Q P PXQX.
Proof.
intros O E E' S U1 U2 P PX PY Q QX PXQX.
intros HCd1 HCd2 HDiff  HNC HCol1 HCol2 HCol3 HCs HPXQX.
apply length_eq_cong_2 with PX QX; auto; clear HPXQX.
destruct HCd1 as [H [H' [HPX' HPY']]]; clear H; clear H'.
destruct HPX' as [PX' [HProjp1 HCong1]]; destruct HPY' as [PY' [HProjp2 HCong2]].
destruct HCd2 as [H [H' [HQX' HQY']]]; clear H; clear H'.
destruct HQX' as [QX' [HProjp3 HCong3]]; destruct HQY' as [QY' [HProjp4 HCong4]].
assert (PY' = QY')
  by (assert_diffs; apply col_cong_3_cong_3_eq with O E PY S U2; auto).
treat_equalities;
assert (HPerp1 : Perp P Q S U2) by (apply projp_projp_perp with PY'; auto).
assert (HPerp2 : Perp U1 S S U2)
  by (unfold Cs in HCs; spliter; assert_diffs; apply per_perp; Perp).
destruct HProjp1 as [H H1]; clear H; destruct HProjp3 as [H H2]; clear H.
elim H1; clear H1; intro H1; elim H2; clear H2; intro H2;
destruct H1 as [HCol5 HPerp3]; destruct H2 as [HCol6 HPerp4]; treat_equalities.

  {
  elim (eq_dec_points S PX'); intro HDiff1;
  elim (eq_dec_points S QX'); intro HDiff2; treat_equalities.

    {
    exfalso; unfold Cong_3 in *; spliter; treat_equalities.
    assert (HPar1 : Par P Q S U1)
      by (apply l12_9_2D with S U2; Perp).
    assert (HPar2 : Par P S Q S)
      by (apply l12_9_2D with S U1; Perp).
    elim HPar2; clear HPar2; intro HCol1; [apply HCol1; exists S; Col|].
    elim HPar1; clear HPar1; intro HCol2; [apply HCol2; exists S; spliter; Col|].
    spliter; apply perp_not_col2 in HPerp3;
    elim HPerp3; intro HNC'; apply HNC'; Col.
    }

    {
    assert (O = PX) by (unfold Cong_3 in HCong1; spliter; treat_equalities; auto).
    treat_equalities; assert (HCol7 : Col S U2 P).
      {
      assert (H : Par P S S U2)
        by (apply l12_9_2D with S U1; Perp).
      elim H; clear H; intro H; [exfalso; apply H; exists S|spliter]; Col.
      }
    assert (HNC' : ~ Col S U1 U2) by (apply perp_not_col; Perp).
    assert (H : Rectangle P S QX' Q).
      {
      apply perp3__rect; try (intro; assert_diffs; apply HNC'; ColR);
      [apply perp_col0 with S U1|apply perp_sym; apply perp_col0 with S U1|];
      Col; Perp.
      apply perp_sym; apply par_perp__perp with S U1; Perp.
      apply l12_9_2D with S U2; Perp.
      }
    apply Rectangle_Plg in H; apply plg_to_parallelogram in H;
    apply plg_cong_2 in H.
    unfold Cong_3 in HCong3; spliter; apply cong_transitivity with S QX'; Cong.
    }

    {
    assert (O = QX) by (unfold Cong_3 in HCong3; spliter; treat_equalities; auto).
    treat_equalities; assert (HCol7 : Col S U2 Q).
      {
      assert (H : Par Q S S U2)
        by (apply l12_9_2D with S U1; Perp).
      elim H; clear H; intro H; [exfalso; apply H; exists S|spliter]; Col.
      }
    assert (HNC' : ~ Col S U1 U2) by (apply perp_not_col; Perp).
    assert (H : Rectangle Q S PX' P).
      {
      apply perp3__rect; try (intro; assert_diffs; apply HNC'; ColR);
      [apply perp_col0 with S U1|apply perp_sym; apply perp_col0 with S U1|];
      Col; Perp.
      apply perp_sym; apply par_perp__perp with S U1; Perp.
      apply l12_9_2D with S U2; Perp.
      }
    apply Rectangle_Plg in H; apply plg_to_parallelogram in H;
    apply plg_cong_2 in H.
    unfold Cong_3 in HCong1; spliter; apply cong_transitivity with S PX'; Cong.
    }

    {
    elim (eq_dec_points S PY'); intro HDiff3; treat_equalities.

      {
      assert (HNC' := HPerp3); apply perp_not_col2 in HNC'.
      elim HNC'; clear HNC'; intro HNC'; [exfalso; apply HNC'|intuition].
      destruct HProjp2 as [H' H]; clear H'.
      elim H; clear H; intro H; [|spliter; subst; Col].
      destruct H as [H HPerp5]; clear H.
      assert (HPar : Par P S S U1)
        by (apply l12_9_2D with S U2; Perp).
      elim HPar; clear HPar; intro HPar;
      [exfalso; apply HPar; exists S|spliter]; Col.
      }

      {
      assert (HNC' : ~ Col S U1 U2) by (apply perp_not_col; Perp).
      assert (HCol7 : Col S U1 PX') by (apply l4_13 with O E PX; Col).
      assert (HCol8 : Col S U2 PY') by (apply l4_13 with O E PY; Col).
      assert (HCol9 : Col S U1 QX') by (apply l4_13 with O E QX; Col).
      assert (HDiff4 : P <> PY').
        {
        intro; treat_equalities; apply HDiff1.
        assert_diffs; apply l6_21 with S U1 U2 S; Col.
        assert (HPar : Par P PX' S U2)
          by (apply l12_9_2D with S U1; Perp).
        elim HPar; clear HPar; intro HPar;
        [exfalso; apply HPar; exists P|]; spliter; Col.
        }
      assert (HDiff5 : Q <> PY').
        {
        intro; treat_equalities; apply HDiff2.
        assert_diffs; apply l6_21 with S U1 U2 S; Col.
        assert (HPar : Par Q QX' S U2)
          by (apply l12_9_2D with S U1; Perp).
        elim HPar; clear HPar; intro HPar;
        [exfalso; apply HPar; exists Q|]; spliter; Col.
        }
      assert (HRect1 : Rectangle PX' S PY' P).
        {
        apply perp3__rect; try (intro; assert_diffs; apply HNC'; ColR).

          {
          apply perp_col0 with S U2; Col.
          apply perp_col0 with S U1; Col; Perp.
          }

          {
          apply perp_col0 with P Q; try (apply perp_col0 with S U2); Col; Perp.
          apply col_permutation_1; apply projp2_col with S U2; auto.
          }

          {
          apply par_perp__perp with S U1; Perp.
          apply l12_9_2D with S U2; Perp.
          apply perp_sym; apply perp_col0 with P Q; Col.
          apply col_permutation_1; apply projp2_col with S U2; auto.
          }
        }
      assert (HRect2 : Rectangle QX' S PY' Q).
        {
        apply perp3__rect; try (intro; assert_diffs; apply HNC'; ColR).

          {
          apply perp_col0 with S U2; Col.
          apply perp_col0 with S U1; Col; Perp.
          }

          {
          apply perp_col0 with P Q; try (apply perp_col0 with S U2); Col; Perp.
          apply col_permutation_1; apply projp2_col with S U2; auto.
          }

          {
          apply par_perp__perp with S U1; Perp.
          apply l12_9_2D with S U2; Perp.
          apply perp_sym; apply perp_col0 with P Q; Col.
          apply col_permutation_1; apply projp2_col with S U2; auto.
          }
        }
      assert (HRect3 : Rectangle P PX' QX' Q)
        by (apply rect_2_rect with S PY'; try apply rect_permut; auto).
      apply Rectangle_Parallelogram in HRect3; apply plg_cong_2 in HRect3.
      assert_diffs;
      apply cong_3_2_cong_4 with O E PX QX S U1 PX' QX' in HCong1; Col.
      unfold Cong_4 in HCong1; spliter; apply cong_transitivity with PX' QX'; Cong.
      }
    }
  }

  {
  exfalso; elim (perp_not_col2 S U1 P PX'); Perp; intro H; apply H; Col; clear H.
  assert (HPar : Par P Q S U1) by (apply l12_9_2D with S U2; Perp).
  elim HPar; clear HPar; intro HPar; spliter; Col.
  exfalso; apply HPar; exists Q; Col.
  }

  {
  exfalso; elim (perp_not_col2 S U1 Q QX'); Perp; intro H; apply H; Col; clear H.
  assert (HPar : Par P Q S U1) by (apply l12_9_2D with S U2; Perp).
  elim HPar; clear HPar; intro HPar; spliter; Col.
  exfalso; apply HPar; exists P; Col.
  }

  {
  assert (Cong_4 O E PX QX S U1 P Q) by (assert_diffs; apply cong_3_2_cong_4; Col).
  unfold Cong_4 in *; spliter; Cong.
  }
Qed.

Lemma square_distance_formula :
  forall O E E' S U1 U2 P Q PX PY QX QY PQ PQ2 PXMQX PYMQY PXMQX2 PYMQY2 F,
  Cd O E S U1 U2 P PX PY -> Cd O E S U1 U2 Q QX QY -> Is_length O E E' P Q PQ ->
  Prod O E E' PQ PQ PQ2 -> Diff O E E' PX QX PXMQX ->
  Prod O E E' PXMQX PXMQX PXMQX2 -> Diff O E E' PY QY PYMQY ->
  Prod O E E' PYMQY PYMQY PYMQY2 -> Sum O E E' PXMQX2 PYMQY2 F ->
  PQ2 = F.
Proof.
intros O E E' S U1 U2 P Q PX PY QX QY PQ PQ2 PXMQX PYMQY PXMQX2 PYMQY2 F.
intros HCd1 HCd2 HPQ HPQ2 HPXMQX HPXMQX2 HPYMQY HPYMQY2 HF.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HPXMQX; unfold Ar2 in *; spliter; Col).
assert (HCol1 : Col O E PX) by (apply Cd_Col in HCd1; spliter; Col).
assert (HCol2 : Col O E QX) by (apply Cd_Col in HCd2; spliter; Col).
assert (HCol3 : Col O E PY) by (apply Cd_Col in HCd1; spliter; Col).
assert (HCol4 : Col O E QY) by (apply Cd_Col in HCd2; spliter; Col).
destruct (is_length_exists O E E' PX QX) as [PXQX HPXQX]; Col.
assert (HCol5 : Col O E PXQX).
  {
  unfold Is_length, Length in HPXQX; induction HPXQX; spliter; treat_equalities; Col.
  }
destruct (prod_exists O E E' HNC PXQX PXQX) as [PXQX2 HPXQX2]; Col.
assert (PXQX2 = PXMQX2) by (apply l16_9_2 with O E E' PX QX PXQX PXMQX; Col).
destruct (is_length_exists O E E' PY QY) as [PYQY HPYQY]; Col.
assert (HCol6 : Col O E PYQY).
  {
  unfold Is_length, Length in HPYQY; induction HPYQY; spliter; treat_equalities; Col.
  }
destruct (prod_exists O E E' HNC PYQY PYQY) as [PYQY2 HPYQY2]; Col.
assert (PYQY2 = PYMQY2) by (apply l16_9_2 with O E E' PY QY PYQY PYMQY; Col).
treat_equalities; apply sum_uniqueness with O E E' PXQX2 PYQY2; auto; clear HF; clear F.
clear HPXMQX2; clear HPXMQX; clear PXMQX; clear HPYMQY2; clear HPYMQY; clear PYMQY.
assert (HCs : Cs O E S U1 U2) by (unfold Cd in HCd1; spliter; auto).
destruct (point_of_coordinates O E S U1 U2 PX QY) as [R HCd3]; Col.
elim HPQ; clear HPQ; intro HPQ; [|spliter; treat_equalities; exfalso; Col].
elim HPXQX; clear HPXQX; intro HPXQX; [|spliter; treat_equalities; exfalso; Col].
elim HPYQY; clear HPYQY; intro HPYQY; [|spliter; treat_equalities; exfalso; Col].
elim (eq_dec_points P R); intro HPR; [assert (HPR' := HPR);
rewrite eq_points_coordinates in HPR; [|apply HCd1|apply HCd3]|];
elim (eq_dec_points Q R); intro HQR; [assert (HQR' := HQR);
rewrite eq_points_coordinates in HQR; [|apply HCd2|apply HCd3]| |assert (HQR' := HQR);
rewrite eq_points_coordinates in HQR; [|apply HCd2|apply HCd3]|];
apply sum_comm; Col; apply pythagoras with P Q R PYQY PXQX PQ; auto; try intro;
try (destruct HPR as [HPX HPY]); try (destruct HQR as [HQX HQY]);
treat_equalities; Col; Perp; clear HPYQY2; clear HPXQX2; clear HPQ2; clear HPQ;
try clear HPX; try clear HPY; try clear HQX; try clear HQY.

  {
  assert (O = PYQY); treat_equalities.
    {
    assert_diffs; apply length_uniqueness with O E E' PY PY; try apply length_id_2; auto.
    }
  assert_diffs; apply length_id_2; auto.
  }

  {
  assert (O = PXQX); treat_equalities.
    {
    assert_diffs; apply length_uniqueness with O E E' QX QX; try apply length_id_2; auto.
    }
  assert_diffs; apply length_id_2; auto.
  }

  {
  assert (O = PYQY); treat_equalities.
    {
    assert_diffs; apply length_uniqueness with O E E' PY PY; try apply length_id_2; auto.
    }
  assert_diffs; apply length_id_2; auto.
  }

  {
  apply square_distance_formula_aux with S U1 U2 PX PY QX; auto.
  }

  {
  apply square_distance_formula_aux with S U2 U1 QY QX PY; auto;
  try apply coord_exchange_axes; auto; try apply grid_exchange_axes; auto.
  apply length_sym; auto.
  }

  {
  assert (O = PXQX); treat_equalities.
    {
    assert_diffs; apply length_uniqueness with O E E' QX QX; try apply length_id_2; auto.
    }
  assert_diffs; apply length_id_2; auto.
  }

  {
  destruct HCd3 as [H [H' [HRX HRY]]]; clear H; clear H';
  destruct HRX as [RX' [HProjp5 HCong5]]; destruct HRY as [RY' [HProjp6 HCong6]];
  destruct HCd1 as [H [H' [HPX HPY]]]; clear H; clear H';
  destruct HPX as [PX' [HProjp1 HCong1]]; destruct HPY as [PY' [HProjp2 HCong2]];
  assert (RX' = PX')
    by (assert_diffs; apply col_cong_3_cong_3_eq with O E PX S U1; Col); subst;
  treat_equalities; destruct HCd2 as [H [H' [HQX HQY]]]; clear H; clear H';
  destruct HQX as [QX' [HProjp3 HCong3]]; destruct HQY as [QY' [HProjp4 HCong4]];
  assert (RY' = QY')
    by (assert_diffs; apply col_cong_3_cong_3_eq with O E QY S U2; Col); subst;
  assert (HPerp1 : Perp P R S U1) by (apply projp_projp_perp with PX'; auto);
  assert (HPerp2 : Perp Q R S U2) by (apply projp_projp_perp with QY'; auto);
  assert (HPerp3 : Perp U1 S S U2)
    by (unfold Cs in HCs; spliter; assert_diffs; apply per_perp; Perp).
  apply perp_per_2; auto; apply perp_sym; apply par_perp__perp with S U1; Perp.
  apply l12_9_2D with S U2; Perp.
  }

  {
  apply square_distance_formula_aux with S U2 U1 QY PX PY; auto;
  try apply coord_exchange_axes; auto; try apply grid_exchange_axes; auto.
  apply length_sym; auto.
  }

  {
  apply length_sym.
  apply square_distance_formula_aux with S U1 U2 QX QY PX; auto.
  apply length_sym; auto.
  }
Qed.

(** Lemma 16.12 in dimension 2. *)
Lemma characterization_of_congruence :
  forall O E E' S U1 U2
         A AX AY B BX BY C CX CY D DX DY
         AXMBX AXMBX2 AYMBY AYMBY2 AB2
         CXMDX CXMDX2 CYMDY CYMDY2 CD2,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY ->
  Cd O E S U1 U2 C CX CY -> Cd O E S U1 U2 D DX DY ->
  Diff O E E' AX BX AXMBX -> Prod O E E' AXMBX AXMBX AXMBX2 ->
  Diff O E E' AY BY AYMBY -> Prod O E E' AYMBY AYMBY AYMBY2 ->
  Sum O E E' AXMBX2 AYMBY2 AB2 ->
  Diff O E E' CX DX CXMDX -> Prod O E E' CXMDX CXMDX CXMDX2 ->
  Diff O E E' CY DY CYMDY -> Prod O E E' CYMDY CYMDY CYMDY2 ->
  Sum O E E' CXMDX2 CYMDY2 CD2 ->
  (Cong A B C D <-> AB2 = CD2).
Proof.
intros O E E' S U1 U2 A AX AY B BX BY C CX CY D DX DY.
intros AXMBX AXMBX2 AYMBY AYMBY2 AB2' CXMDX CXMDX2 CYMDY CYMDY2 CD2'.
intros HCdA HCdB HCdC HCdD HAXMBX HAXMBX2 HAYMBY HAYMBY2 HAB2.
intros HCXMDX HCXMDX2 HCYMDY HCYMDY2 HCD2.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HAXMBX; unfold Ar2 in *; spliter; Col).
destruct (is_length_exists O E E' A B) as [AB HLengthAB]; Col.
assert (HColAB : Col O E AB).
  {
  unfold Is_length, Length in *; induction HLengthAB;
  spliter; treat_equalities; Col.
  }
destruct (prod_exists O E E' HNC AB AB) as [AB2 HLengthAB2]; Col.
assert (AB2 = AB2').
  {
  apply square_distance_formula with O E E' S U1 U2
                                     A B AX AY BX BY AB
                                     AXMBX AYMBY AXMBX2 AYMBY2; auto.
  }
treat_equalities; clear HAB2; clear HAYMBY2; clear HAYMBY;
clear HAXMBX2; clear HAXMBX; clear HCdA; clear HCdB.
destruct (is_length_exists O E E' C D) as [CD HLengthCD]; Col.
assert (HColCD : Col O E CD).
  {
  unfold Is_length, Length in *; induction HLengthCD;
  spliter; treat_equalities; Col.
  }
destruct (prod_exists O E E' HNC CD CD) as [CD2 HLengthCD2]; Col.
assert (CD2 = CD2').
  {
  apply square_distance_formula with O E E' S U1 U2
                                     C D CX CY DX DY CD
                                     CXMDX CYMDY CXMDX2 CYMDY2; auto.
  }
treat_equalities; clear HCD2; clear HCYMDY2; clear HCYMDY;
clear HCXMDX2; clear HCXMDX; clear HCdC; clear HCdD.
split; [intro HCong|intro; treat_equalities].

  {
  assert (H : Cong O AB O CD).
    {
    unfold Is_length, Length in *;
    induction HLengthAB; [|spliter; treat_equalities; exfalso; apply HNC; Col];
    induction HLengthCD; [|spliter; treat_equalities; exfalso; apply HNC; Col].
    spliter; apply cong_transitivity with A B; trivial.
    apply cong_transitivity with C D; Cong.
    }
  clear HLengthAB; clear HLengthCD; clear HCong; rename H into HCong.
  assert (H : Col O AB CD) by (assert_diffs; ColR).
  elim (l7_20 O AB CD); Col; clear H; clear HCong; intro HMid; treat_equalities.

    {
    apply prod_uniqueness with O E E' AB AB; auto.
    }

    {
    assert (HOpp1 : Opp O E E' AB CD)
      by (apply midpoint_opp; unfold Ar2; auto; repeat (split; Col)).
    clear HMid; destruct (opp_exists O E E' HNC E) as [ME HOpp2]; Col.
    assert (Prod O E E' AB ME CD) by (apply opp_prod; auto).
    assert (HXMY2' : Prod O E E' CD CD AB2).
      {
      apply prod_assoc1 with AB ME AB; auto.
      apply prod_assoc2 with ME AB E; try apply prod_1_l; Col; apply prod_comm; auto.
      apply opp_prod; auto; apply opp_comm; auto.
      }
    apply prod_uniqueness with O E E' CD CD; auto.
    }
  }

  {
  elim HLengthAB; clear HLengthAB; intro HLengthAB;
  [|spliter; treat_equalities; exfalso; apply HNC; Col].
  elim HLengthCD; clear HLengthCD; intro HLengthCD;
  [|spliter; treat_equalities; exfalso; apply HNC; Col].
  elim (eq_squares_eq_or_opp O E E' AB CD AB2); auto; intro HOpp; treat_equalities;
  [apply length_eq_cong_1 with O E E' AB; auto|].
  unfold Length, LeP, LtP in *; spliter; apply opp_midpoint in HOpp.
  unfold Midpoint in *; spliter.
  apply cong_transitivity with O CD; trivial.
  apply cong_transitivity with O AB; Cong.
  }
Qed.

Lemma bet_betCood_aux : forall O E S U1 U2 A AX AY B BX BY C CX CY,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY -> Cd O E S U1 U2 C CX CY ->
  Bet A B C ->
  Bet AX BX CX.
Proof.
intros O E S U1 U2 A AX AY B BX BY C CX CY HCdA HCdB HCdC HBet.
destruct (parallel_existence S U1 A) as [A1 [A2 [HDiff4 [HPar HCol]]]];
try (intro; unfold Cd, Cs in *; spliter; treat_equalities; intuition).
assert (HAX' := HCdA).
destruct HAX' as [H [H' [HAX' H'']]]; clear H; clear H'; clear H''.
destruct HAX' as [AX' [HProjpAX' HCongAX']].
assert (HA : Projp AX' A A1 A2).
  {
  split; auto; induction (eq_dec_points A AX');
  [treat_equalities; right|left; split]; Col.
  apply par_perp__perp with S U1; auto.
  destruct HProjpAX' as [Hclear HAX']; clear Hclear.
  induction HAX'; spliter; Perp; intuition.
  }
assert (HBX' := HCdB).
destruct HBX' as [H [H' [HBX' H'']]]; clear H; clear H'; clear H''.
destruct HBX' as [BX' [HProjpBX' HCongBX']].
destruct (exists_projp A1 A2 BX') as [BX'' HBX'']; auto.
assert (HCX' := HCdC).
destruct HCX' as [H [H' [HCX' H'']]]; clear H; clear H'; clear H''.
destruct HCX' as [CX' [HProjpCX' HCongCX']].
destruct (exists_projp A1 A2 CX') as [CX'' HCX'']; auto.
assert (HDiff : O <> E) by (unfold Cd, Cs in *; spliter; auto).
assert (HColAX : Col O E AX).
  {
  unfold Cd in *; destruct HCdA as [H [H' [[PX [HProjp HCong]] H'']]].
  apply projp_col in HProjp; apply l4_13 with S U1 PX; Cong.
  }
assert (HColBX : Col O E BX).
  {
  unfold Cd in *; destruct HCdB as [H [H' [[PX [HProjp HCong]] H'']]].
  apply projp_col in HProjp; apply l4_13 with S U1 PX; Cong.
  }
assert (HColCX : Col O E CX).
  {
  unfold Cd in *; destruct HCdC as [H [H' [[PX [HProjp HCong]] H'']]].
  apply projp_col in HProjp; apply l4_13 with S U1 PX; Cong.
  }
apply l4_6 with AX' BX' CX'.

  {
  apply projp_preserves_bet with A B C S U1; auto.
  }

  {
  assert (Cong_5 O E AX BX CX S U1 AX' BX' CX')
    by (apply cong_3_3_cong_5; assert_diffs; auto).
  unfold Cong_5 in *; spliter; repeat (split; Cong).
  }
Qed.

Lemma bet_betCood : forall O E S U1 U2 A AX AY B BX BY C CX CY,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY -> Cd O E S U1 U2 C CX CY ->
  Bet A B C ->
  Bet AX BX CX /\ Bet AY BY CY.
Proof.
intros O E S U1 U2 A AX AY B BX BY C CX CY HCdA HCdB HCdC HBet.
split; [apply bet_betCood_aux with O E S U1 U2 A AY B BY C CY|]; auto.
apply bet_betCood_aux with O E S U2 U1 A AX B BX C CX; auto;
apply coord_exchange_axes; auto.
Qed.

Lemma characterization_of_betweenness_aux : forall O E E' S U1 U2
                                                   A AX AY B BX BY C CX CY
                                                   BXMAX CXMAX AB AC IAC T,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY -> Cd O E S U1 U2 C CX CY ->
  ~ Col O E E' -> Col O E AX -> Col O E BX -> Col O E CX ->
  Col O E BXMAX -> Col O E CXMAX -> Col O E T ->
  Col O E AB -> Col O E AC -> Col O E IAC ->
  Diff O E E' BX AX BXMAX -> Diff O E E' CX AX CXMAX ->
  Length O E E' A B AB -> Length O E E' A C AC ->
  Prod O E E' T AC AB -> Prod O E E' IAC AC E ->
  Bet A B C -> A <> B -> A <> C -> B <> C ->
  Prod O E E' T CXMAX BXMAX.
Proof.
intros O E E' S U1 U2 A AX AY B BX BY C CX CY BXMAX CXMAX AB AC IAC T.
intros HCdA HCdB HCdC HNC HColAX HColBX HColCX HColBXMAX HColCXMAX HColT.
intros HColAB HColAC HColIAC HBXMAX HCXMAX HAB HAC HT HIAC HBet HDiff1 HDiff2 HDiff3.
destruct (parallel_existence S U1 A) as [A1 [A2 [HDiff4 [HPar HCol]]]];
try (intro; unfold Cd, Cs in *; spliter; treat_equalities; intuition).
assert (HAX' := HCdA).
destruct HAX' as [H [H' [HAX' H'']]]; clear H; clear H'; clear H''.
destruct HAX' as [AX' [HProjpAX' HCongAX']].
assert (HA : Projp AX' A A1 A2).
  {
  split; auto; induction (eq_dec_points A AX');
  [treat_equalities; right|left; split]; Col.
  apply par_perp__perp with S U1; auto.
  destruct HProjpAX' as [Hclear HAX']; clear Hclear.
  induction HAX'; spliter; Perp; intuition.
  }
assert (HBX' := HCdB).
destruct HBX' as [H [H' [HBX' H'']]]; clear H; clear H'; clear H''.
destruct HBX' as [BX' [HProjpBX' HCongBX']].
destruct (exists_projp A1 A2 BX') as [BX'' HBX'']; auto.
assert (HCX' := HCdC).
destruct HCX' as [H [H' [HCX' H'']]]; clear H; clear H'; clear H''.
destruct HCX' as [CX' [HProjpCX' HCongCX']].
destruct (exists_projp A1 A2 CX') as [CX'' HCX'']; auto.
elim (col_dec A B BX''); intro HABBX''.

  {
  elim (eq_dec_points A BX''); intro HABX''; treat_equalities.

    {
    assert (AX' = BX').
      {
      elim (line_dec S U1 A1 A2); intro HLine.

        {
        assert (A = AX') by (apply col_projp_eq with S U1;
                             auto; assert_diffs; spliter; ColR).
        treat_equalities; apply eq_sym; apply col_projp_eq with A1 A2; auto.
        assert (Col S U1 BX') by (apply projp_col with B; auto).
        assert_diffs; spliter; ColR.
        }

        {
        assert (HCol' : Col A AX' BX') by (apply projp2_col with A1 A2; auto).
        assert (HParS : Par_strict S U1 A1 A2); [|clear HLine].
          {
          elim (col_dec S U1 A1); intro HCol'';
          [apply par_not_col_strict with A2|apply par_not_col_strict with A1];
          Col ; try (intro; apply HLine); Col.
          }
        apply l6_21 with S U1 A AX'; Col;
        [| |apply l4_13 with O E AX|apply l4_13 with O E BX]; Col;
        intro; treat_equalities; apply HParS; exists A; split; Col;
        apply col_permutation_2; apply l4_13 with O E AX; Col.
        }
      }
    treat_equalities; assert (HPerp : Perp A C S U1).
      {
      assert (HCol' : Col AX' A B) by (apply projp2_col with S U1; auto).
      assert_cols; apply perp_sym; apply perp_col0 with A B;
      try apply projp_projp_perp with AX'; Col.
      }
    assert (AX' = CX') by (apply perp_projp2_eq with A C S U1; auto).
    treat_equalities; assert (AX = BX).
      {
      assert_diffs; apply col_cong_3_cong_3_eq with S U1 AX' O E; Cong.
      apply l4_13 with O E AX; auto.
      }
    assert (AX = CX).
      {
      assert_diffs; apply col_cong_3_cong_3_eq with S U1 AX' O E; Cong.
      apply l4_13 with O E AX; auto.
      }
    treat_equalities;
    assert (O = BXMAX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col);
    assert (O = CXMAX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col);
    treat_equalities; apply prod_0_r; unfold Prod, Ar2 in *; spliter; Col.
    }

    {
    assert (B = BX'').
      {
      apply col_par_projp2_eq with A1 A2 S U1 BX'; Par.
      assert (Col A1 A2 BX'') by (apply projp_col with BX'; auto); ColR.
      }
    assert (C = CX'').
      {
      apply col_par_projp2_eq with A1 A2 S U1 CX'; Par; assert_cols.
      assert (Col A1 A2 BX'') by (apply projp_col with BX'; auto); ColR.
      }
    treat_equalities.
    assert (HElim : LeP O E E' AX BX \/ LeP O E E' BX AX)
      by (apply col_2_le_or_ge; Col).
    elim HElim; clear HElim; intro HLe4.

      {
      destruct (length_existence O E E' B A) as [LAB HLAB]; Col.
      assert (LAXBX : Length O E E' BX AX LAB).
        {
        apply length_eq_cong_2 with B A; auto.
        assert (Cong AX BX AX' BX').
          {
          apply cong_3_2_cong_4 with O E AX BX S U1 AX' BX' in HCongBX';
          try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
          }
        assert (Cong A B AX' BX').
          {
          apply col_2_par_projp2_cong with S U1 A1 A2; auto;
          [apply projp_col with A|apply projp_col with B]; auto.
          }
        apply cong_transitivity with AX' BX'; Cong.
        }
      assert (LAB = BXMAX)
        by (apply l16_9_1 with O E E' BX AX; Col; left; auto).
      elim HLe4; clear HLe4; intro HLt; treat_equalities;
      [|assert (AX' = BX') by (apply col_cong_3_cong_3_eq with O E AX S U1;
                               try intro; treat_equalities; Col);
      treat_equalities;
      apply projp_id with AX' A B A1 A2 in HBX''; intuition].
      apply bet_lt12_le13 with O E E' AX BX CX in HLt;
      [|apply bet_betCood_aux with O E S U1 U2 A AY B BY C CY; auto].
      destruct (length_existence O E E' C A) as [LAC HLAC]; Col.
      assert (LAXCX : Length O E E' CX AX LAC).
        {
        apply length_eq_cong_2 with C A; auto.
        assert (Cong AX CX AX' CX').
          {
          apply cong_3_2_cong_4 with O E AX CX S U1 AX' CX' in HCongCX';
          try intro; treat_equalities; Col;
          unfold Cong_4 in *; spliter; Cong.
          }
        assert (Cong A C AX' CX').
          {
          apply col_2_par_projp2_cong with S U1 A1 A2; auto;
          [apply projp_col with A|apply projp_col with C]; auto.
          }
        apply cong_transitivity with AX' CX'; Cong.
        }
      assert (LAC = CXMAX)
        by (apply l16_9_1 with O E E' CX AX; Col; left; auto).
      assert (AB = LAB).
        {
        apply length_uniqueness with O E E' A B; auto;
        apply length_eq_cong_2 with B A; Cong.
        }
      assert (AC = LAC); treat_equalities.
        {
        apply length_uniqueness with O E E' A C; auto;
        apply length_eq_cong_2 with C A; Cong.
        }
      auto.
      }

      {
      destruct (length_existence O E E' A B) as [LAB HLAB]; Col.
      assert (LAXBX : Length O E E' AX BX LAB).
        {
        apply length_eq_cong_2 with A B; auto.
        assert (Cong AX BX AX' BX').
          {
          apply cong_3_2_cong_4 with O E AX BX S U1 AX' BX' in HCongBX';
          try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
          }
        assert (Cong A B AX' BX').
          {
          apply col_2_par_projp2_cong with S U1 A1 A2; auto;
          [apply projp_col with A|apply projp_col with B]; auto.
          }
        apply cong_transitivity with AX' BX'; Cong.
        }
      destruct (diff_exists O E E' AX BX) as [AXMBX HAXMBX]; Col.
      assert (LAB = AXMBX)
        by (apply l16_9_1 with O E E' AX BX; Col; left; auto).
      elim HLe4; clear HLe4; intro HLt; treat_equalities;
      [|assert (AX' = BX') by (apply col_cong_3_cong_3_eq with O E BX S U1;
                               try intro; treat_equalities; Col);
      treat_equalities;
      apply projp_id with AX' A B A1 A2 in HBX''; intuition].
      apply bet_lt21_le31 with O E E' AX BX CX in HLt;
      [|apply bet_betCood_aux with O E S U1 U2 A AY B BY C CY; auto].
      destruct (length_existence O E E' A C) as [LAC HLAC]; Col.
      assert (LAXCX : Length O E E' AX CX LAC).
        {
        apply length_eq_cong_2 with A C; auto.
        assert (Cong AX CX AX' CX').
          {
          apply cong_3_2_cong_4 with O E AX CX S U1 AX' CX' in HCongCX';
          try intro; treat_equalities; Col;
          unfold Cong_4 in *; spliter; Cong.
          }
        assert (Cong A C AX' CX').
          {
          apply col_2_par_projp2_cong with S U1 A1 A2; auto;
          [apply projp_col with A|apply projp_col with C]; auto.
          }
        apply cong_transitivity with AX' CX'; Cong.
        }
      destruct (diff_exists O E E' AX CX) as [AXMCX HAXMCX]; Col.
      assert (LAC = AXMCX)
        by (apply l16_9_1 with O E E' AX CX; Col; left; auto).
      treat_equalities.
      assert (Opp O E E' BXMAX LAB) by (apply diff_opp with BX AX; auto).
      assert (Opp O E E' CXMAX LAC) by (apply diff_opp with CX AX; auto).
      destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
      assert (AB = LAB) by (apply length_uniqueness with O E E' A B; auto).
      assert (AC = LAC) by (apply length_uniqueness with O E E' A C; auto).
      treat_equalities; apply prod_assoc2 with AC ME AB;
      [|apply opp_prod; auto; apply opp_comm|
       apply opp_prod; auto; apply opp_comm]; auto.
      }
    }
  }

  {
  destruct (length_existence O E E' A BX'') as [ABX'' HABX'']; Col.
  destruct (length_existence O E E' A CX'') as [ACX'' HACX'']; Col.
  assert (HColABX'' : Col O E ABX'').
    {
    destruct HABX'' as [H [H' [HElim H'']]]; clear H; clear H'; clear H''.
    elim HElim; clear HElim; intro HLt; treat_equalities; Col.
    destruct HLt as [D [HDiff H]]; clear H.
    apply diff_ar2 in HDiff; unfold Ar2 in *; spliter; Col.
    }
  assert (HColACX'' : Col O E ACX'').
    {
    destruct HACX'' as [H [H' [HElim H'']]]; clear H; clear H'; clear H''.
    elim HElim; clear HElim; intro HLt; treat_equalities; Col.
    destruct HLt as [D [HDiff H]]; clear H.
    apply diff_ar2 in HDiff; unfold Ar2 in *; spliter; Col.
    }
  destruct (prod_exists O E E' HNC AB ACX'') as [F HF]; Col.
  assert (HF' : Prodg O E E' ABX'' AC F).
    {
    apply thales with A B C BX'' CX'' AB ACX''; auto.

      {
      assert_diffs; auto.
      }

      {
      assert_cols; auto.
      }

      {
      apply projp_col in HBX''; apply projp_col in HCX''; ColR.
      }

      {
      destruct HBX'' as [H HElim1]; clear H;
      destruct HProjpBX' as [H HElim2]; clear H.
      destruct HCX'' as [H HElim3]; clear H;
      destruct HProjpCX' as [H HElim4]; clear H.
      elim HElim1; clear HElim1; intro H; destruct H as [HColBX'' HPerp1];
      elim HElim2; clear HElim2; intro H; destruct H as [HColBX' HPerp2];
      elim HElim3; clear HElim3; intro H; destruct H as [HColCX'' HPerp3];
      elim HElim4; clear HElim4; intro H; destruct H as [HColCX' HPerp4];
      treat_equalities.

        {
        assert (HCol1 : Par B BX' BX' BX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol1; clear HCol1; intro HCol1;
        [exfalso; apply HCol1; exists BX'; Col|].
        assert (HCol2 : Par C CX' CX' CX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol2; clear HCol2; intro HCol2;
        [exfalso; apply HCol2; exists CX'; Col|].
        left; apply l12_9_2D with A1 A2.

          {
          apply perp_sym; apply perp_col0 with BX' BX''; Perp;
          assert_diffs; spliter; Col.
          }

          {
          apply perp_sym; apply perp_col0 with CX' CX''; Perp;
          assert_diffs; spliter; Col.
          intro; treat_equalities; assert_cols; apply HABBX''; ColR.
          }
        }

        {
        assert (HCol1 : Par B BX' BX' BX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol1; clear HCol1; intro HCol1;
        [exfalso; apply HCol1; exists BX'; Col|].
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply perp_col0 with BX' BX''; Perp;
        assert_diffs; spliter; Col.
        }

        {
        assert (HCol1 : Par B BX' BX' BX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol1; clear HCol1; intro HCol1;
        [exfalso; apply HCol1; exists BX'; Col|].
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply perp_col0 with BX' BX''; Perp;
        assert_diffs; spliter; Col.
        apply perp_sym; apply par_perp__perp with S U1; Perp.
        }

        {
        right; auto.
        }

        {
        assert (HCol2 : Par C CX' CX' CX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol2; clear HCol2; intro HCol2;
        [exfalso; apply HCol2; exists CX'; Col|].
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply perp_col0 with CX' CX''; Perp;
        assert_diffs; spliter; Col.
        intro; treat_equalities; assert_cols; apply HABBX''; ColR.
        }

        {
        left; apply l12_9_2D with A1 A2; Perp; Perp.
        }

        {
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply par_perp__perp with S U1; Perp.
        }

        {
        right; auto.
        }

        {
        assert (HCol2 : Par C CX' CX' CX'')
          by (apply par_perp2__par with S U1 A1 A2; Perp).
        elim HCol2; clear HCol2; intro HCol2;
        [exfalso; apply HCol2; exists CX'; Col|].
        left; apply l12_9_2D with A1 A2; Perp.

          {
          apply perp_sym; apply par_perp__perp with S U1; Perp.
          }

          {
          apply perp_sym; apply perp_col0 with CX' CX''; Perp;
          assert_diffs; spliter; Col.
          intro; treat_equalities; assert_cols; apply HABBX''; ColR.
          }
        }

        {
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply par_perp__perp with S U1; Perp.
        }

        {
        left; apply l12_9_2D with A1 A2; Perp.
        apply perp_sym; apply par_perp__perp with S U1; Perp.
        apply perp_sym; apply par_perp__perp with S U1; Perp.
        }

        {
        right; auto.
        }

        {
        exfalso; apply HABBX''; Col.
        }

        {
        exfalso; apply HABBX''; Col.
        }

        {
        exfalso; apply HABBX''; Col.
        }

        {
        right; auto.
        }
      }

      {
      left; auto.
      }
    }
  elim HF'; clear HF'; intro HF'; [|destruct HF' as [HFalse H]; clear H;
                                    exfalso; apply HFalse; do 3 (split; Col)].
  assert (HProd : Prod O E E' T ACX'' ABX'').
    {
    assert (HColF : Col O E F) by (unfold Prod, Ar2 in *; spliter; Col).
    destruct (prod_exists O E E' HNC F IAC) as [G HG]; Col.
    assert (Prod O E E' ABX'' E G)
      by (apply prod_assoc2 with AC IAC F; auto; apply prod_comm; auto).
    assert (Prod O E E' ACX'' T G).
      {
      apply prod_assoc2 with AB IAC F; auto; apply prod_comm; auto.
      apply prod_assoc2 with AC T E; auto; apply prod_comm; auto.
      apply prod_1_r; Col.
      }
    assert (G = ABX'')
      by (apply prod_uniqueness with O E E' ABX'' E; auto; apply prod_1_r; Col).
    treat_equalities; apply prod_comm; auto.
    }
  assert (HElim : LeP O E E' AX BX \/ LeP O E E' BX AX)
    by (apply col_2_le_or_ge; Col).
  elim HElim; clear HElim; intro HLe4.

    {
    assert (LAXBX : Length O E E' BX AX ABX'').
      {
      apply length_eq_cong_2 with A BX''; auto.
      assert (Cong AX BX AX' BX').
        {
        apply cong_3_2_cong_4 with O E AX BX S U1 AX' BX' in HCongBX';
        try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
        }
      assert (Cong A BX'' AX' BX').
        {
        apply col_2_par_projp2_cong with S U1 A1 A2; auto;
        [apply projp_col with A|apply projp_col with B]; auto.
        }
      apply cong_transitivity with AX' BX'; Cong.
      }
    assert (ABX'' = BXMAX)
      by (apply l16_9_1 with O E E' BX AX; Col; left; auto).
    elim HLe4; clear HLe4; intro HLt; treat_equalities;
    [|assert (AX' = BX') by (apply col_cong_3_cong_3_eq with O E AX S U1;
                             try intro; treat_equalities; Col);
    treat_equalities;
    apply projp_id with AX' A BX'' A1 A2 in HBX''; auto;
    treat_equalities; exfalso; Col].
    apply bet_lt12_le13 with O E E' AX BX CX in HLt;
    [|apply bet_betCood_aux with O E S U1 U2 A AY B BY C CY; auto].
    assert (LAXCX : Length O E E' CX AX ACX'').
      {
      apply length_eq_cong_2 with A CX''; auto.
      assert (Cong AX CX AX' CX').
        {
        apply cong_3_2_cong_4 with O E AX CX S U1 AX' CX' in HCongCX';
        try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
        }
      assert (Cong A CX'' AX' CX').
        {
        apply col_2_par_projp2_cong with S U1 A1 A2; auto;
        [apply projp_col with A|apply projp_col with C]; auto.
        }
      apply cong_transitivity with AX' CX'; Cong.
      }
    assert (ACX'' = CXMAX)
      by (apply l16_9_1 with O E E' CX AX; Col; left; auto).
    treat_equalities; auto.
    }

    {
    assert (LAXBX : Length O E E' AX BX ABX'').
      {
      apply length_eq_cong_2 with A BX''; auto.
      assert (Cong AX BX AX' BX').
        {
        apply cong_3_2_cong_4 with O E AX BX S U1 AX' BX' in HCongBX';
        try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
        }
      assert (Cong A BX'' AX' BX').
        {
        apply col_2_par_projp2_cong with S U1 A1 A2; auto;
        [apply projp_col with A|apply projp_col with B]; auto.
        }
      apply cong_transitivity with AX' BX'; Cong.
      }
    destruct (diff_exists O E E' AX BX) as [AXMBX HAXMBX]; Col.
    assert (ABX'' = AXMBX)
      by (apply l16_9_1 with O E E' AX BX; Col; left; auto).
    elim HLe4; clear HLe4; intro HLt; treat_equalities;
    [|assert (AX' = BX') by (apply col_cong_3_cong_3_eq with O E BX S U1;
                             try intro; treat_equalities; Col);
    treat_equalities;
    apply projp_id with AX' A BX'' A1 A2 in HBX''; auto;
    treat_equalities; exfalso; Col].
    apply bet_lt21_le31 with O E E' AX BX CX in HLt;
    [|apply bet_betCood_aux with O E S U1 U2 A AY B BY C CY; auto].
    assert (LAXCX : Length O E E' AX CX ACX'').
      {
      apply length_eq_cong_2 with A CX''; auto.
      assert (Cong AX CX AX' CX').
        {
        apply cong_3_2_cong_4 with O E AX CX S U1 AX' CX' in HCongCX';
        try intro; treat_equalities; Col; unfold Cong_4 in *; spliter; Cong.
        }
      assert (Cong A CX'' AX' CX').
        {
        apply col_2_par_projp2_cong with S U1 A1 A2; auto;
        [apply projp_col with A|apply projp_col with C]; auto.
        }
      apply cong_transitivity with AX' CX'; Cong.
      }
    destruct (diff_exists O E E' AX CX) as [AXMCX HAXMCX]; Col.
    assert (ACX'' = AXMCX)
      by (apply l16_9_1 with O E E' AX CX; Col; left; auto).
    treat_equalities.
    assert (Opp O E E' BXMAX ABX'') by (apply diff_opp with BX AX; auto).
    assert (Opp O E E' CXMAX ACX'') by (apply diff_opp with CX AX; auto).
    destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
    apply prod_assoc2 with ACX'' ME ABX'';
    [auto|apply opp_prod; auto; apply opp_comm; auto|
     apply opp_prod; auto; apply opp_comm; auto].
    }
  }
Qed.


Unset Regular Subst Tactic.

Lemma characterization_of_betweenness :
  forall O E E' S U1 U2
         A AX AY B BX BY C CX CY
         BXMAX BYMAY CXMAX CYMAY,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY -> Cd O E S U1 U2 C CX CY ->
  Diff O E E' BX AX BXMAX -> Diff O E E' BY AY BYMAY ->
  Diff O E E' CX AX CXMAX -> Diff O E E' CY AY CYMAY ->
  (Bet A B C <-> exists T, O <> E /\ Col O E T /\
                           LeP O E E' O T /\ LeP O E E' T E /\
                           Prod O E E' T CXMAX BXMAX /\
                           Prod O E E' T CYMAY BYMAY).
Proof.
intros O E E' S U1 U2 A AX AY B BX BY C CX CY BXMAX BYMAY CXMAX CYMAY.
intros HCdA HCdB HCdC HBXMAX HBYMAY HCXMAX HCYMAY.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
assert (HColAX : Col O E AX)
  by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
assert (HColAY : Col O E AY)
  by (apply diff_ar2 in HBYMAY; unfold Ar2 in *; spliter; Col).
assert (HColBX : Col O E BX)
  by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
assert (HColBY : Col O E BY)
  by (apply diff_ar2 in HBYMAY; unfold Ar2 in *; spliter; Col).
assert (HColCX : Col O E CX)
  by (apply diff_ar2 in HCXMAX; unfold Ar2 in *; spliter; Col).
assert (HColCY : Col O E CY)
  by (apply diff_ar2 in HCYMAY; unfold Ar2 in *; spliter; Col).
assert (HColBXMAX : Col O E BXMAX)
  by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
assert (HColBYMAY : Col O E BYMAY)
  by (apply diff_ar2 in HBYMAY; unfold Ar2 in *; spliter; Col).
assert (HColCXMAX : Col O E CXMAX)
  by (apply diff_ar2 in HCXMAX; unfold Ar2 in *; spliter; Col).
assert (HColCYMAY : Col O E CYMAY)
  by (apply diff_ar2 in HCYMAY; unfold Ar2 in *; spliter; Col).
split; [intro HBet|intro HT].

  {
  elim (eq_dec_points A B); intro HDiff1; treat_equalities.

    {
    assert (AX = BX /\ AY = BY)
      by (rewrite <- eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
    spliter; treat_equalities.
    assert (O = BXMAX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
    assert (O = BYMAY)
      by (apply diff_uniqueness with O E E' AY AY; auto; apply diff_null; Col).
    treat_equalities; exists O; split; try (intro; treat_equalities; Col).
    split; Col. split; try apply leP_refl.
    split; try apply ps_le; Between.
    split; apply prod_0_l; Col.
    }

    {
    elim (eq_dec_points A C); intro HDiff2; treat_equalities; [intuition|].
    elim (eq_dec_points B C); intro HDiff3; treat_equalities.

      {
      assert (BX = CX /\ BY = CY)
        by (rewrite <- eq_points_coordinates; [|apply HCdB|apply HCdC]; auto).
      spliter; treat_equalities.
      assert (BXMAX = CXMAX) by (apply diff_uniqueness with O E E' BX AX; auto).
      assert (BYMAY = CYMAY) by (apply diff_uniqueness with O E E' BY AY; auto).
      treat_equalities; exists E; split; try (intro; treat_equalities; Col).
      split; Col. split; try apply ps_le; Between.
      split; try apply leP_refl.
      split; apply prod_1_l; Col.
      }

      {
      destruct (length_existence O E E' A B) as [AB HAB]; Col.
      destruct (length_existence O E E' A C) as [AC HAC]; Col.
      destruct (length_existence O E E' B C) as [BC HBC]; Col.
      assert (HSum : Sum O E E' AB BC AC)
        by (assert_diffs; apply triangular_equality_bis with A B C; auto).
      assert (HLe1 : LeP O E E' O AB) by (apply length_pos with A B; auto).
      assert (HLe2 : LeP O E E' AB AC)
        by (apply length_leP_le_2 with A B A C; try (apply l5_5_2; exists C); Cong).
      assert (HColAB : Col O E AB) by (unfold Length in *; spliter; Col).
      assert (HColAC : Col O E AC) by (unfold Length in *; spliter; Col).
      destruct (inv_exists O E E' AC) as [IAC HIAC]; Col;
      try (intro; unfold Length in *; spliter; treat_equalities; auto).
      assert (HColIAC : Col O E IAC) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HLe3 : LeP O E E' O IAC).
        {
        apply pos_inv_pos with AC; auto;
        try (intro; unfold Length in *; spliter; treat_equalities; auto).
        apply length_pos with A C; auto.
        }
      destruct (prod_exists O E E' HNC AB IAC) as [T HT]; Col.
      exists T; split; try (intro; treat_equalities; Col).
      split; [unfold Prod, Ar2 in *; spliter; Col|].
      split; [apply compatibility_of_prod_with_order with AB IAC; auto|].
      split; [apply le_pos_prod_le with AB AC IAC; auto; apply prod_comm; auto|].
      assert (HColT : Col O E T) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HT' : Prod O E E' T AC AB)
        by (apply prod_assoc1 with AB IAC E; auto; apply prod_1_r; Col).
      split;
      [apply characterization_of_betweenness_aux
       with S U1 U2 A AX AY B BX BY C CX CY AB AC IAC|
       apply characterization_of_betweenness_aux
       with S U2 U1 A AY AX B BY BX C CY CX AB AC IAC
      ]; auto; apply coord_exchange_axes; auto.
      }
    }
  }

  {
  destruct HT as [T [H [HColT [HOLeT [HTLeE [HX HY]]]]]]; clear H.
  rename B into B'; rename BX into B'X; rename BY into B'Y; rename HCdB into HCdB'.
  rename BXMAX into B'XMAX; rename HBXMAX into HB'XMAX.
  rename BYMAY into B'YMAY; rename HBYMAY into HB'YMAY.
  rename HColBX into HColB'X; rename HColBY into HColB'Y.
  rename HColBXMAX into HColB'XMAX; rename HColBYMAY into HColB'YMAY.
  destruct (length_existence O E E' A C) as [AC HAC]; Col.
  assert (HColAC : Col O E AC) by (unfold Length in *; spliter; Col).
  assert (HLe1 : LeP O E E' O AC) by (apply length_pos with A C; auto).
  destruct (prod_exists O E E' HNC T AC) as [AB HT]; Col.
  assert (HColAB : Col O E AB) by (unfold Prod, Ar2 in *; spliter; Col).
  assert (HLe2 : LeP O E E' O AB)
    by (apply compatibility_of_prod_with_order with T AC; auto).
  assert (HB : exists B, Bet A B C /\ Length O E E' A B AB).
    {
    assert (Le O AB A C).
      {
      apply length_leP_le_1 with O E E' AB AC; auto.
      assert_diffs; do 2 (split; Cong).
      apply le_pos_prod_le with T E AC; auto; apply prod_1_l; Col.
      }
    destruct (le_bet A C O AB) as [B [HBet HCong]]; auto; exists B; split; auto.
    assert_diffs; do 3 (split; Cong).
    }
  destruct HB as [B [HBet HAB]].
  elim (eq_dec_points A C); intro HDiff2; treat_equalities.

    {
    assert (AX = CX /\ AY = CY)
      by (rewrite <- eq_points_coordinates; [|apply HCdA|apply HCdC]; auto).
    spliter; treat_equalities.
    assert (O = CXMAX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
    assert (O = CYMAY)
      by (apply diff_uniqueness with O E E' AY AY; auto; apply diff_null; Col).
    treat_equalities.
    assert (O = B'XMAX)
      by (apply prod_uniqueness with O E E' T O; auto; apply prod_0_r; Col).
    assert (O = B'YMAY)
      by (apply prod_uniqueness with O E E' T O; auto; apply prod_0_r; Col).
    treat_equalities.
    assert (AX = B'X) by (apply diff_uniquenessA with O E E' AX O; auto).
    assert (AY = B'Y) by (apply diff_uniquenessA with O E E' AY O; auto).
    treat_equalities.
    assert (A = B')
      by (rewrite eq_points_coordinates; [|apply HCdA|apply HCdB']; auto).
    treat_equalities; Between.
    }

    {
    assert (HCdB : exists BX, exists BY, Cd O E S U1 U2 B BX BY)
      by (apply coordinates_of_point; unfold Cd in *; spliter; auto).
    destruct HCdB as [BX [BY HCdB]].
    elim (eq_dec_points A B); intro HDiff1; treat_equalities;
    try (elim (eq_dec_points B C); intro HDiff3; treat_equalities).

      {
      assert (AX = BX /\ AY = BY)
        by (rewrite <- eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
      assert (O = AB); spliter; treat_equalities.
        {
        apply length_uniqueness with O E E' A A; auto; apply length_id_2;
        assert_diffs; auto.
        }
      elim (eq_dec_points O T); intro HOT; treat_equalities.

        {
        assert (O = B'XMAX)
          by (apply prod_uniqueness with O E E' O CXMAX; auto; apply prod_0_l; Col).
        assert (O = B'YMAY)
          by (apply prod_uniqueness with O E E' O CYMAY; auto; apply prod_0_l; Col).
        treat_equalities.
        assert (AX = B'X)
          by (apply diff_uniquenessA with O E E' AX O; auto; apply diff_null; Col).
        assert (AY = B'Y)
          by (apply diff_uniquenessA with O E E' AY O; auto; apply diff_null; Col).
        assert (A = B'); treat_equalities; Between.
        rewrite eq_points_coordinates; [|apply HCdA|apply HCdB']; auto.
        }

        {
        apply prod_null in HT; elim HT; clear HT; intro H; [intuition|].
        apply eq_sym in H; treat_equalities; exfalso; apply HDiff2.
        apply length_id in HAC; spliter; auto.
        }
      }

      {
      assert (BX = CX /\ BY = CY)
        by (rewrite <- eq_points_coordinates; [|apply HCdB|apply HCdC]; auto).
      spliter; treat_equalities.
      assert (AB = AC) by (apply length_uniqueness with O E E' A B; auto).
      spliter; treat_equalities.
      assert (E = T); treat_equalities.
        {
        apply prod_uniquenessA with O E E' AB AB; try apply prod_1_l; auto.
        intro; treat_equalities; apply length_id in HAB;
        assert_diffs; induction HAB; auto.
        }
      assert (CXMAX = B'XMAX)
        by (apply prod_uniqueness with O E E' E CXMAX; auto; apply prod_1_l; Col).
      assert (CYMAY = B'YMAY)
        by (apply prod_uniqueness with O E E' E CYMAY; auto; apply prod_1_l; Col).
      treat_equalities.
      assert (BX = B'X) by (apply diff_uniquenessA with O E E' AX CXMAX; auto).
      assert (BY = B'Y) by (apply diff_uniquenessA with O E E' AY CYMAY; auto).
      assert (B = B'); treat_equalities; Between.
      rewrite eq_points_coordinates; [|apply HCdB|apply HCdB']; auto.
      }

      {
      destruct (inv_exists O E E' AC) as [IAC HIAC]; Col;
      try (intro; unfold Length in *; spliter; treat_equalities; auto).
      assert (HColIAC : Col O E IAC) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HColBX : Col O E BX) by (apply Cd_Col in HCdB; spliter; Col).
      destruct (diff_exists O E E' BX AX) as [BXMAX HBXMAX]; Col.
      assert (HColBXMAX : Col O E BXMAX)
        by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
      assert (HX' : Prod O E E' T CXMAX BXMAX).
        {
        apply characterization_of_betweenness_aux
        with S U1 U2 A AX AY B BX BY C CX CY AB AC IAC; auto.
        }
      assert (BXMAX = B'XMAX) by (apply prod_uniqueness with O E E' T CXMAX; auto).
      assert (HColBY : Col O E BY) by (apply Cd_Col in HCdB; spliter; Col).
      destruct (diff_exists O E E' BY AY) as [BYMAY HBYMAY]; Col.
      assert (HColBYMAY : Col O E BYMAY)
        by (apply diff_ar2 in HBYMAY; unfold Ar2 in *; spliter; Col).
      assert (HY' : Prod O E E' T CYMAY BYMAY).
        {
        apply characterization_of_betweenness_aux
        with S U2 U1 A AY AX B BY BX C CY CX AB AC IAC; auto;
        apply coord_exchange_axes; auto.
        }
      assert (BYMAY = B'YMAY) by (apply prod_uniqueness with O E E' T CYMAY; auto).
      treat_equalities.
      assert (BX = B'X) by (apply diff_uniquenessA with O E E' AX BXMAX; auto).
      assert (BY = B'Y) by (apply diff_uniquenessA with O E E' AY BYMAY; auto).
      treat_equalities.
      assert (B = B')
        by (rewrite eq_points_coordinates; [|apply HCdB|apply HCdB']; auto).
      treat_equalities; auto.
      }
    }
  }
Qed.

Lemma same_abscissa_col : forall O E S U1 U2 A AX AY B BY C CY,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B AX BY -> Cd O E S U1 U2 C AX CY ->
  Col A B C.
Proof.
intros O E S U1 U2 A AX AY B BY C CY HCdA HCdB HCdC.
destruct HCdA as [HCs [H [[PXA [HProjpA HCongA]] H']]]; clear H; clear H'.
destruct HCdB as [H [H' [[PXB [HProjpB HCongB]] H'']]]; clear H; clear H'; clear H''.
destruct HCdC as [H [H' [[PXC [HProjpC HCongC]] H'']]]; clear H; clear H'; clear H''.
assert (HDiff1 : O <> E) by (unfold Cs in *; spliter; auto).
assert (HColAX : Col O E AX)
  by (apply l4_13 with S U1 PXA; Cong; apply projp_col with A; auto).
eapply col_cong_3_cong_3_eq in HCongB; [| | |apply HCongA]; treat_equalities; auto.
eapply col_cong_3_cong_3_eq in HCongC; [| | |apply HCongA]; treat_equalities; auto.
clear HCongA; elim (eq_dec_points A PXA); intro HDiff2; treat_equalities;
[apply projp2_col with S U1; auto|].
eapply projp2_col in HProjpB; [|apply HProjpA].
eapply projp2_col in HProjpC; [|apply HProjpA].
ColR.
Qed.

Lemma characterization_of_collinearity :
  forall O E E' S U1 U2
         A AX AY B BX BY C CX CY
         AXMBX AYMBY BXMCX BYMCY XProd YProd,
  Cd O E S U1 U2 A AX AY -> Cd O E S U1 U2 B BX BY -> Cd O E S U1 U2 C CX CY ->
  Diff O E E' AX BX AXMBX -> Diff O E E' AY BY AYMBY ->
  Diff O E E' BX CX BXMCX -> Diff O E E' BY CY BYMCY ->
  Prod O E E' AXMBX BYMCY XProd -> Prod O E E' AYMBY BXMCX YProd ->
  (Col A B C <-> XProd = YProd).
Proof.
intros O E E' S U1 U2 A AX AY B BX BY C CX CY AXMBX AYMBY BXMCX BYMCY XProd YProd.
intros HCdA HCdB HCdC HAXMBX HAYMBY HBXMCX HBYMCY HXProd HYProd.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HAXMBX; unfold Ar2 in *; spliter; Col).
assert (HColAX : Col O E AX)
  by (apply diff_ar2 in HAXMBX; unfold Ar2 in *; spliter; Col).
assert (HColAY : Col O E AY)
  by (apply diff_ar2 in HAYMBY; unfold Ar2 in *; spliter; Col).
assert (HColBX : Col O E BX)
  by (apply diff_ar2 in HBXMCX; unfold Ar2 in *; spliter; Col).
assert (HColBY : Col O E BY)
  by (apply diff_ar2 in HBYMCY; unfold Ar2 in *; spliter; Col).
assert (HColCX : Col O E CX)
  by (apply diff_ar2 in HBXMCX; unfold Ar2 in *; spliter; Col).
assert (HColCY : Col O E CY)
  by (apply diff_ar2 in HBYMCY; unfold Ar2 in *; spliter; Col).
assert (HColAXMBX : Col O E AXMBX)
  by (apply diff_ar2 in HAXMBX; unfold Ar2 in *; spliter; Col).
assert (HColAYMBY : Col O E AYMBY)
  by (apply diff_ar2 in HAYMBY; unfold Ar2 in *; spliter; Col).
assert (HColBXMCX : Col O E BXMCX)
  by (apply diff_ar2 in HBXMCX; unfold Ar2 in *; spliter; Col).
assert (HColBYMCY : Col O E BYMCY)
  by (apply diff_ar2 in HBYMCY; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' BX AX) as [BXMAX HBXMAX]; Col.
assert (HColBXMAX : Col O E BXMAX)
  by (apply diff_ar2 in HBXMAX; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' BY AY) as [BYMAY HBYMAY]; Col.
assert (HColBYMAY : Col O E BYMAY)
  by (apply diff_ar2 in HBYMAY; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' CX AX) as [CXMAX HCXMAX]; Col.
assert (HColCXMAX : Col O E CXMAX)
  by (apply diff_ar2 in HCXMAX; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' CY AY) as [CYMAY HCYMAY]; Col.
assert (HColCYMAY : Col O E CYMAY)
  by (apply diff_ar2 in HCYMAY; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' CX BX) as [CXMBX HCXMBX]; Col.
assert (HColCXMBX : Col O E CXMBX)
  by (apply diff_ar2 in HCXMBX; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' CY BY) as [CYMBY HCYMBY]; Col.
assert (HColCYMBY : Col O E CYMBY)
  by (apply diff_ar2 in HCYMBY; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' AX CX) as [AXMCX HAXMCX]; Col.
assert (HColAXMCX : Col O E AXMCX)
  by (apply diff_ar2 in HAXMCX; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' AY CY) as [AYMCY HAYMCY]; Col.
assert (HColAYMCY : Col O E AYMCY)
  by (apply diff_ar2 in HAYMCY; unfold Ar2 in *; spliter; Col).
assert (HColXProd : Col O E XProd) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColYProd : Col O E YProd) by (unfold Prod, Ar2 in *; spliter; Col).
split; intro HCol; treat_equalities.

  {
  elim (eq_dec_points A B); intro HDiff1; elim (eq_dec_points A C); intro HDiff2;
  elim (eq_dec_points B C); intro HDiff3; treat_equalities;
  [|intuition|intuition| |intuition| | |].

    {
    apply eq_points_coordinates with O E S U1 U2 B AX AY B BX BY in HCdA; auto.
    destruct HCdA as [H H']; clear H';
    elim H; clear H; auto; intros; treat_equalities.
    assert (O = AXMBX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
    assert (O = AYMBY)
      by (apply diff_uniqueness with O E E' AY AY; auto; apply diff_null; Col).
    treat_equalities.
    assert (O = XProd)
      by (apply prod_uniqueness with O E E' O BYMCY; auto; apply prod_0_l; Col).
    assert (O = YProd)
      by (apply prod_uniqueness with O E E' O BXMCX; auto; apply prod_0_l; Col).
    treat_equalities; auto.
    }

    {
    apply eq_points_coordinates with O E S U1 U2 A AX AY A BX BY in HCdA; auto.
    destruct HCdA as [H H']; clear H';
    elim H; clear H; auto; intros; treat_equalities.
    assert (O = AXMBX)
      by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
    assert (O = AYMBY)
      by (apply diff_uniqueness with O E E' AY AY; auto; apply diff_null; Col).
    treat_equalities.
    assert (O = XProd)
      by (apply prod_uniqueness with O E E' O BYMCY; auto; apply prod_0_l; Col).
    assert (O = YProd)
      by (apply prod_uniqueness with O E E' O BXMCX; auto; apply prod_0_l; Col).
    treat_equalities; auto.
    }

    {
    apply eq_points_coordinates with O E S U1 U2 A AX AY A CX CY in HCdC; auto.
    destruct HCdC as [H H']; clear H';
    elim H; clear H; auto; intros; treat_equalities.
    destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
    apply prod_uniqueness with O E E' AXMBX BYMCY; auto.
    apply prod_assoc1 with BXMCX ME AYMBY; auto;
    [|apply prod_comm|apply prod_comm; auto]; apply opp_prod; auto;
    [apply diff_opp with BX AX|apply diff_opp with BY AY]; auto.
    }

    {
    apply eq_points_coordinates with O E S U1 U2 B BX BY B CX CY in HCdC; auto.
    destruct HCdC as [H H']; clear H';
    elim H; clear H; auto; intros; treat_equalities.
    assert (O = BXMCX)
      by (apply diff_uniqueness with O E E' BX BX; auto; apply diff_null; Col).
    assert (O = BYMCY)
      by (apply diff_uniqueness with O E E' BY BY; auto; apply diff_null; Col).
    treat_equalities.
    assert (O = XProd)
      by (apply prod_uniqueness with O E E' AXMBX O; auto; apply prod_0_r; Col).
    assert (O = YProd)
      by (apply prod_uniqueness with O E E' AYMBY O; auto; apply prod_0_r; Col).
    treat_equalities; auto.
    }

    {
    do 2 (try (elim HCol; clear HCol; intro HCol)); rename HCol into HBet1.

      {
      assert (HBet2 : Bet AX BX CX /\ Bet AY BY CY)
        by (apply bet_betCood with O E S U1 U2 A B C; auto).
      destruct HBet2 as [HBet2 HBet3].
      assert (HBet':= HBet1).
      rewrite characterization_of_betweenness in HBet';
      [|apply HCdA|apply HCdB|apply HCdC|
       apply HBXMAX|apply HBYMAY|apply HCXMAX| apply HCYMAY].
      destruct HBet' as [T [HDiff4 [HColT [HLe1 [HLe2 [HProd1 HProd2]]]]]].
      assert (HSumX : Sum O E E' AXMBX BXMCX AXMCX)
        by (apply sum_diff_diff with AX BX CX; auto).
      assert (HSumY : Sum O E E' AYMBY BYMCY AYMCY)
        by (apply sum_diff_diff with AY BY CY; auto).
      destruct (prod_exists O E E' HNC AXMBX AYMBY) as [P1 HP1]; Col.
      assert (HColP1 : Col O E P1) by (unfold Prod, Ar2 in *; spliter; Col).
      destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
      assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
      destruct (prod_exists O E E' HNC ME T) as [P2 HP2]; Col.
      assert (HColP2 : Col O E P2) by (unfold Prod, Ar2 in *; spliter; Col).
      destruct (sum_exists O E E' HNC XProd P1) as [XProd' HXProd']; Col.
      assert (HColXProd' : Col O E XProd') by (unfold Sum, Ar2 in *; spliter; Col).
      destruct (prod_exists O E E' HNC AXMBX AYMCY) as [D HProdX']; Col.
      assert (XProd' = D); treat_equalities.
        {
        apply sum_uniqueness with O E E' XProd P1; auto.
        apply distr_l with AXMBX BYMCY AYMBY AYMCY; auto.
        apply sum_comm; auto.
        }
      destruct (sum_exists O E E' HNC YProd P1) as [YProd' HYProd']; Col.
      assert (HColYProd' : Col O E YProd') by (unfold Sum, Ar2 in *; spliter; Col).
      destruct (prod_exists O E E' HNC AYMBY AXMCX) as [D HProdY']; Col.
      assert (YProd' = D); treat_equalities.
        {
        apply sum_uniqueness with O E E' YProd P1; auto.
        apply distr_l with AYMBY BXMCX AXMBX AXMCX; auto;
        [apply sum_comm|apply prod_comm]; auto.
        }
      destruct (prod_exists O E E' HNC P2 XProd') as [XProd'' HXProd'']; Col.
      destruct (prod_exists O E E' HNC AXMBX BYMAY) as [D HProdX'']; Col.
      assert (XProd'' = D); treat_equalities.
        {
        apply prod_uniqueness with O E E' AXMBX BYMAY; auto.
        apply prod_assoc2 with AYMCY P2 XProd'; auto; apply prod_comm; auto.
        apply prod_assoc1 with T ME CYMAY; auto; apply prod_comm; auto.
        apply opp_prod; auto; apply diff_opp with AY CY; auto.
        }
      destruct (prod_exists O E E' HNC P2 YProd') as [YProd'' HYProd'']; Col.
      destruct (prod_exists O E E' HNC AYMBY BXMAX) as [D HProdY'']; Col.
      assert (YProd'' = D); treat_equalities.
        {
        apply prod_uniqueness with O E E' AYMBY BXMAX; auto.
        apply prod_assoc2 with AXMCX P2 YProd'; auto; apply prod_comm; auto.
        apply prod_assoc1 with T ME CXMAX; auto; apply prod_comm; auto.
        apply opp_prod; auto; apply diff_opp with AX CX; auto.
        }
      assert (XProd'' = YProd''); treat_equalities.
        {
        apply prod_uniqueness with O E E' AXMBX BYMAY; auto; apply prod_comm.
        apply prod_assoc1 with AYMBY ME BXMAX; auto; [|apply prod_comm];
        apply opp_prod; auto; [apply diff_opp with AY BY|apply diff_opp with AX BX];
        auto.
        }
      assert (XProd' = YProd'); treat_equalities.
        {
        apply prod_uniquenessB with O E E' P2 XProd''; auto.
        intro H; apply eq_sym in H; treat_equalities; apply prod_null in HP2.
        elim HP2; clear HP2; intro HFalse; apply eq_sym in HFalse; treat_equalities;
        [apply HDiff4; apply opp_uniqueness with O E E' O;
         try apply opp0; Col; apply opp_comm; auto|].
        assert (O = BXMAX)
          by (apply prod_uniqueness with O E E' O CXMAX; auto; apply prod_0_l; Col).
        assert (O = BYMAY)
          by (apply prod_uniqueness with O E E' O CYMAY; auto; apply prod_0_l; Col).
        treat_equalities; apply diff_null_eq in HBXMAX; apply diff_null_eq in HBYMAY.
        treat_equalities; apply HDiff1; rewrite eq_points_coordinates;
        [|apply HCdA|apply HCdB]; auto.
        }
      apply sum_uniquenessA with O E E' P1 XProd'; auto.
      }

      {
      assert (HBet2 : Bet BX CX AX /\ Bet BY CY AY)
        by (apply bet_betCood with O E S U1 U2 B C A; auto).
      destruct HBet2 as [HBet2 HBet3].
      assert (HBet':= HBet1).
      rewrite characterization_of_betweenness in HBet';
      [|apply HCdB|apply HCdC|apply HCdA|
       apply HCXMBX|apply HCYMBY|apply HAXMBX| apply HAYMBY].
      destruct HBet' as [T [HDiff4 [HColT [HLe1 [HLe2 [HProd1 HProd2]]]]]].
      apply prod_uniqueness with O E E' AXMBX BYMCY; auto.
      destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
      assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
      destruct (prod_exists O E E' HNC ME T) as [P HP]; Col.
      apply prod_assoc2 with P AYMBY BXMCX; apply prod_comm; auto.

        {
        apply prod_assoc1 with ME T CXMBX; auto.
        apply prod_comm; apply opp_prod; auto.
        apply diff_opp with CX BX; auto.
        }

        {
        apply prod_assoc2 with T ME CYMBY; apply prod_comm; auto.
        apply prod_comm; apply opp_prod; auto.
        apply diff_opp with CY BY; auto.
        }
      }

      {
      assert (HBet2 : Bet CX AX BX /\ Bet CY AY BY)
        by (apply bet_betCood with O E S U1 U2 C A B; auto).
      destruct HBet2 as [HBet2 HBet3].

      assert (HBet':= HBet1).
      rewrite characterization_of_betweenness in HBet';
      [|apply HCdC|apply HCdA|apply HCdB|
       apply HAXMCX|apply HAYMCY|apply HBXMCX| apply HBYMCY].
      destruct HBet' as [T [HDiff4 [HColT [HLe1 [HLe2 [HProd1 HProd2]]]]]].
      assert (HSumX : Sum O E E' CXMAX AXMBX CXMBX)
        by (apply sum_diff_diff with CX AX BX; auto).
      assert (HSumY : Sum O E E' CYMAY AYMBY CYMBY)
        by (apply sum_diff_diff with CY AY BY; auto).
      destruct (prod_exists O E E' HNC CXMAX BYMCY) as [P1 HP1]; Col.
      destruct (prod_exists O E E' HNC CYMAY BXMCX) as [P2 HP1']; Col.
      assert (P1 = P2); treat_equalities.
        {
        apply prod_uniqueness with O E E' CXMAX BYMCY; auto.
        destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
        assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
        destruct (prod_exists O E E' HNC ME T) as [P HP]; Col.
        apply prod_assoc1 with BXMCX P CYMAY; apply prod_comm; auto.

          {
          apply prod_assoc1 with ME T AXMCX; auto.
          apply prod_comm; apply opp_prod; auto.
          apply diff_opp with AX CX; auto.
          }

          {
          apply prod_assoc2 with T ME AYMCY; apply prod_comm; auto.
          apply prod_comm; apply opp_prod; auto.
          apply diff_opp with AY CY; auto.
          }
        }
      assert (HColP1 : Col O E P1) by (unfold Prod, Ar2 in *; spliter; Col).
      destruct (sum_exists O E E' HNC XProd P1) as [XProd' HXProd']; Col.
      destruct (prod_exists O E E' HNC CXMBX BYMCY) as [P2 HP2]; Col.
      assert (P2 = XProd'); treat_equalities.
        {
        apply sum_uniqueness with O E E' XProd P1; auto.
        apply sum_comm; Col.
        apply distr_r with CXMAX AXMBX BYMCY CXMBX; auto.
        }
      destruct (sum_exists O E E' HNC YProd P1) as [YProd' HYProd']; Col.
      assert (P2 = YProd'); treat_equalities.
        {
        apply sum_uniqueness with O E E' YProd P1; auto.
        apply sum_comm; Col.
        apply distr_r with CYMAY AYMBY BXMCX CYMBY; auto.
        apply prod_comm; auto.
        destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
        assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
        apply prod_assoc1 with CXMBX ME BYMCY; auto.

          {
          apply opp_prod; auto.
          apply diff_opp with CX BX; auto.
          }

          {
          apply prod_comm; apply opp_prod; auto.
          apply diff_opp with CY BY; auto.
          }
        }
      apply sum_uniquenessA with O E E' P1 P2; auto.
      }
    }
  }

  {
  elim (eq_dec_points O AXMBX); intro HDiff1;
  treat_equalities; try apply diff_null_eq in HAXMBX;
  elim (eq_dec_points O AYMBY); intro HDiff2;
  treat_equalities; try apply diff_null_eq in HAYMBY;
  elim (eq_dec_points O BXMCX); intro HDiff3;
  treat_equalities; try apply diff_null_eq in HBXMCX;
  elim (eq_dec_points O BYMCY); intro HDiff4;
  treat_equalities; try apply diff_null_eq in HBYMCY; treat_equalities.

    {
    assert (A = B) by (rewrite eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
    treat_equalities; Col.
    }

    {
    assert (A = B) by (rewrite eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
    treat_equalities; Col.
    }

    {
    assert (A = B) by (rewrite eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
    treat_equalities; Col.
    }

    {
    assert (A = B) by (rewrite eq_points_coordinates; [|apply HCdA|apply HCdB]; auto).
    treat_equalities; Col.
    }

    {
    assert (B = C) by (rewrite eq_points_coordinates; [|apply HCdB|apply HCdC]; auto).
    treat_equalities; Col.
    }

    {
    apply same_abscissa_col with O E S U1 U2 AX AY BY CY; auto.
    }

    {
    apply prod_O_l_eq in HXProd; apply eq_sym in HXProd; treat_equalities.
    apply prod_null in HYProd; elim HYProd; clear HYProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    apply prod_O_l_eq in HXProd; apply eq_sym in HXProd; treat_equalities.
    apply prod_null in HYProd; elim HYProd; clear HYProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    assert (B = C) by (rewrite eq_points_coordinates; [|apply HCdB|apply HCdC]; auto).
    treat_equalities; Col.
    }

    {
    apply prod_O_l_eq in HYProd; apply eq_sym in HYProd; treat_equalities.
    apply prod_null in HXProd; elim HXProd; clear HXProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    apply same_abscissa_col with O E S U2 U1 AY AX BX CX; auto;
    apply coord_exchange_axes; auto.
    }

    {
    apply prod_O_l_eq in HYProd; apply eq_sym in HYProd; treat_equalities.
    apply prod_null in HXProd; elim HXProd; clear HXProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    assert (B = C) by (rewrite eq_points_coordinates; [|apply HCdB|apply HCdC]; auto).
    treat_equalities; Col.
    }

    {
    apply prod_O_r_eq in HYProd; apply eq_sym in HYProd; treat_equalities.
    apply prod_null in HXProd; elim HXProd; clear HXProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    apply prod_O_r_eq in HXProd; apply eq_sym in HXProd; treat_equalities.
    apply prod_null in HYProd; elim HYProd; clear HYProd; intro H;
    apply eq_sym in H; treat_equalities; intuition.
    }

    {
    destruct (length_existence O E E' AX BX) as [L1 HL1]; Col.
    assert (HColL1 : Col O E L1) by (unfold Length in *; spliter; Col).
    destruct (length_existence O E E' AX CX) as [L2 HL2]; Col.
    assert (HColL2 : Col O E L2) by (unfold Length in *; spliter; Col).
    destruct (length_existence O E E' BX CX) as [L3 HL3]; Col.
    assert (HColL3 : Col O E L3) by (unfold Length in *; spliter; Col).
    assert (HElim : LeP O E E' L1 L3 /\ LeP O E E' L2 L3 \/
                    LeP O E E' L1 L2 /\ LeP O E E' L3 L2 \/
                    LeP O E E' L2 L1 /\ LeP O E E' L3 L1).
      {
      assert (H1 : LeP O E E' L1 L2 \/ LeP O E E' L2 L1)
          by (apply col_2_le_or_ge; Col).
      assert (H2 : LeP O E E' L1 L3 \/ LeP O E E' L3 L1)
        by (apply col_2_le_or_ge; Col).
      assert (H3 : LeP O E E' L2 L3 \/ LeP O E E' L3 L2)
        by (apply col_2_le_or_ge; Col).
      elim H1; clear H1; intro HLe1; elim H2; clear H2; intro HLe2;
      elim H3; clear H3; intro HLe3; auto.

        {
        apply leP_asym in HLe2; treat_equalities; [left; split; auto; right; auto|].
        apply leP_trans with L2; auto.
        }

        {
        apply leP_asym in HLe2; treat_equalities; [left; split; auto; right; auto|].
        apply leP_trans with L2; auto.
        }
      }
    do 2 (try (elim HElim; clear HElim; intro HElim;
               try destruct HElim as [HLe1 HLe2])); [right; right|left|right; left].
      {
      assert (HBetX : Bet CX AX BX).
        {
        apply l5_12_b; [assert_diffs; ColR|
                apply length_leP_le_1 with O E E' L2 L3|
                apply length_leP_le_1 with O E E' L1 L3];
        auto; apply length_sym; auto.
        }
      rewrite characterization_of_betweenness;
      [|apply HCdC|apply HCdA|apply HCdB|
       apply HAXMCX|apply HAYMCY|apply HBXMCX|apply HBYMCY].
      assert (HDiff5 : O <> L3).
        {
        intro; treat_equalities; apply length_id in HL3; spliter; treat_equalities.
        apply HDiff1; apply diff_uniqueness with O E E' BX BX; auto;
        apply diff_null; Col.
        }
      assert (HLe3 : LeP O E E' O L3) by (apply length_pos with BX CX; auto).
      destruct (inv_exists O E E' L3) as [IBC HIBC]; Col.
      assert (HColIBC : Col O E IBC) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HLe4 : LeP O E E' O IBC) by (apply pos_inv_pos with L3; auto).
      destruct (prod_exists O E E' HNC L2 IBC) as [T HT]; Col; exists T.
      split; try (intro; treat_equalities; Col).
      split; [unfold Prod, Ar2 in *; spliter; Col|].
      assert (HLe5 : LeP O E E' O L2) by (apply length_pos with AX CX; auto).
      split; [apply compatibility_of_prod_with_order with L2 IBC; auto|].
      split; [apply le_pos_prod_le with L2 L3 IBC; auto; apply prod_comm; auto|].
      assert (HDiff6 : O <> E) by (assert_diffs; auto).
      destruct (prod_exists O E E' HNC BXMCX BYMCY) as [P HP]; Col.
      destruct (prod_exists O E E' HNC AXMCX BYMCY) as [Pr HProd1]; Col.
      assert (HSum : Sum O E E' XProd P Pr).
        {
        apply distr_l with BYMCY AXMBX BXMCX AXMCX; auto; try apply prod_comm; auto.
        apply sum_diff_diff with AX BX CX; auto.
        }
      assert (HProd2 : Prod O E E' AYMCY BXMCX Pr).
        {
        destruct (prod_exists O E E' HNC AYMCY BXMCX) as [P' HP']; Col.
        assert (Pr = P'); treat_equalities; auto.
        apply sum_uniqueness with O E E' XProd P; auto.
        apply distr_l with BXMCX AYMBY BYMCY AYMCY; auto; try apply prod_comm; auto.
        apply sum_diff_diff with AY BY CY; auto.
        }
      assert (HProd3 : Prod O E E' T L3 L2).
        {
        apply prod_assoc1 with L2 IBC E; auto; try apply prod_1_r; Col.
        }
      elim (eq_dec_points O L2); intro HDiff7; treat_equalities.

        {
        assert (O = T)
          by (apply prod_uniqueness with O E E' O IBC; auto; apply prod_0_l; Col).
        apply length_id in HL2; spliter; treat_equalities.
        assert (O = AXMCX)
          by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
        treat_equalities; split; [apply prod_0_l; Col|].
        apply diff_null_eq in HAXMCX; treat_equalities.
        assert (BXMAX = BXMCX) by (apply diff_uniqueness with O E E' BX AX; auto).
        treat_equalities.
        assert (AYMBY = CYMBY).
          {
          apply prod_uniquenessA with O E E' BXMAX XProd; auto; apply prod_comm.
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          apply prod_assoc1 with AXMBX ME BYMCY; auto;
          [apply diff_2_prod with AX BX|
           apply prod_comm; apply diff_2_prod with CY BY]; auto.
          }
        assert (AY = CY); treat_equalities.
          {
          apply diff_uniquenessA with O E E' BY AYMBY; auto.
          }
        assert (O = AYMCY); treat_equalities; [|apply prod_0_l; Col].
        apply diff_uniqueness with O E E' AY AY; auto.
        apply diff_null; Col.
        }

        {
        elim (length_eq_or_opp O E E' AX CX L2 AXMCX); auto;
        try apply length_sym; auto; intro HOpp; treat_equalities.

          {
          assert (HLe6 : LtP O E E' CX AX).
            {
            assert (H : LeP O E E' CX AX).
              {
              apply compatibility_of_sum_with_order with O L2 CX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' CX CX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' CX BX) by (apply bet_lt12_le13 with AX; auto).
          assert (L3 = BXMCX) by (apply l16_9_1 with O E E' BX CX; auto; left; auto).
          treat_equalities; split; auto.
          apply prod_assoc1 with IBC L2 Pr; auto; apply prod_comm; auto.
          apply prod_assoc1 with AYMCY L3 E; auto; apply prod_comm; auto.
          apply prod_1_l; Col.
          }

          {
          assert (L2 = CXMAX); treat_equalities.
            {
            apply opp_uniqueness with O E E' AXMCX; Col; apply opp_comm; auto.
            apply diff_opp with CX AX; auto.
            }
          assert (HLe6 : LtP O E E' AX CX).
            {
            assert (H : LeP O E E' AX CX).
              {
              apply compatibility_of_sum_with_order with O L2 AX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' AX AX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' BX CX) by (apply bet_lt21_le31 with AX; auto).
          assert (L3 = CXMBX); treat_equalities.
            {
            apply l16_9_1 with O E E' CX BX; auto;
            left; auto; apply length_sym; auto.
            }
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          assert (HColT : Col O E T) by (unfold Prod, Ar2 in *; spliter; Col).
          assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
          destruct (prod_exists O E E' HNC ME T) as [OppT HMT]; Col.
          assert (Prod O E E' T BXMCX AXMCX); [|split; auto].
            {
            apply prod_assoc2 with ME L3 OppT; apply prod_comm; auto;
            [apply opp_prod; auto; apply diff_opp with CX BX; auto|
             apply prod_assoc2 with T ME L2; apply prod_comm; auto;
             apply prod_comm; apply opp_prod; auto].
            }
          destruct (opp_exists O E E' HNC IBC) as [MIBC HMIBC]; Col.
          apply prod_assoc1 with MIBC AXMCX Pr; auto; apply prod_comm; auto.

            {
            apply prod_assoc2 with ME IBC L2; auto; [|apply prod_comm];
            apply opp_prod; auto; apply diff_opp with AX CX; auto.
            }

            {
            destruct (opp_exists O E E' HNC Pr) as [MProd HMProd]; Col;
            [unfold Prod, Ar2 in *; spliter; Col|].
            apply prod_assoc2 with ME IBC MProd; auto;
            [apply opp_prod|apply prod_comm; apply opp_prod|]; auto.
            apply prod_assoc1 with AYMCY L3 E; auto; apply prod_comm; auto;
            try apply prod_1_l; Col.
            apply prod_assoc1 with ME BXMCX Pr; apply prod_comm; auto;
            apply opp_prod; auto; apply diff_opp with BX CX; auto.
            }
          }
        }
      }

      {
      assert (HBetX : Bet AX BX CX).
        {
        apply l5_12_b; [assert_diffs; ColR|
                apply length_leP_le_1 with O E E' L1 L2|
                apply length_leP_le_1 with O E E' L3 L2];
        auto; apply length_sym; auto.
        }
      rewrite characterization_of_betweenness;
      [|apply HCdA|apply HCdB|apply HCdC|
       apply HBXMAX|apply HBYMAY|apply HCXMAX|apply HCYMAY].
      assert (HDiff5 : O <> L2).
        {
        intro; treat_equalities; apply length_id in HL2; spliter; treat_equalities.
        apply HDiff1; apply diff_uniqueness with O E E' AX AX; auto;
        apply diff_null; Col.
        }
      assert (HLe3 : LeP O E E' O L2) by (apply length_pos with AX CX; auto).
      destruct (inv_exists O E E' L2) as [IAC HIAC]; Col.
      assert (HColIAC : Col O E IAC) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HLe4 : LeP O E E' O IAC) by (apply pos_inv_pos with L2; auto).
      destruct (prod_exists O E E' HNC L1 IAC) as [T HT]; Col; exists T.
      split; try (intro; treat_equalities; Col).
      split; [unfold Prod, Ar2 in *; spliter; Col|].
      assert (HLe5 : LeP O E E' O L1) by (apply length_pos with AX BX; auto).
      split; [apply compatibility_of_prod_with_order with L1 IAC; auto|].
      split; [apply le_pos_prod_le with L1 L2 IAC; auto; apply prod_comm; auto|].
      assert (HDiff6 : O <> E) by (assert_diffs; auto).
      destruct (prod_exists O E E' HNC AXMBX AYMBY) as [P HP]; Col.
      destruct (prod_exists O E E' HNC AXMCX AYMBY) as [Pr HProd1]; Col.
      assert (HSum : Sum O E E' XProd P Pr).
        {
        apply distr_l with AYMBY BXMCX AXMBX AXMCX; auto; try apply prod_comm; auto.
        apply sum_comm; Col; apply sum_diff_diff with AX BX CX; auto.
        }
      assert (HProd2 : Prod O E E' AYMCY AXMBX Pr).
        {
        destruct (prod_exists O E E' HNC AYMCY AXMBX) as [P' HP']; Col.
        assert (Pr = P'); treat_equalities; auto.
        apply sum_uniqueness with O E E' XProd P; auto.
        apply distr_l with AXMBX BYMCY AYMBY AYMCY; auto; try apply prod_comm; auto.
        apply sum_comm; Col; apply sum_diff_diff with AY BY CY; auto.
        }
      assert (HProd3 : Prod O E E' T L2 L1).
        {
        apply prod_assoc1 with L1 IAC E; auto; try apply prod_1_r; Col.
        }
      elim (eq_dec_points O L1); intro HDiff7; treat_equalities.

        {
        apply length_id in HL1; spliter; treat_equalities.
        assert (O = AXMBX)
          by (apply diff_uniqueness with O E E' AX AX; auto; apply diff_null; Col).
        treat_equalities; intuition.
        }

        {
        elim (length_eq_or_opp O E E' AX BX L1 AXMBX); auto;
        try apply length_sym; auto; intro HOpp; treat_equalities.

          {
          assert (HLe6 : LtP O E E' BX AX).
            {
            assert (H : LeP O E E' BX AX).
              {
              apply compatibility_of_sum_with_order with O L1 BX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' BX BX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' CX AX) by (apply bet_lt21_le31 with BX; auto).
          assert (L2 = AXMCX) by (apply l16_9_1 with O E E' AX CX; auto; left; auto).
          treat_equalities.
          assert (HProd4 : Prod O E E' T CXMAX BXMAX); [|split; auto].
            {
            destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
            assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
            apply prod_assoc1 with L1 IAC ME; auto;
            [|apply opp_prod; auto; apply diff_opp with AX BX; auto].
            apply prod_assoc2 with L2 ME E; auto; apply opp_prod; auto.
            apply diff_opp with AX CX; auto.
            }
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          assert (HColProd : Col O E Pr) by (unfold Prod, Ar2 in *; spliter; Col).
          destruct (opp_exists O E E' HNC Pr) as [MProd HMProd]; Col.
          apply prod_assoc1 with IAC L1 MProd; auto; apply prod_comm; auto;
          [apply prod_assoc1 with ME AYMCY Pr; auto; apply prod_comm;
           apply opp_prod; auto; apply diff_opp with AY CY; auto|].
          apply prod_assoc1 with BYMAY L2 E; apply prod_comm; auto;
          try apply prod_1_l; Col; apply prod_assoc2 with AYMBY ME Pr; auto;
          apply opp_prod; auto; apply diff_opp with AY BY; auto.
          }

          {
          assert (L1 = BXMAX); treat_equalities.
            {
            apply opp_uniqueness with O E E' AXMBX; Col; apply opp_comm; auto.
            apply diff_opp with BX AX; auto.
            }
          assert (HLe6 : LtP O E E' AX BX).
            {
            assert (H : LeP O E E' AX BX).
              {
              apply compatibility_of_sum_with_order with O L1 AX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' AX AX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' AX CX) by (apply bet_lt12_le13 with BX; auto).
          assert (L2 = CXMAX); treat_equalities.
            {
            apply l16_9_1 with O E E' CX AX; auto; left; apply length_sym; auto.
            }
          split; auto.
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          apply prod_assoc1 with IAC L1 Pr; apply prod_comm; auto;
          [apply prod_assoc1 with AYMCY ME AXMBX; auto; [|apply prod_comm];
           apply opp_prod; auto; apply diff_opp with AY CY; auto|].
          apply prod_assoc1 with BYMAY L2 E; apply prod_comm; auto;
          try apply prod_1_l; Col.
          apply prod_assoc1 with AXMCX ME AYMBY; auto; [|apply prod_comm];
          apply opp_prod; auto;
          [apply diff_opp with AX CX|apply diff_opp with BY AY]; auto.
          }
        }
      }

      {
      assert (HBetX : Bet BX CX AX).
        {
        apply l5_12_b; [assert_diffs; ColR|
                apply length_leP_le_1 with O E E' L3 L1|
                apply length_leP_le_1 with O E E' L2 L1];
        auto; apply length_sym; auto.
        }
      rewrite characterization_of_betweenness;
      [|apply HCdB|apply HCdC|apply HCdA|
       apply HCXMBX|apply HCYMBY|apply HAXMBX|apply HAYMBY].
      assert (HDiff5 : O <> L1).
        {
        intro; treat_equalities; apply length_id in HL1; spliter; treat_equalities.
        apply HDiff1; apply diff_uniqueness with O E E' AX AX; auto;
        apply diff_null; Col.
        }
      assert (HLe3 : LeP O E E' O L1) by (apply length_pos with AX BX; auto).
      destruct (inv_exists O E E' L1) as [IAB HIAB]; Col.
      assert (HColIAB : Col O E IAB) by (unfold Prod, Ar2 in *; spliter; Col).
      assert (HLe4 : LeP O E E' O IAB) by (apply pos_inv_pos with L1; auto).
      destruct (prod_exists O E E' HNC L3 IAB) as [T HT]; Col; exists T.
      split; try (intro; treat_equalities; Col).
      split; [unfold Prod, Ar2 in *; spliter; Col|].
      assert (HLe5 : LeP O E E' O L3) by (apply length_pos with BX CX; auto).
      split; [apply compatibility_of_prod_with_order with L3 IAB; auto|].
      split; [apply le_pos_prod_le with L3 L1 IAB; auto; apply prod_comm; auto|].
      assert (HDiff6 : O <> E) by (assert_diffs; auto).
      assert (HProd1 : Prod O E E' T L1 L3).
        {
        apply prod_assoc1 with L3 IAB E; auto; try apply prod_1_r; Col.
        }
      elim (eq_dec_points O L3); intro HDiff7; treat_equalities.

        {
        apply length_id in HL3; spliter; treat_equalities.
        assert (O = BXMCX)
          by (apply diff_uniqueness with O E E' BX BX; auto; apply diff_null; Col).
        treat_equalities; intuition.
        }

        {
        elim (length_eq_or_opp O E E' BX CX L3 BXMCX); auto;
        try apply length_sym; auto; intro HOpp; treat_equalities.

          {
          assert (HLe6 : LtP O E E' CX BX).
            {
            assert (H : LeP O E E' CX BX).
              {
              apply compatibility_of_sum_with_order with O L3 CX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' CX CX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' AX BX) by (apply bet_lt21_le31 with CX; auto).
          assert (L1 = BXMAX)
            by (apply l16_9_1 with O E E' BX AX; auto; left; apply length_sym; auto).
          treat_equalities.
          assert (HProd2 : Prod O E E' T AXMBX CXMBX); [|split; auto].
            {
            destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
            assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
            apply prod_assoc1 with L3 IAB ME; auto;
            [|apply opp_prod; auto; apply diff_opp with BX CX; auto].
            apply prod_assoc2 with L1 ME E; auto; apply opp_prod; auto.
            apply diff_opp with BX AX; auto.
            }
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          apply prod_assoc1 with IAB L3 XProd; auto; apply prod_comm; auto.
          apply prod_assoc1 with CYMBY L1 E; apply prod_comm; auto;
          try apply prod_1_l; Col; apply prod_assoc1 with AXMBX ME BYMCY; auto;
          [|apply prod_comm]; apply opp_prod; auto;
          [apply diff_opp with AX BX|apply diff_opp with CY BY]; auto.
          }

          {
          assert (L3 = CXMBX); treat_equalities.
            {
            apply opp_uniqueness with O E E' BXMCX; Col; apply opp_comm; auto.
            apply diff_opp with CX BX; auto.
            }
          assert (HLe6 : LtP O E E' BX CX).
            {
            assert (H : LeP O E E' BX CX).
              {
              apply compatibility_of_sum_with_order with O L3 BX; auto;
              try apply sum_O_B; Col; apply sum_comm; Col; apply diff_sum; auto.
              }
            elim H; clear H; intro H; auto; treat_equalities.
            exfalso; apply HDiff7; apply diff_uniqueness with O E E' BX BX; auto.
            apply diff_null; Col.
            }
          assert (HLe7 : LeP O E E' BX AX) by(apply bet_lt12_le13 with CX; auto).
          assert (L1 = AXMBX) by (apply l16_9_1 with O E E' AX BX; auto; left; auto).
          treat_equalities.
          split; auto.
          destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
          destruct (opp_exists O E E' HNC XProd) as [MProd HMProd]; Col.
          apply prod_assoc1 with IAB L3 MProd; apply prod_comm; auto;
          [apply prod_assoc2 with BXMCX ME XProd; auto; apply opp_prod; auto;
           apply diff_opp with BX CX; auto|].
          apply prod_assoc1 with CYMBY L1 E; apply prod_comm; auto;
          try apply prod_1_l; Col.
          apply prod_assoc2 with BYMCY ME XProd; auto; apply opp_prod; auto.
          apply diff_opp with BY CY; auto.
          }
        }
      }
    }
  }
Qed.

End T16.
