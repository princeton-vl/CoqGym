Require Export GeoCoq.Tarski_dev.Annexes.circles.
Require Export GeoCoq.Tarski_dev.Annexes.half_angles.
Require Export GeoCoq.Tarski_dev.Ch12_parallel_inter_dec.

Section Inscribed_angle.

Context `{TE:Tarski_euclidean}.

(** The sum of the angles of a triangle is the flat angle. *)

Lemma trisuma__bet : forall A B C D E F, TriSumA A B C D E F -> Bet D E F.
Proof.
  apply alternate_interior__triangle.
  unfold alternate_interior_angles_postulate.
  apply l12_21_a.
Qed.

Lemma bet__trisuma : forall A B C D E F, Bet D E F -> A <> B -> B <> C -> A <> C -> D <> E -> E <> F ->
  TriSumA A B C D E F.
Proof.
  intros A B C D E F HBet; intros.
  destruct (ex_trisuma A B C) as [P [Q [R HTri]]]; auto.
  apply conga_trisuma__trisuma with P Q R; trivial.
  assert (Hd := HTri).
  apply trisuma_distincts in Hd; spliter.
  apply conga_line; auto.
  apply (trisuma__bet A B C); trivial.
Qed.

Lemma right_saccheris : forall A B C D, Saccheri A B C D -> Per A B C.
Proof.
  apply postulates_in_euclidean_context; simpl; repeat (try (left; reflexivity); right).
Qed.

Lemma not_obtuse_saccheris : ~ hypothesis_of_obtuse_saccheri_quadrilaterals.
Proof.
  apply not_oah; right.
  unfold hypothesis_of_right_saccheri_quadrilaterals; apply right_saccheris.
Qed.

Lemma suma123231__sams : forall A B C D E F, SumA A B C B C A D E F -> SAMS D E F C A B.
Proof. exact (t22_20 not_obtuse_saccheris). Qed.

Lemma bet_suma__suma : forall A B C D E F G H I, G <> H -> H <> I ->
  Bet G H I -> SumA A B C B C A D E F -> SumA D E F C A B G H I.
Proof.
  intros A B C D E F G H I HGH HHI HBet HSuma.
  suma.assert_diffs.
  destruct (bet__trisuma A B C G H I) as [D' [E' [F' []]]]; auto.
  apply (conga3_suma__suma D' E' F' C A B G H I); try apply conga_refl; auto.
  apply (suma2__conga A B C B C A); assumption.
Qed.

Lemma high_school_exterior_angle_theorem : forall A B C B', A <> B -> B <> C -> A <> C -> A <> B' ->
  Bet B A B' -> SumA A B C B C A C A B'.
Proof.
  intros A B C B'; intros.
  assert (SumA C A B' C A B B A B').
    apply suma_sym, suma_left_comm, bet__suma; auto.
  destruct (ex_suma A B C B C A) as [D [E [F]]]; auto.
  apply (conga3_suma__suma A B C B C A D E F); try apply conga_refl; auto.
  apply sams2_suma2__conga123 with C A B B A B'.
    apply suma123231__sams; assumption.
    apply bet_suma__sams with B A B'; assumption.
    apply bet_suma__suma; auto.
    assumption.
Qed.

(** If A, B and C are points on a circle where the line AB is a diameter of the circle,
    then the angle ACB is a right angle. *)

Lemma thales_theorem : forall A B C M, ~ Col A B C ->
  Midpoint M A B -> Cong M A M C -> Per A C B.
Proof.
  apply rah__thales_postulate.
  unfold postulate_of_right_saccheri_quadrilaterals; apply right_saccheris.
Qed.

(** In a right triangle, the midpoint of the hypotenuse is the circumcenter. *)

Lemma thales_converse_theorem : forall A B C M, A <> C -> B <> C ->
  Midpoint M A B -> Per A C B -> Cong M A M C.
Proof.
  intros A B C M HAC HBC HM HPer.
  apply thales_postulate__thales_converse_postulate with B; [| |assumption..].
    unfold thales_postulate; apply thales_theorem.
  apply not_col_permutation_5, per_not_col; auto.
Qed.

Lemma bet_cong__ghalfa : forall A B C B', A <> B -> B <> C -> A <> B' ->
  Bet B A B' -> Cong A B A C -> gHalfA A B C C A B'.
Proof.
  intros A B C B' HAB HBC HAB' HBet HCong.
  apply ghalfa_chara; split.
    apply cong__acute; auto.
  assert_diffs.
  apply (conga3_suma__suma A B C B C A C A B'); try apply conga_refl; auto.
    apply high_school_exterior_angle_theorem; auto.
  apply conga_left_comm, l11_44_1_a; Cong.
Qed.

(** If the angle ACB is inscribed in a circle of center O and
    C, O lie on the same side of AB, then this angle is acute. *)

Lemma onc3_os__acute : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OS A B O C ->
  Acute A C B.
Proof.
  intros O P A B C HA HB HC HOS.
  destruct (midpoint_existence A B) as [M HM].
  assert (HNCol : ~ Col A B C) by (eapply one_side_not_col124, HOS).
  assert (HLt : Lt M A M C).
  { assert (HNCol1 : ~ Col A B O) by (eapply one_side_not_col123, HOS).
    assert (M <> O) by (intro; treat_equalities; apply HNCol1; Col).
    assert (O <> C) by (intro; treat_equalities; auto).
    assert_diffs.
    assert (Cong O A O C) by (apply (onc2__cong O P); assumption).
    destruct (angle_partition M O C); auto.
    - assert (HMO := H).
      clear H.
      destruct (l8_18_existence M O C) as [H []].
      { intro.
        destruct (acute_col__out M O C) as [_ [_ [HBet|HBet]]]; auto.
        - apply l9_9_bis in HOS.
          apply HOS.
          repeat split; Col.
          exists M; split; Col.
        - apply (le__nlt O C O M); Le.
          apply (cong2_lt__lt O M O P); Cong.
          apply bet_inc2__incs with A B; Circle; Between.
      }
      assert (Perp O M A B) by (apply mid_onc2__perp with P; auto).
      assert (HOS1 : OS A B C H).
      { apply l12_6, par_not_col_strict with C; Col.
        apply l12_9 with O M; Perp; [|Cop| |Cop].
          apply coplanar_perm_5, col_cop__cop with B; Col; Cop.
          apply coplanar_perm_5, col_cop__cop with A; Col; Cop.
      }
      assert (M <> H) by (intro; subst; apply one_side_not_col124 in HOS1; apply HOS1; Col).
      assert (Per M H C) by (apply perp_per_1, perp_left_comm, perp_col with O; Col).
      apply lt_transitivity with H C; [|assert_diffs; apply l11_46; auto].
      apply cong_lt_per2__lt_1 with O O; Cong.
        apply l8_2, per_col with M; Col; Perp.
        apply perp_per_1, perp_left_comm, perp_col1 with B; Col.
      apply bet__lt1213; auto; apply out2__bet.
        apply (acute_col_perp__out C); [apply acute_sym|..]; Col; Perp.
        apply (l9_19 A B); Col; apply one_side_transitivity with C; assumption.
    - apply lt_transitivity with O C; [|apply l11_46; auto].
      apply (cong2_lt__lt M A O A); Cong.
      apply l11_46; auto.
      left.
      apply mid_onc2__per with P B; auto.
  }
  destruct HLt as [[C' [HBet HCong]] HNCong].
  exists A, C', B; split.
    apply thales_theorem with M; trivial; intro; apply HNCol; ColR.
  assert_diffs.
  assert (C <> C') by (intro; subst; apply HNCong, HCong).
  apply os3__lta.
  - apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; [Col|apply l6_6, bet_out; Between].
      apply out_one_side; [left; intro; apply HNCol; ColR|apply l6_6, bet_out; Between].
  - apply out_one_side_1 with M; Col; apply l6_6, bet_out; auto.
  - apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; [Col|apply l6_6, bet_out; Between].
      apply out_one_side; [left; intro; apply HNCol; ColR|apply l6_6, bet_out; Between].
Qed.

Lemma inscribed_angle_aux : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  OS A B O C -> TS O C A B ->
  gHalfA A C B A O B.
Proof.
  intros O P A B C HA HB HC HOS HTS.
  destruct (segment_construction C O O P) as [C' []].
  assert_diffs.
  assert (O <> C') by (intro; treat_equalities; auto).
  assert (HCong := (onc2__cong O P)).
  apply suma_preserves_ghalfa with A C C' C' C B A O C' C' O B.
    apply (onc3_os__acute O P); assumption.
    apply ts__suma, invert_two_sides, col_two_sides with O; Side; Col.
    apply ts__suma, invert_two_sides, col_two_sides with C; Col.
    apply ghalfa_out4__ghalfa with A O A C'; try apply out_trivial; auto;
      [apply l6_6, bet_out|apply ghalfa_left_comm, bet_cong__ghalfa]; auto.
    apply ghalfa_out4__ghalfa with O B C' B; try apply out_trivial; auto;
      [apply l6_6, bet_out|apply ghalfa_right_comm, bet_cong__ghalfa]; auto.
Qed.

Lemma inscribed_angle_aux1 : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  OS A B O C -> OS O C A B ->
  gHalfA A C B A O B.
Proof.
  assert (Haux : forall O P A B C, OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  OS A B O C -> OS O C A B -> OS O B A C -> gHalfA A C B A O B).
  { intros O P A B C HA HB HC HOS1 HOS2 HOS3.
    destruct (chord_completion O P C O) as [C' [HC' HBet ]]; Circle.
    assert_diffs.
    assert (C' <> O) by (intro; treat_equalities; auto).
    assert (TS O B A C').
    { apply l9_8_2 with C; [|Side].
      apply one_side_not_col124 in HOS3.
      repeat split.
        Col.
        intro; apply HOS3; ColR.
      exists O; split; Col.
    }
    assert (HCong := (onc2__cong O P)).
    apply acute_ghalfa2_sams_suma2__ghalfa123 with B C O A C O B O C' A O C'.
    - repeat split; auto.
        right; intro; assert_cols; assert_ncols; Col.
      exists C'.
      split; CongA.
      repeat split; [Side| |Cop].
      apply l9_9_bis, invert_one_side, one_side_symmetry, os_ts1324__os; [|Side].
      apply col_one_side with C; Col; Side.
    - apply (onc3_os__acute O P); assumption.
    - exists O.
      repeat (split; CongA); [|Cop].
      apply l9_9, invert_two_sides, l9_31; Side.
    - exists C'.
      repeat (split; CongA); [Side|Cop].
    - apply ghalfa_left_comm, bet_cong__ghalfa; auto.
    - apply ghalfa_left_comm, bet_cong__ghalfa; auto.
  }
  intros O P A B C HA HB HC HOS1 HOS2.
  assert_ncols.
  destruct (cop__one_or_two_sides O B A C) as [HTS|]; Col; Cop.
    apply ghalfa_comm, Haux with P; auto; [..|apply one_side_symmetry, os_ts1324__os]; Side.
    apply Haux with P; assumption.
Qed.

(** Euclid Book III Prop 20:
    In a circle the angle at the centre is double of the angle at the circumference,
    when the angles have the same circumference as base. *)

Lemma inscribed_angle : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OS A B O C ->
  gHalfA A C B A O B.
Proof.
  intros O P A B C HA HB HC HOS.
  assert (HCong := (onc2__cong O P)).
  destruct (col_dec A O C).
  { assert_diffs.
    assert (Bet C O A) by (apply col_inc_onc2__bet with O P; Col; Circle).
    assert (O <> C) by (intro; treat_equalities; auto).
    apply ghalfa_right_comm, ghalfa_out4__ghalfa with O B B A; try apply out_trivial; auto.
      apply l6_6, bet_out; auto.
    apply bet_cong__ghalfa; auto.
  }
  destruct (col_dec B O C).
  { assert_diffs.
    assert (Bet C O B) by (apply col_inc_onc2__bet with O P; Col; Circle).
    assert (O <> C) by (intro; treat_equalities; auto).
    apply ghalfa_left_comm, ghalfa_out4__ghalfa with O A A B; try apply out_trivial; auto.
      apply l6_6, bet_out; auto.
    apply bet_cong__ghalfa; auto.
  }
  destruct (cop__one_or_two_sides O C A B); Cop.
    apply inscribed_angle_aux with P; assumption.
    apply inscribed_angle_aux1 with P; assumption.
Qed.

Lemma diam_onc2_ts__suppa : forall O P A B C C',
  OnCircle A O P -> OnCircle B O P -> Diam C C' O P -> TS A B C C' ->
  SuppA A C B A C' B.
Proof.
  intros O P A B C C' HA HB [HBet [HC HC']] HTS.
  assert_diffs.
  assert (HCong := onc2__cong O P).
  assert (HMid : Midpoint O C C') by (split; Cong).
  assert (C <> C') by (intro; treat_equalities; auto).
  assert (HNColA : ~ Col C C' A) by (apply (onc3__ncol O P); auto).
  assert (HNColB : ~ Col C C' B) by (apply (onc3__ncol O P); auto).
  assert (HSumaA : SumA A C C' C C' A C A C') by (apply cong_mid__suma with O; auto).
  assert (HSumaB : SumA B C C' C C' B C B C') by (apply cong_mid__suma with O; auto).
  assert (Per C A C') by (apply thales_theorem with O; auto).
  assert (Per C B C') by (apply thales_theorem with O; auto).
  assert (HSuma : SumA C A C' C B C' C O C') by (assert_diffs; apply bet_per2__suma; auto).
  apply bet_suma__suppa with C O C'; trivial.
  destruct (ex_suma C A C' C' C B) as [D [E [F HSuma1]]]; auto.
  assert (HTS2 : TS C C' A B) by (apply (chord_intersection O P); assumption).
  assert (HTS3 : TS C' C A B) by (apply invert_two_sides, HTS2).
  assert (Acute C' C A).
  { assert_diffs; apply acute_out2__acute with O A.
      apply l6_6, bet_out; auto.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (Acute C' C B).
  { assert_diffs; apply acute_out2__acute with O B.
      apply l6_6, bet_out; auto.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (Acute C C' A).
  { assert_diffs; apply acute_out2__acute with O A.
      apply l6_6, bet_out; Between.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (Acute C C' B).
  { assert_diffs; apply acute_out2__acute with O B.
      apply l6_6, bet_out; Between.
      apply out_trivial; auto.
      apply cong__acute; auto.
  }
  assert (HSuma2 : SumA A C B A C' C D E F).
    apply suma_sym, suma_assoc_1 with A C C' C' C B C A C'; SumA.
  assert (HSAMS : SAMS A C B A C' C).
    apply sams_sym, sams_assoc_1 with A C C' C' C B C A C'; SumA.
  apply suma_assoc_1 with A C' C C C' B D E F; [SumA..|].
  apply suma_assoc_2 with C A C' B C C' C B C'; SumA.
Qed.

(** In a circle the angle at the centre is double of the angle at the circumference. *)

Lemma inscribed_angle_1 : forall O P A B C, A <> B -> B <> C -> A <> C ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> Coplanar A B C O ->
  SumA A C B A C B A O B.
Proof.
  intros O P A B C HAB HBC HAC HA HB HC HCop.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  destruct (col_dec A B O).
  { assert (Midpoint O A B) by (apply col_onc2__mid with P; auto).
    assert (Per A C B) by (apply thales_theorem with O; auto; apply cong_transitivity with O P; Cong).
    assert_diffs; apply bet_per2__suma; Between.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  - destruct (chord_completion O P C O) as [C' []]; Circle.
    assert (TS A B C' C) by (apply l9_2, bet_ts__ts with O; Side).
    assert (SuppA A C' B A C B).
      apply (diam_onc2_ts__suppa O P); [..|repeat split|]; Between.
    apply (suma_suppa2__suma A C' B A C' B); trivial.
    apply ghalfa__suma, inscribed_angle with P; trivial.
    exists C; split; trivial.
  - apply ghalfa__suma, inscribed_angle with P; trivial.
Qed.

(** If two angles ACB and ADB are inscribed in the same circle,
    then they are either congruent or supplementary. *)

Lemma cop2_onc4__or_conga_suppa : forall O P A B C C',
  A <> B -> B <> C -> A <> C -> B <> C' -> A <> C' ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OnCircle C' O P ->
  Coplanar A B C O -> Coplanar A B C' O ->
  CongA A C B A C' B \/ SuppA A C B A C' B.
Proof.
  intros O P A B C C'; intros.
  apply suma2__or_conga_suppa with A O B; trivial; apply inscribed_angle_1 with P; assumption.
Qed.

(** If the angle ACB is inscribed in a circle of center O and
    C, O lie on opposite sides of AB, then this angle is obtuse. *)

Lemma onc3_ts__obtuse : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> TS A B O C ->
  Obtuse A C B.
Proof.
  intros O P A B C HA HB HC HTS.
  destruct (chord_completion O P C O) as [C' []]; Circle.
  assert (TS A B C C') by (apply bet_ts__ts with O; Side).
  apply (acute_suppa__obtuse A C' B).
    apply (onc3_os__acute O P); trivial; exists C; split; Side.
  apply (diam_onc2_ts__suppa O P); Side.
  repeat split; Between.
Qed.

(** Euclid Book III Prop 21:
    In a circle the angles in the same segment are equal to one another. *)

Lemma cop_onc4_os__conga : forall O P A B C C',
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OnCircle C' O P ->
  OS A B C C' -> Coplanar A B C O ->
  CongA A C B A C' B.
Proof.
  intros O P A B C C' HA HB HC HC' HOS HCop.
  assert_ncols.
  destruct (col_dec A B O).
  { assert_diffs.
    assert (Midpoint O A B) by (apply col_onc2__mid with P; auto).
    apply l11_16; auto; apply thales_theorem with O; Col; apply cong_transitivity with O P; Cong.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  - assert_diffs; destruct (cop2_onc4__or_conga_suppa O P A B C C') as [|Habs]; auto.
      apply coplanar_trans_1 with C; Col; Cop.
    exfalso.
    apply (nlta A C' B), acute_obtuse__lta.
      apply (obtuse_suppa__acute A C B); [apply (onc3_ts__obtuse O P)|]; trivial.
      apply (onc3_ts__obtuse O P); trivial; apply l9_2, l9_8_2 with C; Side.
  - apply ghalfa2__conga_2 with A O B; apply inscribed_angle with P; trivial.
    apply one_side_transitivity with C; Side.
Qed.

(** Euclid Book III Prop 22:
    The opposite angles of quadrilaterals in circles are equal to two right angles. *)

Lemma cop_onc4_ts__suppa : forall O P A B C C',
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OnCircle C' O P ->
  TS A B C C' -> Coplanar A B C O ->
  SuppA A C B A C' B.
Proof.
  intros O P A B C C' HA HB.
  revert C C'.
  assert (Haux : forall C C', OnCircle C O P -> OnCircle C' O P -> TS A B C C' -> OS A B O C ->
    SuppA A C B A C' B).
  { intros C C' HC HC' HTS HOS.
    assert_diffs.
    assert (~ Col C A B) by (destruct HTS; assumption).
    assert (Coplanar A B C' O) by (apply coplanar_trans_1 with C; Cop).
    destruct (cop2_onc4__or_conga_suppa O P A B C C') as [Habs|]; Cop.
    exfalso.
    assert (HLta : LtA A C B A C' B); [|destruct HLta as [_ HN]; apply HN, Habs].
    apply acute_obtuse__lta.
      apply (onc3_os__acute O P); assumption.
    apply (onc3_ts__obtuse O P); trivial.
    apply l9_8_2 with C; Side.
  }
  intros C C' HC HC' HTS HCop.
  assert (~ Col C A B) by (destruct HTS; assumption).
  destruct (col_dec A B O).
  { assert_diffs.
    assert (Midpoint O A B) by (apply col_onc2__mid with P; auto).
    destruct HTS as [_ []].
    apply per2__suppa; auto; apply thales_theorem with O; Col; apply cong_transitivity with O P; Cong.
  }
  destruct (cop__one_or_two_sides A B O C); Col; Cop.
  apply suppa_sym, Haux; [..|exists C; split]; Side.
Qed.

(** If the angle ACB is acute and inscribed in a circle of center O,
    then C and O lie on the same side of AB. *)

Lemma acute_cop_onc3__os : forall O P A B C, A <> B ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> Coplanar A B C O -> Acute A C B ->
  OS A B O C.
Proof.
  intros O P A B C HAB HA HB HC HCop HAcute.
  assert_diffs.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  apply coplanar_perm_1 in HCop.
  apply cop__not_two_sides_one_side; Col; intro Habs; apply (nlta A C B).
  - apply acute_per__lta; auto.
    apply thales_theorem with O; trivial.
      apply col_onc2__mid with P; Col.
      apply (onc2__cong O P); assumption.
  - apply acute_obtuse__lta; trivial.
    apply (onc3_ts__obtuse O P); assumption.
Qed.

(** If the angle ACB is obtuse and inscribed in a circle of center O,
    then C and O lie on opposite sides of AB. *)

Lemma cop_obtuse_onc3__ts : forall O P A B C,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> Coplanar A B C O -> Obtuse A C B ->
  TS A B O C.
Proof.
  intros O P A B C HA HB HC HCop HObtuse.
  assert_diffs.
  assert (~ Col A B C) by (apply (onc3__ncol O P); auto).
  apply coplanar_perm_1 in HCop.
  apply cop__not_one_side_two_sides; Col; intro Habs; apply (nlta A C B).
  - apply obtuse_per__lta; auto.
    apply thales_theorem with O; trivial.
      apply col_onc2__mid with P; Col.
      apply (onc2__cong O P); assumption.
  - apply acute_obtuse__lta; trivial.
    apply (onc3_os__acute O P); assumption.
Qed.

(** If the angles ACB and ADB are congruent and inscribed in the same circle,
    then C and D lie on the same side of AB. *)

Lemma conga_cop2_onc4__os : forall O P A B C D, ~ Col A B O ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OnCircle D O P ->
  Coplanar A B O C -> Coplanar A B O D -> CongA A C B A D B ->
  OS A B C D.
Proof.
  intros O P A B C D HNCol HA HB HC HD HCopC HCopD HConga.
  assert_diffs.
  destruct (angle_partition A C B) as [HAcute|[HPer|HObtuse]]; auto.
  - apply one_side_transitivity with O; [apply one_side_symmetry|];
      apply acute_cop_onc3__os with P; Cop.
    apply (acute_conga__acute A C B); assumption.
  - exfalso.
    apply HNCol, col_permutation_1, midpoint_col.
    destruct (midpoint_existence A B) as [M HM].
    assert (M = O); [|subst; apply HM].
    assert (HCong := onc2__cong O P).
    apply (cong4_cop2__eq A C B); Cong; [..|Cop|Cop].
      apply per_not_col; auto.
      apply cong_commutativity, thales_converse_theorem with B; auto.
  - exists O; split; apply l9_2; apply cop_obtuse_onc3__ts with P; Cop.
    apply (conga_obtuse__obtuse A C B); assumption.
Qed.

(** If the angles ACB and ADB are supplementary and inscribed in the same circle,
    then C and D lie on opposite sides of AB. *)

Lemma cop2_onc4_suppa__ts : forall O P A B C D, ~ Col A B O ->
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> OnCircle D O P ->
  Coplanar A B O C -> Coplanar A B O D -> SuppA A C B A D B ->
  TS A B C D.
Proof.
  intros O P A B C D HNCol HA HB HC HD HCopC HCopD HSuppa.
  assert_diffs.
  destruct (angle_partition A C B) as [HAcute|[HPer|HObtuse]]; auto.
  - apply l9_8_2 with O.
      apply cop_obtuse_onc3__ts with P; Cop; apply (acute_suppa__obtuse A C B); assumption.
      apply acute_cop_onc3__os with P; Cop.
  - exfalso.
    apply HNCol, col_permutation_1, midpoint_col.
    destruct (midpoint_existence A B) as [M HM].
    assert (M = O); [|subst; apply HM].
    assert (HCong := onc2__cong O P).
    apply (cong4_cop2__eq A C B); Cong; [..|Cop|Cop].
      apply per_not_col; auto.
      apply cong_commutativity, thales_converse_theorem with B; auto.
  - apply l9_2, l9_8_2 with O.
      apply cop_obtuse_onc3__ts with P; Cop.
    apply acute_cop_onc3__os with P; Cop; apply (obtuse_suppa__acute A C B); assumption.
Qed.

(** Non degenerated triangles can be circumscribed. *)

Lemma triangle_circumscription : forall A B C, ~ Col A B C ->
  exists CC : Tpoint, Cong A CC B CC /\ Cong A CC C CC /\ Coplanar A B C CC.
Proof.
  apply postulates_in_euclidean_context; simpl; repeat (try (left; reflexivity); right).
Qed.

(** Euclid Book III Prop 23:
    On the same straight line there cannot be constructed
    two similar and unequal segments of circles on the same side. *)

Lemma conga_cop_onc6_os__eq : forall A B C D O P O' P',
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P -> Coplanar A B C O ->
  OnCircle A O' P' -> OnCircle B O' P' -> OnCircle D O' P' -> Coplanar A B D O' ->
  OS A B C D -> CongA A C B A D B ->
  (O = O' /\ Cong O P O' P').
Proof.
  intros A B C D O P O' P' HA HB HC HCop HA' HB' HD' HCop' HOS HConga.
  assert (O = O'); [|split; trivial; subst O'; apply cong_transitivity with O A; Cong].
  assert (HNCol : ~ Col A B C) by (apply one_side_not_col123 with D, HOS).
  assert (HCong := onc2__cong O P).
  destruct (col_dec A B O) as [|HNCol1].
  { assert_diffs.
    apply cong2_cop2_onc3__eq with P' A B D; auto; [|apply coplanar_trans_1 with C; Col; Cop].
    assert (Midpoint O A B) by (apply col_onc2__mid with P; assumption).
    apply thales_converse_theorem with B; auto.
    apply (l11_17 A C B); trivial.
    apply thales_theorem with O; Cong.
  }
  assert (HNCol' : ~ Col A B D) by (apply one_side_not_col124 with C, HOS).
  assert (HCong' := onc2__cong O' P').
  destruct (midpoint_existence A B) as [M HM].
  assert (HOS1 : OS A B O O').
  { assert_diffs; destruct (angle_partition A C B) as [HAcute|[HPer|HObtuse]]; auto.
    - apply one_side_transitivity with C;
        [|apply one_side_transitivity with D; trivial; apply one_side_symmetry].
        apply acute_cop_onc3__os with P; auto.
      apply acute_cop_onc3__os with P'; auto.
      apply (acute_conga__acute A C B); assumption.
    - exfalso.
      apply HNCol1.
      assert (O = M); [|subst; Col].
      apply (cong4_cop2__eq A B C); Cong; [|Cop].
      apply cong_commutativity, thales_converse_theorem with B; auto.
    - exists C; split; [|apply l9_2, l9_8_2 with D; [apply l9_2|Side]].
        apply cop_obtuse_onc3__ts with P; auto.
      apply cop_obtuse_onc3__ts with P'; auto.
      apply (conga_obtuse__obtuse A C B); assumption.
  }
  assert (HNCol1' : ~ Col A B O') by (apply one_side_not_col124 with O, HOS1).
  destruct (bet_cop_onc2__ex_onc_os_out O P A B C M) as [C1]; Between; Col; [assert_diffs; auto..|].
  destruct (bet_cop_onc2__ex_onc_os_out O' P' A B D M) as [D1]; Between; Col; [assert_diffs; auto..|].
  spliter.
  assert (HNCol2 : ~ Col A B C1) by (apply one_side_not_col124 with C; assumption).
  assert (HOut : Out M C1 D1).
  { apply (l9_19 A B); [Col| |
      apply one_side_transitivity with C; [|apply one_side_transitivity with D]; Side].
    assert (O <> M) by (intro; subst; apply HNCol1; Col).
    assert (O' <> M) by (intro; subst; apply HNCol1'; Col).
    assert (Col O O' M); [|ColR].
    assert_diffs; apply (cop_per2__col A); auto;
      [|apply mid_onc2__per with P B; auto|apply mid_onc2__per with P' B; auto].
    apply coplanar_trans_1 with B; Col; [|Cop].
    apply coplanar_trans_1 with C; Col; [Cop|].
    apply coplanar_perm_12, coplanar_trans_1 with D; Col; Cop.
  }
  destruct (eq_dec_points C1 D1).
  { subst D1.
    apply (cong4_cop2__eq A B C1); Cong; exists M; left; split; Col.
  }
  assert (HNCol2' : ~ Col A B D1) by (apply one_side_not_col124 with D; assumption).
  assert (CongA A C1 B A C B) by (apply (cop_onc4_os__conga O P); Side; exists M; left; split; Col).
  assert (CongA A D1 B A D B) by (apply (cop_onc4_os__conga O' P'); Side; exists M; left; split; Col).
  assert (Out A B M) by (assert_diffs; apply l6_6, bet_out; Between).
  assert (Out B A M) by (assert_diffs; apply l6_6, bet_out; Between).
  assert (HH := HOut).
  destruct HH as [HMC1 [HMD1 [HBet|HBet]]]; exfalso.
  - apply (lta_not_conga A D B A C B); CongA.
    apply (conga_preserves_lta A D1 B A C1 B); trivial.
    assert (Out D1 M C1) by (apply l6_6, bet_out; Between).
    apply os3__lta; [|apply one_side_symmetry, l9_19 with M; Col|];
      apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2'; ColR.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2'; ColR.
  - apply (lta_not_conga A C B A D B); trivial.
    apply (conga_preserves_lta A C1 B A D1 B); trivial.
    assert (Out C1 M D1) by (apply l6_6, bet_out; Between).
    apply os3__lta; [|apply l9_19 with M; Col|];
      apply one_side_transitivity with M.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2; ColR.
      apply invert_one_side, out_one_side; Col.
      apply out_one_side; trivial; left; intro; apply HNCol2; ColR.
Qed.

Lemma conga_cop_onc3_os__onc : forall A B C D O P,
  OnCircle A O P -> OnCircle B O P -> OnCircle C O P ->
  Coplanar A B C O -> OS A B C D -> CongA A C B A D B ->
  OnCircle D O P.
Proof.
  intros A B C D O P HA HB HC HCop HOS HConga.
  destruct (triangle_circumscription A B D) as [O'].
    apply one_side_not_col124 in HOS; Col.
  spliter.
  assert (OnCircle A O' A /\ OnCircle B O' A /\ OnCircle D O' A).
    unfold OnCircle; repeat split; Cong.
  spliter.
  destruct (conga_cop_onc6_os__eq A B C D O P O' A); trivial.
  subst O'; apply cong_transitivity with O A; Cong.
Qed.

(** If the angles ACB and ADB are congruent and C, D lie on the same side of AB,
    then A, B, C and D are concyclic. *)

Lemma conga_os__ex_circle : forall A B C D,
  OS A B C D -> CongA A C B A D B -> exists O P,
  OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P /\ Coplanar A B C O.
Proof.
  intros A B C D HOS HConga.
  destruct (triangle_circumscription A B C) as [O]; spliter.
    apply one_side_not_col123 with D, HOS.
  assert (OnCircle A O A /\ OnCircle B O A /\ OnCircle C O A).
    unfold OnCircle; repeat split; Cong.
  spliter.
  exists O, A; repeat split; trivial.
  apply (conga_cop_onc3_os__onc A B C); assumption.
Qed.

(** If the angles ACB and ADB are supplementary and C, D lie on opposite sides of AB,
    then A, B, C and D are concyclic. *)

Lemma suppa_ts__ex_circle : forall A B C D,
  TS A B C D -> SuppA A C B A D B -> exists O P,
  OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P /\ Coplanar A B C O.
Proof.
  intros A B.
  assert (Haux : forall C D, TS A B C D -> Obtuse A C B -> SuppA A C B A D B -> exists O P,
    OnCircle A O P /\ OnCircle B O P /\ OnCircle C O P /\ OnCircle D O P /\ Coplanar A B C O).
  { intros C D HTS HObtuse HSuppa.
    assert (HNCol : ~ Col A B C) by (destruct HTS; Col).
    destruct (triangle_circumscription A B C HNCol) as [O]; spliter.
    assert (OnCircle A O A /\ OnCircle B O A /\ OnCircle C O A).
      unfold OnCircle; repeat split; Cong.
    spliter.
    exists O, A; repeat split; trivial.
    destruct (chord_completion O A C O) as [C'[HC' HBet]]; Circle.
    assert (TS A B C C').
      apply bet_ts__ts with O; [apply l9_2, cop_obtuse_onc3__ts with A|]; assumption.
    apply (conga_cop_onc3_os__onc A B C'); trivial.
      apply coplanar_trans_1 with C; Col; Cop.
      exists C; split; Side.
      apply (suppa2__conga456 A C B); [apply (cop_onc4_ts__suppa O A)|]; assumption.
  }
  intros C D HTS HSuppa.
  assert_diffs; destruct (angle_partition A C B) as [|[|]]; auto.
  { destruct (Haux D C) as [O [P]].
      Side.
      apply (acute_suppa__obtuse A C B); trivial.
      apply suppa_sym, HSuppa.
    exists O, P.
    spliter; repeat split; trivial.
    apply coplanar_trans_1 with D; [destruct HTS as [_ []]; Col|Cop..].
  }
  destruct (midpoint_existence A B) as [M].
  exists M, A.
  destruct HTS as [HNCol1 [HNCol2 _]].
  unfold OnCircle; repeat split; [Cong..| | |Cop];
    apply cong_symmetry, thales_converse_theorem with B; auto.
  apply (per_suppa__per A C B); assumption.
Qed.

(** In a convex quadrilateral, if two opposite angles are supplementary
    then the two other angles are also supplementary. *)

Lemma suppa_ts2__suppa : forall A B C D,
  TS A C B D -> TS B D A C -> SuppA A B C A D C -> SuppA B A D B C D.
Proof.
  intros A B C D HTS1 HTS2 HSuppa.
  destruct (suppa_ts__ex_circle A C B D) as [O [P]]; trivial.
  spliter.
  apply (cop_onc4_ts__suppa O P); trivial.
  apply coplanar_perm_2, coplanar_trans_1 with C; [destruct HTS1; Col|Cop..].
Qed.

End Inscribed_angle.

Section Inscribed_angle_2.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma chord_par_diam : forall O P A B C C' A' U,
 O <> P -> ~Col A B C' -> Diam C C' O P -> Midpoint A' A C' -> OnCircle A O P -> OnCircle B O P ->
 Col A B U -> Perp O U A B -> Par A C' O U -> B = C.
Proof.
intros.
assert_diffs.
assert(Midpoint U A B).
{
  apply(col_onc2_perp__mid O P A B U); Col.
}
assert(O <> A').
intro.
treat_equalities.
induction H7.
apply H7.
exists O.
split; Col.
spliter.
assert(Perp A U  O U).
{
  apply perp_sym in H6.
  apply (perp_col A B O U U); Col.
  intro.
  treat_equalities.
  apply perp_distinct in H6.
  tauto.
}
apply perp_left_comm in H18.
apply perp_not_col in H18.
apply H18; Col.
unfold Diam in H1.
spliter.
assert(HH:=mid_onc2__perp O P A C' A' H15 H13 H3 H17 H2).
assert(Perp O U O A').
{
  apply(par_perp__perp A C' O U O A' H7); Perp.
}

assert(Par O A' A B).
{
  apply (l12_9_2D _ _ _ _ O U); Perp.
}
assert(HM:=midpoint_existence B C').
ex_and HM O'.
assert(HP:= triangle_mid_par A B C' O' A' H0 H20 H2).
apply par_strict_par in HP.
assert(Par O A' A' O').
{
  apply (par_trans _ _ A B); Par.
}
assert(Col O O' A').
{
  induction H21.
  apply False_ind.
  apply H21.
  exists A'.
  split; Col.
  spliter.
  Col.
}

induction(eq_dec_points O O').
treat_equalities.
eapply(symmetric_point_uniqueness C' O); Midpoint.
split; eCong.
Between.

assert(HQ:= mid_onc2__perp O P B C' O' H23  H10 H4 H17 H20).
apply(perp_col O A' A C' O') in HH; Col.
assert(Par A C' B C').
{
  apply(l12_9_2D A C' B C' O O'); Perp.
}
apply False_ind.
induction H24.
apply H24.
exists C'.
split;Col.
spliter.
apply H0.
Col.
Qed.

End Inscribed_angle_2.
