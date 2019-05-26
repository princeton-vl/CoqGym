Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.archimedes.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section Archimedes_for_angles.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma grada_distincts : forall A B C D E F,
  GradA A B C D E F ->
  A <> B /\ C <> B /\ D <> E /\ F <> E.
Proof.
  induction 1.
    assert_diffs; repeat split; trivial.
  apply suma_distincts in H2; spliter; repeat split; auto.
Qed.

Lemma conga2_grada__grada : forall A B C D E F A' B' C' D' E' F',
  GradA A B C D E F ->
  CongA A B C A' B' C' -> CongA D E F D' E' F' ->
  GradA A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HGA.
  revert A' B' C' D' E' F'.
  induction HGA; intros A' B' C' D' E' F' Hconga1 Hconga2.
    apply grada_init, conga_trans with D E F; trivial; apply conga_trans with A B C; CongA.
  suma.assert_diffs.
  assert (Hconga3 : CongA D E F D E F) by CongA.
  apply grada_stab with D E F.
    apply (IHHGA A' B' C' D E F); trivial.
    apply (conga2_sams__sams D E F A B C); trivial.
  apply (conga3_suma__suma D E F A B C G H I); trivial.
Qed.

Lemma grada__lea : forall A B C D E F, GradA A B C D E F -> LeA A B C D E F.
Proof.
  intros A B C D E F.
  induction 1.
    Lea.
  apply lea_trans with D E F; trivial.
  apply sams_suma__lea123789 with A B C; trivial.
Qed.

Lemma grada_out__out : forall A B C D E F,
  Out E D F -> GradA A B C D E F ->
  Out B A C.
Proof.
  intros A B C D E F Hout HGA.
  apply out_lea__out with D E F; trivial.
  apply grada__lea; trivial.
Qed.

Lemma grada2_sams_suma__grada : forall A B C D E F G H I K L M,
  GradA A B C D E F -> GradA A B C G H I ->
  SAMS D E F G H I -> SumA D E F G H I K L M ->
  GradA A B C K L M.
Proof.
  intros A B C D E F G H I K L M HGA1 HGA2 HIsi.
  revert K L M.
  induction HGA2.
  { rename H into HConga; rename D0 into G; rename E0 into H; rename F0 into I.
    intros K L M HSuma.
    suma.assert_diffs.
    apply (conga2_sams__sams D E F G H I D E F A B C) in HIsi; CongA.
    apply (conga3_suma__suma D E F G H I K L M D E F A B C K L M) in HSuma; CongA.
    apply grada_stab with D E F; trivial.
  }
  assert (Hd1 := sams_distincts D0 E0 F0 A B C H0); assert (Hd2 := sams_distincts D E F G H I HIsi); spliter.
  destruct (ex_suma D E F D0 E0 F0) as [K [L [M HSuma]]]; auto.
  intros K0 L0 M0 HSuma2.
  assert (HIsi2 : SAMS D E F D0 E0 F0).
    apply sams_lea2__sams with D E F G H I; Lea.
    apply sams_suma__lea123789 with A B C; trivial.
  apply grada_stab with K L M.
    apply IHHGA2; trivial.
    apply sams_assoc_2 with D E F D0 E0 F0 G H I; trivial.
  apply suma_assoc_2 with D E F D0 E0 F0 G H I; trivial.
Qed.

Lemma gradaexp__grada : forall A B C D E F,
  GradAExp A B C D E F -> GradA A B C D E F.
Proof.
  intros A B C.
  induction 1; [apply grada_init | apply grada2_sams_suma__grada with D E F D E F]; trivial.
Qed.

Lemma acute_archi_aux : forall O A B C D E,
  Per O A B -> O <> A -> B <> A -> C <> D -> D <> E ->
  Bet A C D -> Bet C D E -> Bet D E B -> CongA C O D D O E ->
  Lt C D D E.
Proof.
  intros O A B C D E HPer HOA HBA HCD HDE HBet1 HBet2 HBet3 HCongA.
  assert_diffs.
  assert (HNCol1 : ~ Col O A B) by (apply per_not_col; auto).
  assert (HNCol2 : ~ Col O A D).
    intro; elim (eq_dec_points A C); intro; assert_cols; treat_equalities; apply HNCol1; ColR.
  destruct (angle_construction_1 A D O O D E) as [P [HP1 HP2]]; Col.
    intro; apply HNCol2; ColR.
  assert (HAcute : Acute A D O).
    apply l11_43_aux; Col; left; apply l8_2, per_col with B; auto; ColR.
  assert (HF : InAngle P O D E).
  { apply lea_in_angle; Side.
    apply (l11_30 A D O E D O); CongA.
    destruct (acute_chara A D O E) as [HD HI]; eBetween.
    apply lta__lea, HD, HAcute.
  }
  destruct HF as [_ [_ [HDP [F [HBet4 [Heq|HOut]]]]]].
    exfalso; subst F; apply HNCol2; ColR.
  assert_diffs.
  apply l6_6 in HOut.
  assert (HCongA1 : CongA A D O O D F).
    apply (out_conga A D O O D P); trivial; apply out_trivial; auto.
  assert (HCongA2 : CongA O D C A D O).
    elim (eq_dec_points A C); intro.
      treat_equalities; CongA.
    apply (out_conga O D C C D O); CongA; try (apply out_trivial; auto); apply bet_out; eBetween.
  clear dependent P.
  assert (HNCol3 : ~ Col O D F) by (apply (ncol_conga_ncol A D O); Col).
  assert_diffs.
  destruct (l11_50_1 O D C O D F) as [HCong1 [HCong2 HCongA3]]; Cong.
    intro; apply HNCol2; ColR.
    apply (out_conga D O C D O E); CongA; try (apply out_trivial; auto); apply l6_6, bet_out; auto.
    apply conga_trans with A D O; trivial.
  apply (cong2_lt__lt D F D E); Cong.
  assert (HNCol4 : ~ Col E D F).
  { intro; elim (eq_dec_points E F); intro; [|apply HNCol3; ColR].
    treat_equalities.
    apply (acute_not_per A D O); trivial.
    apply l8_2, per_col with C; Col.
    exists E; repeat split; Cong.
  }
  assert_diffs.
  apply l11_44_2_b; trivial.
  apply lta_trans with F D O.
  - destruct (l11_41 D E O C) as [Hlta1 Hlta2]; Between.
      intro; apply HNCol3; ColR.
    apply (conga_preserves_lta D E O O D C); trivial;
    [apply (out_conga D E F D E F)|apply (out_conga O D A F D O)]; CongA;
    try (apply out_trivial; auto).
      apply bet_out; Between.
    apply l6_6, bet_out; eBetween.
  - destruct (l11_41 F O D E); Col.
Qed.

Lemma acute_archi_aux1 : forall O A0 A1 B P Q R,
  Per O A0 B -> B <> A0 -> Bet A0 A1 B ->
  GradA A0 O A1 P Q R -> A0 <> A1 ->
  LeA A0 O B P Q R \/ exists A, Bet A0 A1 A /\ Bet A0 A B /\ CongA P Q R A0 O A.
Proof.
  intros O A0 A1 B P Q R HPer HBA0 HBet HGA HA0A1.
  assert (Hdiff := grada_distincts A0 O A1 P Q R HGA); spliter.
  assert (HNCol : ~ Col O A0 B) by (apply per_not_col; auto).
  assert_diffs.
  elim (lea_total A0 O B P Q R); auto.
  intro HLeA; right.
  assert (HNCol2 : ~ Col P Q R).
  { intro HCol.
    assert (HBet1 : Bet P Q R).
      apply not_out_bet; trivial.
      intro HOut; assert (Out O A0 A1) by (apply grada_out__out with P Q R; trivial).
      apply HNCol; ColR.
    assert (Bet A0 O B); assert_cols; Col.
    apply bet_lea__bet with P Q R; trivial.
  }
  destruct (angle_construction_1 P Q R A0 O B) as [C [Hconga HOS]]; Col.
  assert (HA : InAngle C A0 O B).
    apply lea_in_angle; Side; apply (l11_30 P Q R A0 O B); CongA.
  destruct HA as [_ [_ [HCO [A [HA HUn]]]]].
  destruct HUn as [Heq|Hout].
    exfalso; treat_equalities; apply HNCol; Col.
  exists A.
  apply (out_conga P Q R A0 O C P R A0 A) in Hconga; try (apply out_trivial; auto); [|apply l6_6; trivial].
  repeat (split; trivial).
  elim (eq_dec_points A1 A).
    intro; subst A; Between.
  intro HAA1.
  apply (ncol_conga_ncol P Q R A0 O A) in HNCol2; trivial.
  assert (HInangle : InAngle A1 A0 O A).
  { apply lea_in_angle.
      apply (l11_30 A0 O A1 P Q R); CongA; apply grada__lea; trivial.
    apply out_one_side; auto.
    assert_diffs.
    apply l6_7 with B; [|apply l6_6]; apply bet_out; auto.
  }
  destruct HInangle as [_ [_ [_ [X [HX1 HUn]]]]].
  destruct HUn as [HX2|HX2].
    subst X; exfalso; Col.
  elim (eq_dec_points X A1); intro.
    subst X; trivial.
  exfalso; apply HNCol2; assert_diffs; ColR.
Qed.

Lemma acute_archi_aux2 : forall O A0 A1 B C,
  Per O A0 B -> O <> A0 -> B <> A0 ->
  Bet A0 A1 B -> A0 <> A1 -> Grad A0 A1 C ->
  exists P, exists Q, exists R, GradA A0 O A1 P Q R /\ (LeA A0 O B P Q R \/
  exists A', Bet A0 A1 A' /\ Bet A0 A' B /\ CongA P Q R A0 O A' /\ Le A0 C A0 A' /\
  exists A, Bet A0 A A' /\ CongA A O A' A0 O A1 /\ Le A0 A1 A A').
Proof.
  intros O A0 A1 B E HPer HOA0 HBA0 HBet HA0A1 HG.
  assert (HNCol : ~ Col O A0 B) by (apply per_not_col; auto).
  assert (HNCol1 : ~ Col A0 O A1) by (intro; apply HNCol; ColR).
  assert_diffs.
  induction HG; rename A into A0; rename B0 into A1.
    exists A0; exists O; exists A1; split; [apply grada_init; CongA|].
    right; exists A1; repeat (split; CongA); Between; Le.
    exists A0; repeat (split; CongA); Between; Le.
  destruct IHHG as [P [Q [R [HGA HUn]]]]; auto.
  destruct HUn as [HLea|HA'].
    exists P; exists Q; exists R; split; trivial; left; trivial.
  destruct HA' as [A' [HBet1' [HBet2' [HConga' [HLe' HA]]]]].
  destruct HA as [A [HBet1 [HConga HLe]]].
  assert (HIsi : SAMS P Q R A0 O A1).
  { apply sams_lea2__sams with A0 O B A0 O B.
    - apply acute__sams, l11_43_aux; Col.
    - apply (l11_30 A0 O A' A0 O B); CongA.
      exists A'; assert_diffs; split; CongA.
      repeat split; auto.
      exists A'; split; trivial.
      right; apply out_trivial; auto.
    - exists A1; split; CongA.
      repeat split; auto.
      exists A1; split; trivial.
      right; apply out_trivial; auto.
  }
  assert_diffs.
  destruct (ex_suma P Q R A0 O A1) as [P' [Q' [R' HSuma]]]; auto.
  assert (HGA' : GradA A0 O A1 P' Q' R') by (apply grada_stab with P Q R; trivial).
  exists P'; exists Q'; exists R'; split; trivial.
  destruct (acute_archi_aux1 O A0 A1 B P' Q' R') as [HLea|HA'']; auto.
  right; destruct HA'' as [A'' [HBet1'' [HBet2'' HConga'']]].
  assert (HNCol2 : ~ Col A O A') by (apply (ncol_conga_ncol A0 O A1); Col; CongA).
  assert (HNCol3 : ~ Col A0 O A') by (intro; assert_diffs; apply HNCol; ColR).
  assert (HNCol4 : ~ Col A' O A'').
  { intro HCol; apply HNCol1.
    elim (eq_dec_points A' A''); intro; [|ColR].
    treat_equalities.
    assert (HSuma2 : SumA A0 O A' A0 O A1 A0 O A').
      apply (conga3_suma__suma P Q R A0 O A1 P' Q' R'); CongA.
    apply sams_suma__out546 in HSuma2; Col.
    apply (conga2_sams__sams P Q R A0 O A1); CongA.
  }
  assert (HNCol5 : ~ Col A0 O A'') by (intro; assert_diffs; apply HNCol4; ColR).
  assert (HBet4 : Bet A0 A' A'').
  { apply col_two_sides_bet with O.
      ColR.
    apply in_angle_two_sides; Col.
    apply lea_in_angle.
      apply (l11_30 P Q R P' Q' R'); CongA; apply sams_suma__lea123789 with A0 O A1; trivial.
    apply out_one_side; Col; apply l6_7 with B; [|apply l6_6]; assert_diffs; apply bet_out; auto.
  }
  assert (HConga4 : CongA A O A' A' O A'').
  { assert_diffs.
    assert (HNOS : ~ OS O A' A0 A'') by (apply l9_9; repeat split; auto; Col; exists A'; Col).
    apply conga_trans with A0 O A1; trivial.
    apply sams2_suma2__conga456 with P Q R P' Q' R'; trivial.
    - apply (conga2_sams__sams A0 O A' A' O A''); CongA.
      split; auto; split.
        right; intro; Col.
      exists A''; repeat (split; CongA); Cop.
      apply l9_9_bis, out_one_side; Col.
      apply bet_out; auto.
    - apply (conga3_suma__suma A0 O A' A' O A'' A0 O A''); CongA.
      exists A''; repeat (split; CongA); Cop.
  }
  assert (HLe'' : Le A0 A1 A' A'').
    apply le_transitivity with A A'; trivial; assert_diffs.
    apply lt__le, acute_archi_aux with O A0 B; eBetween.
  exists A''; repeat (split; trivial).
    apply bet2_le2__le1346 with C A'; auto.
    apply (l5_6 A0 A1 A' A''); Cong.
  exists A'; split; trivial; split; trivial.
  apply conga_trans with A O A'; CongA.
Qed.

Lemma archi_in_acute_angles :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> Acute D E F ->
    exists P Q R, GradA A B C P Q R /\ LeA D E F P Q R.
Proof.
  intros archi A B C D E F HNCol HAcute.
  assert_diffs.
  elim (col_dec D E F).
  { intro HCol; exists A; exists B; exists C; split.
      apply grada_init; CongA.
    apply l11_31_1; auto; apply not_bet_out; trivial.
    intro HBet; apply (nlta D E F), acute_obtuse__lta; trivial.
    apply bet__obtuse; auto.
  }
  intro HNCol1.
  elim (lea_total D E F A B C); auto; intro HLea.
    exists A; exists B; exists C; split; trivial; apply grada_init; CongA.
  destruct (l8_18_existence D E F) as [D0 [HD0 HD0']]; trivial.
  assert (HOut : Out E D0 D) by (apply acute_col_perp__out with F; Col; Perp; apply acute_sym; trivial).
  assert_diffs.
  assert (HConga : CongA D E F D0 E F) by (apply (out_conga D0 E F D0 E F); CongA; apply out_trivial; auto).
  apply (acute_conga__acute D E F D0 E F) in HAcute; trivial.
  apply (l11_30 A B C D E F A B C D0 E F) in HLea; CongA.
  apply (ncol_conga_ncol D E F D0 E F) in HNCol1; trivial.
  assert (HPer : Per E D0 F) by (apply perp_per_1; auto; apply perp_left_comm, perp_col with D; Perp; Col).
  clear H0 HD0 HD0' HOut H9.
  destruct (angle_construction_1 A B C D0 E F) as [D1' [HConga1 HOS]]; trivial.
  destruct (lea_in_angle D0 E F D1') as [_ [_ [_ [D1 [HBet HUn]]]]]; Side.
    apply (l11_30 A B C D0 E F); CongA.
  destruct HUn as [Heq|HOut].
    exfalso; subst D1; Col.
  apply l6_6 in HOut.
  apply (out_conga A B C D0 E D1' A C D0 D1) in HConga1; trivial; try (apply out_trivial; auto).
  apply one_side_not_col123 in HOS.
  assert_diffs.
  assert (D0 <> D1) by (intro; subst D1; assert_cols; Col).
  clear dependent D1'.
  destruct (segment_construction D0 F D0 F) as [F' [HF'1 HF'2]].
  destruct (archi D0 D1 D0 F') as [G [HG1 HG2]]; auto.
  destruct (acute_archi_aux2 E D0 D1 F G) as [P [Q [R [HGA HUn]]]]; auto.
  exists P; exists Q; exists R; split.
    assert (Hdistincts := grada_distincts D0 E D1 P Q R HGA); spliter.
    apply (conga2_grada__grada D0 E D1 P Q R); CongA.
  destruct HUn as [HLea2|Habs].
    assert_diffs; apply (l11_30 D0 E F P Q R); CongA.
  exfalso.
  destruct Habs as [A' [HBet2 [HBet3 [HConga2 [HLe HA]]]]].
  apply (le__nlt D0 F' D0 G); trivial.
  apply le1234_lt__lt with D0 F.
    apply le_transitivity with D0 A'; Le.
  split; Le.
  intro HCong.
  assert (F = F') by (apply between_cong with D0; trivial).
  treat_equalities; auto.
Qed.

Lemma angles_archi_aux :
  forall A B C D E F G H I,
    GradA A B C D E F -> GradA A B C G H I -> ~ SAMS D E F G H I ->
    exists P Q R, GradA A B C P Q R /\ ~ SAMS P Q R A B C.
Proof.
  intros A B C D E F G H I HGA1 HGA2.
  induction HGA2.
    intro HNIsi; exists D; exists E; exists F; split; trivial.
    assert (Hd := grada_distincts A B C D E F HGA1); spliter.
    intro HIsi; apply HNIsi, (conga2_sams__sams D E F A B C); CongA.
  intro HNIsi.
  elim (sams_dec D E F D0 E0 F0); [|apply IHHGA2; trivial].
  intro HIsi; clear IHHGA2.
  assert (Hd := sams_distincts D E F D0 E0 F0 HIsi); spliter.
  destruct (ex_suma D E F D0 E0 F0) as [P [Q [R HSuma]]]; auto.
  exists P; exists Q; exists R; split.
    apply grada2_sams_suma__grada with D E F D0 E0 F0; trivial.
  intro HIsi2; apply HNIsi, sams_assoc_1 with D0 E0 F0 A B C P Q R; trivial.
Qed.

Lemma angles_archi_aux1 :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> ~ Bet D E F ->
    exists P Q R, GradA A B C P Q R /\ (LeA D E F P Q R \/ ~ SAMS P Q R A B C).
Proof.
  intros archi A B C D E F HNCol HNBet.
  assert (Hdiff : D <> E /\ F <> E) by (split; intro; subst E; Between); spliter.
  assert_diffs.
  destruct (angle_bisector D E F) as [F1 [HInangle HConga]]; auto.
  assert(HNOS : ~ OS E F1 D F).
  { assert_diffs.
    elim (col_dec D E F1).
      intros HCol; apply col123__nos; Col.
    intro HNCol1.
    apply l9_9, invert_two_sides, in_angle_two_sides; Col.
    apply not_col_permutation_1, (ncol_conga_ncol D E F1); CongA.
  }
  assert (HSuma : SumA D E F1 D E F1 D E F) by (assert_diffs; exists F; repeat (split; CongA); Cop).
  destruct (archi_in_acute_angles archi A B C D E F1) as [P1 [Q1 [R1 [HGA HLea]]]]; trivial.
  { apply nbet_sams_suma__acute with D E F; trivial.
    assert_diffs; split; trivial; split.
      right; intro HBet; apply HNBet, bet_in_angle_bet with F1; trivial.
    exists F; repeat (split; CongA); Cop.
    elim (col_dec D E F1).
      intros HCol HTS; destruct HTS; Col.
    intro HNCol1.
    elim (col_dec D E F).
      intros HCol HTS; destruct HTS as [_ []]; Col.
    intro HNCol2; apply l9_9_bis, in_angle_one_side; Col.
  }
  assert_diffs.
  destruct (sams_dec P1 Q1 R1 P1 Q1 R1) as [HIsi|HNIsi].
  { destruct (ex_suma P1 Q1 R1 P1 Q1 R1) as [P [Q [R HSuma1]]]; auto.
    exists P; exists Q; exists R; split.
      apply grada2_sams_suma__grada with P1 Q1 R1 P1 Q1 R1; trivial.
    left; apply sams_lea2_suma2__lea with D E F1 D E F1 P1 Q1 R1 P1 Q1 R1; trivial.
  }
  destruct (angles_archi_aux A B C P1 Q1 R1 P1 Q1 R1) as [P [Q [R [HGA1 HNsams1]]]]; trivial.
  exists P; exists Q; exists R; split; auto.
Qed.

(** Inspired by Hartshorne's demonstration of Lemma 35.1 in Geometry Euclid and Beyond *)
Lemma archi_in_angles :
  archimedes_axiom ->
  forall A B C D E F,
    ~ Col A B C -> D <> E -> F <> E ->
    exists P Q R, GradA A B C P Q R /\ (LeA D E F P Q R \/ ~ SAMS P Q R A B C).
Proof.
  intros archi A B C D E F HNCol HDE HFE.
  elim (bet_dec D E F); [|apply angles_archi_aux1; trivial].
  intro HBet1.
  destruct (segment_construction A B A B) as [A0 [HBet HCong]].
  assert_diffs.
  assert (HNCol1 : ~ Col A0 B C) by (intro; apply HNCol; ColR).
  destruct (angles_archi_aux1 archi A B C C B A0) as [P1 [Q1 [R1 [HGA HUn]]]]; Between.
  elim (sams_dec P1 Q1 R1 A B C); [|intro; exists P1; exists Q1; exists R1; auto].
  intro HIsi.
  destruct HUn as [HLea|HNIsi]; [|exfalso; auto].
  assert_diffs.
  destruct (ex_suma P1 Q1 R1 A B C) as [P [Q [R HSuma]]]; auto.
  exists P; exists Q; exists R; split.
    apply grada_stab with P1 Q1 R1; trivial.
  suma.assert_diffs.
  left; apply l11_31_2; auto.
  apply (bet_lea__bet A B A0); trivial.
  apply sams_lea2_suma2__lea with A0 B C A B C P1 Q1 R1 A B C; Lea.
  exists A; repeat (split; CongA); Cop.
  apply l9_9; repeat split; auto.
  exists B; split; Col; Between.
Qed.

(** If Archimedes' postulate holds, every nondegenerate angle can be repeated until exceeding 180° *)
Lemma archi__grada_destruction :
  archimedes_axiom ->
  forall A B C,
    ~ Col A B C ->
    exists P Q R, GradA A B C P Q R /\ ~ SAMS P Q R A B C.
Proof.
  intros archi A B C HNCol.
  destruct (segment_construction A B A B) as [A0 [HBet HCong]].
  assert_diffs.
  destruct (archi_in_angles archi A B C A B A0) as [P [Q [R [HGA HUn]]]]; auto.
  exists P; exists Q; exists R; split; auto.
  destruct HUn as [HLea|]; trivial.
  intro HIsi.
  destruct HIsi as [_ [[HOut|HNBet] _]].
    apply HNCol; Col.
  apply HNBet, (bet_lea__bet A B A0); trivial.
Qed.


Lemma gradaexp_destruction_aux : forall A B C P Q R,
  GradA A B C P Q R ->
  exists S T U, GradAExp A B C S T U /\ (Obtuse S T U \/ LeA P Q R S T U).
Proof.
  intros A B C.
  induction 1.
    assert_diffs; exists D; exists E; exists F; split; [apply gradaexp_init|right]; Lea.
  destruct IHGradA as [P [Q [R [HGAE HUn]]]].
  assert (Hd := HGAE); apply gradaexp__grada, grada_distincts in Hd; spliter.
  destruct (sams_dec P Q R P Q R) as [HIsi|HNIsi].
  { destruct HUn as [Habs|HLea].
      absurd (SAMS P Q R P Q R); trivial; apply obtuse__nsams, Habs.
    destruct (ex_suma P Q R P Q R) as [S [T [U HSuma]]]; auto.
    exists S; exists T; exists U; split.
      apply gradaexp_stab with P Q R; trivial.
    right; apply sams_lea2_suma2__lea with D E F A B C P Q R P Q R; trivial.
    apply grada__lea, gradaexp__grada, HGAE.
  }
  apply nsams__obtuse in HNIsi; auto.
  exists P; exists Q; exists R; split; auto.
Qed.

(** If Archimedes' postulate holds, every nondegenerate angle can be doubled until exceeding 90° *)
Lemma archi__gradaexp_destruction :
  archimedes_axiom ->
  forall A B C,
    ~ Col A B C ->
    exists P Q R, GradAExp A B C P Q R /\ Obtuse P Q R.
Proof.
  intros archi A B C HNCol.
  destruct (archi__grada_destruction archi A B C HNCol) as [D [E [F [HGA HNIsi]]]].
  destruct (gradaexp_destruction_aux A B C D E F HGA) as [P [Q [R [HGAE HUn]]]].
  exists P; exists Q; exists R; split; trivial.
  destruct HUn as [HObtuse|HLea]; trivial.
  assert_diffs.
  apply nsams__obtuse; auto.
  intro HIsi; apply HNIsi.
  apply sams_lea2__sams with P Q R P Q R; trivial.
  apply grada__lea, gradaexp__grada, HGAE.
Qed.

End Archimedes_for_angles.