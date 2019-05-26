Require Export GeoCoq.Tarski_dev.Annexes.saccheri.

Section Defect.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma defect_distincts : forall A B C D E F,
  Defect A B C D E F ->
  A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  suma.assert_diffs.
  repeat split; auto.
Qed.

Lemma ex_defect : forall A B C,
  A <> B -> B <> C -> A <> C -> exists D E F, Defect A B C D E F.
Proof.
  intros A B C HAB HBC HAC.
  destruct (ex_trisuma A B C) as [G [H [I HTri]]]; auto.
  suma.assert_diffs.
  destruct (ex_suppa G H I) as [D [E [F HSuppa]]]; auto.
  exists D, E, F, G, H, I.
  split; assumption.
Qed.

Lemma conga_defect__defect : forall A B C D E F D' E' F',
  Defect A B C D E F -> CongA D E F D' E' F' ->
  Defect A B C D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HConga.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  assert_diffs.
  apply (conga2_suppa__suppa G H I D E F); CongA.
Qed.

Lemma defect2__conga : forall A B C D E F D' E' F',
  Defect A B C D E F -> Defect A B C D' E' F' ->
  CongA D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HDef'.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  destruct HDef' as [G' [H' [I' [HTri' HSuppa']]]].
  apply (suppa2__conga456 G H I); trivial.
  suma.assert_diffs.
  apply (conga2_suppa__suppa G' H' I' D' E' F'); try apply conga_refl; auto.
  apply (trisuma2__conga A B C); assumption.
Qed.

Lemma defect_perm_231 : forall A B C D E F,
  Defect A B C D E F -> Defect B C A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply trisuma_perm_231, HTri.
Qed.

Lemma defect_perm_312 : forall A B C D E F,
  Defect A B C D E F -> Defect C A B D E F.
Proof.
  intros.
  do 2 apply defect_perm_231; trivial.
Qed.

Lemma defect_perm_321 : forall A B C D E F,
  Defect A B C D E F -> Defect C B A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply trisuma_perm_321, HTri.
Qed.

Lemma defect_perm_213 : forall A B C D E F,
  Defect A B C D E F -> Defect B A C D E F.
Proof.
  intros.
  apply defect_perm_321, defect_perm_312; trivial.
Qed.

Lemma defect_perm_132 : forall A B C D E F,
  Defect A B C D E F -> Defect A C B D E F.
Proof.
  intros.
  apply defect_perm_321, defect_perm_231; trivial.
Qed.

Lemma conga3_defect__defect : forall A B C D E F A' B' C',
  Defect A B C D E F ->
  CongA A B C A' B' C' -> CongA B C A B' C' A' -> CongA C A B C' A' B' ->
  Defect A' B' C' D E F.
Proof.
  intros A B C D E F A' B' C' HDef HCongaB HCongaC HCongaA.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  exists G, H, I.
  split; trivial.
  apply (conga3_trisuma__trisuma A B C); trivial.
Qed.

Lemma col_defect__out : forall A B C D E F,
  Col A B C -> Defect A B C D E F -> Out E D F.
Proof.
  intros A B C D E F HCol HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (bet_suppa__out G H I); trivial.
  apply (col_trisuma__bet A B C); Col.
Qed.

Lemma rah_defect__out :
  hypothesis_of_right_saccheri_quadrilaterals ->
  forall A B C D E F, Defect A B C D E F -> Out E D F.
Proof.
  intros rah A B C D E F HDef.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (bet_suppa__out G H I); trivial.
  apply (t22_14__bet rah A B C), HTri.
Qed.

Lemma defect_ncol_out__rah : forall A B C D E F,
  ~ Col A B C -> Defect A B C D E F -> Out E D F ->
  hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HNCol HDef HOut.
  destruct HDef as [G [H [I [HTri HSuppa]]]].
  apply (t22_14__rah A B C G H I); trivial.
  apply (out_suppa__bet D E F); [|apply suppa_sym]; assumption.
Qed.

(** The following development is inspired by The Foundations of Geometry and the Non-Euclidean Plane, by George E Martin, chapter 22 *)

(** Additivity of the defect : if C1 is between A and C, the defect of ABC is
    the sum of the defects of ABC1 and BC1C.
    In this proof, we have to exclude the semi-elliptical case so that the sums of angles behave. *)
Lemma t22_16_1 :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C C1 D E F G H I K L M,
    Bet A C1 C -> Defect A B C1 D E F -> Defect B C1 C G H I ->
    SumA D E F G H I K L M ->
    SAMS D E F G H I /\ Defect A B C K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefC HSuma.
  assert (HDA := defect_distincts A B C1 D E F HDefA).
  assert (HDC := defect_distincts B C1 C G H I HDefC).
  spliter; clean.
  apply defect_perm_321 in HDefA.
  destruct HDefA as [P [Q [R [HTri HSuppa]]]].
  assert (HSuma1 : SumA P Q R D E F A C1 C) by SumA.
  destruct HTri as [S [T [U [HSuma2 HSuma3]]]].
  assert (HInter : SumA S T U D E F B C1 C /\ SAMS S T U D E F).
  { suma.assert_diffs.
    destruct (ex_suma S T U D E F) as [B' [C1' [C' HSuma']]]; auto.
    assert (HSuma4 : SumA B C1 C A C1 B A C1 C) by (apply suma_sym, inangle__suma, in_angle_line; auto).
    destruct (ex_suma A C1 B D E F) as [V [W [X HSuma5]]]; auto.
    assert (HIsi : SAMS P Q R D E F) by (apply bet_suma__sams with A C1 C; trivial).
    assert (HIsi1 : SAMS S T U A C1 B) by (apply (t22_20 noah), HSuma2).
    assert (HIsi2 : SAMS A C1 B D E F).
    { apply sams_lea2__sams with P Q R D E F; Lea.
      apply (sams_suma__lea456789 S T U); trivial.
    }
    assert (HSuma6 : SumA S T U V W X A C1 C) by (apply suma_assoc_1 with A C1 B D E F P Q R; trivial).
    assert (HIsi3 : SAMS S T U D E F).
      apply sams_lea2__sams with P Q R D E F; Lea; apply sams_suma__lea123789 with A C1 B; SumA.
    assert (HSuma7 : SumA B' C1' C' A C1 B A C1 C) by (apply suma_assoc_2 with S T U D E F V W X; SumA).
    split; trivial.
    apply (conga3_suma__suma S T U D E F B' C1' C'); try (apply conga_refl); auto.
    apply sams2_suma2__conga123 with A C1 B A C1 C; trivial; apply bet_suma__sams with A C1 C; trivial.
  }
  clear dependent P; clear Q R.

  destruct HInter as [HSuma3 HIsi3].
  apply defect_perm_231 in HDefC.
  destruct HDefC as [P [Q [R [HTri HSuppa]]]].
  assert (HSuma1 : SumA P Q R G H I A C1 C) by SumA.
  destruct HTri as [V [W [X [HSuma4 HSuma5]]]].
  assert (HIsi1 : SAMS P Q R G H I) by (apply bet_suma__sams with A C1 C; trivial).
  assert (HIsi5 : SAMS V W X B C1 C) by (apply (t22_20 noah), HSuma4).
  assert (HIsi : SAMS D E F G H I).
  { apply sams_lea2__sams with P Q R G H I; Lea.
    apply lea_trans with B C1 C.
      apply (sams_suma__lea456789 S T U); trivial.
    apply (sams_suma__lea456789 V W X); trivial.
  }
  split; trivial.

  suma.assert_diffs.
  destruct (ex_suma V W X S T U) as [A' [B' [C' HSuma6]]]; auto.
  assert (HIsi6 : SAMS V W X S T U).
  { apply sams_lea2__sams with V W X B C1 C; Lea.
    apply sams_suma__lea123789 with D E F; trivial.
  }
  assert (HSuma7 : SumA A' B' C' D E F P Q R) by (apply suma_assoc_2 with V W X S T U B C1 C; trivial).
  assert (HSuma8 : SumA A' B' C' K L M A C1 C).
  { apply suma_assoc_1 with D E F G H I P Q R; trivial.
    apply sams_assoc_2 with V W X S T U B C1 C; trivial.
  }
  exists A', B', C'.
  split; [|apply bet_suma__suppa with A C1 C; assumption].
  clear dependent D; clear dependent E; clear dependent G; clear dependent H;
  clear dependent K; clear dependent L; clear dependent P; clear dependent Q; clear F I M R.

  destruct (ex_suma V W X C1 B A) as [D [E [F HSuma]]]; auto.
  assert (HIsi : SAMS V W X C1 B A).
  { apply sams_lea2__sams with V W X S T U; Lea.
    apply sams_suma__lea123789 with B A C1; SumA.
  }
  suma.assert_diffs.
  apply trisuma_perm_132.
  exists D; exists E; exists F.
  split.
  - assert (HConga : CongA C1 C B A C B).
    { apply (out_conga C1 C B C1 C B); try (apply out_trivial); CongA.
      apply bet_out; Between.
    }
    apply (conga3_suma__suma C1 C B C B A D E F); CongA.
    assert (HInAngle : InAngle C1 C B A).
      repeat split; auto; exists C1; split; Between; right; apply out_trivial; auto.
    apply suma_assoc_1 with C B C1 C1 B A V W X; SumA.
  - assert (HConga : CongA B A C B A C1).
      apply (out_conga B A C1 B A C1); try (apply out_trivial); CongA; apply bet_out; auto.
    apply (conga3_suma__suma D E F B A C1 A' B' C'); CongA.
    apply suma_assoc_2 with V W X C1 B A S T U; SumA.
Qed.

Lemma t22_16_1bis :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C C1 D E F G H I K L M,
    Bet A C1 C ->
    Defect A B C1 D E F -> Defect B C1 C G H I -> Defect A B C K L M ->
    SAMS D E F G H I /\ SumA D E F G H I K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefB HDef.
  assert (Hd := defect_distincts A B C1 D E F HDefA).
  assert (Hd' := defect_distincts B C1 C G H I HDefB).
  spliter.
  destruct (ex_suma D E F G H I) as [K' [L' [M' HSuma]]]; auto.
  destruct (t22_16_1 noah A B C C1 D E F G H I K' L' M') as [HIsi HDef']; trivial.
  split; trivial.
  apply (conga3_suma__suma D E F G H I K' L' M'); try (apply conga_refl); auto.
  apply (defect2__conga A B C); trivial.
Qed.


Lemma t22_16_2aux :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 ->
    Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D -> Col A B C -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
    SAMS C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  assert (Hd'' := defect_distincts A B C D1 D2 D3 HDefD).
  spliter; suma.assert_diffs.
  apply col_defect__out in HDefD; trivial.
  destruct (col_dec A D C) as [HCol1|HNCol].
  { assert (Col C B D) by ColR.
    assert (Col A B D) by ColR.
    apply col_defect__out in HDefA; trivial.
    apply col_defect__out in HDefB; trivial.
    apply col_defect__out in HDefC; trivial.
    split; [SumA|].
    apply (conga3_suma__suma D1 D2 D3 B1 B2 B3 P Q R); try (apply conga_refl); auto;
    apply l11_21_b; trivial.
  }
  assert (B = O) by (apply (l6_21 A C D B); Col).
  subst O.
  apply out213_suma__conga in HSuma; trivial.
  destruct (t22_16_1bis noah A D C B C1 C2 C3 A1 A2 A3 B1 B2 B3) as [HIsi HSuma1]; trivial.
    apply defect_perm_132, HDefC.
    apply defect_perm_321, HDefA.
  split; trivial.
  apply (conga3_suma__suma C1 C2 C3 A1 A2 A3 B1 B2 B3); CongA.
Qed.

Lemma t22_16_2aux1 :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 ->
    Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D -> Col A B D -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
    SAMS C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  spliter; suma.assert_diffs.
  assert (HOut : Out C2 C1 C3) by (apply (col_defect__out A B D); trivial).
  split; [SumA|].
  assert (HSuma1 : SumA C1 C2 C3 A1 A2 A3 A1 A2 A3) by (apply out213__suma; auto).
  apply (conga3_suma__suma C1 C2 C3 A1 A2 A3 A1 A2 A3); try (apply conga_refl); auto.
  apply (suma2__conga D1 D2 D3 B1 B2 B3); trivial.
  destruct (t22_16_2aux noah B A D C B1 B2 B3 A1 A2 A3 D1 D2 D3 C1 C2 C3 O A1 A2 A3); Col;
  apply defect_perm_213; trivial.
Qed.

(** In a convex quadrilateral ABCD, the sum of the defects of ABC and ADC is equal to
    the sum of the defects of ABD and CBD. We add some hypotheses to make the proof easier *)
Lemma t22_16_2 :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
    Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 ->
    Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
    Bet A O C -> Bet B O D ->
    SAMS D1 D2 D3 B1 B2 B3 -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
    SAMS C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HIsi HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  spliter; suma.assert_diffs.

  destruct (col_dec A B C) as [HCol|HNCol].
    apply (t22_16_2aux noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (col_dec A D C) as [HCol1|HNCol1].
    apply (t22_16_2aux noah A D C B A1 A2 A3 D1 D2 D3 C1 C2 C3 B1 B2 B3 O); Between; SumA;
    apply defect_perm_132; trivial.
  destruct (col_dec A B D) as [HCol2|HNCol2].
    apply (t22_16_2aux1 noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (col_dec C B D) as [HCol3|HNCol3].
    destruct (t22_16_2aux1 noah C B A D C1 C2 C3 B1 B2 B3 A1 A2 A3 D1 D2 D3 O P Q R); Between; SumA;
    apply defect_perm_321; trivial.
  assert (Hdiff : O <> A /\ O <> B /\ O <> C /\ O <> D).
    assert_cols; repeat split; intro; subst O; Col.
  spliter.

  destruct (ex_defect A B O) as [S1 [T1 [U1 HDef1]]]; auto.
  destruct (ex_defect B C O) as [S2 [T2 [U2 HDef2]]]; auto.
  destruct (ex_defect C D O) as [S3 [T3 [U3 HDef3]]]; auto.
  destruct (ex_defect A D O) as [S4 [T4 [U4 HDef4]]]; auto.
  destruct (t22_16_1bis noah A B C O S1 T1 U1 S2 T2 U2 D1 D2 D3) as [HIsi12 HSuma12]; trivial.
    apply defect_perm_132, HDef2.
  destruct (t22_16_1bis noah A D C O S4 T4 U4 S3 T3 U3 B1 B2 B3) as [HIsi34 HSuma34]; trivial.
    apply defect_perm_231, HDef3.
  destruct (t22_16_1bis noah B A D O S1 T1 U1 S4 T4 U4 C1 C2 C3) as [HIsi14 HSuma14]; trivial.
    apply defect_perm_213, HDef1.
    apply defect_perm_132, HDef4.
    apply defect_perm_213, HDefC.
  destruct (t22_16_1bis noah B C D O S2 T2 U2 S3 T3 U3 A1 A2 A3) as [HIsi23 HSuma23]; trivial.
    apply defect_perm_132, HDef3.
    apply defect_perm_213, HDefA.
  suma.assert_diffs.

  destruct (ex_suma D1 D2 D3 S3 T3 U3) as [V [W [X HSuma1]]]; auto.
  assert (HIsi1 : SAMS D1 D2 D3 S3 T3 U3).
    apply sams_lea2__sams with D1 D2 D3 B1 B2 B3; Lea; apply (sams_suma__lea456789 S4 T4 U4); trivial.
  assert (HSuma2 : SumA V W X S4 T4 U4 P Q R).
    apply suma_assoc_2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; SumA.
  assert (HIsi2 : SAMS V W X S4 T4 U4).
    apply sams_assoc_2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; SumA.
  assert (HSuma3 : SumA A1 A2 A3 S1 T1 U1 V W X).
    apply suma_assoc_2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; SumA.
  assert (HIsi3 : SAMS A1 A2 A3 S1 T1 U1).
    apply sams_assoc_2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; SumA.
  split.
    apply sams_assoc_2 with S4 T4 U4 S1 T1 U1 V W X; SumA.
  apply suma_assoc_2 with S4 T4 U4 S1 T1 U1 V W X; SumA.
Qed.

End Defect.