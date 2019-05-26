Require Export GeoCoq.Tarski_dev.Annexes.suma.

Section HalfAngle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Definition HalfA P A O B := ~ Bet A O B /\ InAngle P A O B /\ CongA A O P B O P.

Lemma halfa_distincts : forall P A O B, HalfA P A O B -> O <> A /\ O <> B /\ O <> P.
Proof.
  unfold HalfA.
  intros.
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma halfa__suma : forall P A O B, HalfA P A O B -> SumA A O P A O P A O B.
Proof.
  unfold HalfA.
  intros P A O B H.
  spliter.
  assert_diffs.
  apply (conga3_suma__suma A O P B O P A O B); [SumA|CongA..].
Qed.

Lemma halfa_exists : forall A O B, ~ Bet A O B -> exists P, HalfA P A O B.
Proof.
  intros A O B HNBet.
  assert_diffs.
  destruct (angle_bisector A O B) as [P [HIn HConga]]; auto.
  apply conga_comm in HConga.
  exists P; repeat (split; trivial).
Qed.

Lemma halfa_sym : forall A O B P, HalfA P A O B -> HalfA P B O A.
Proof.
  unfold HalfA.
  intros.
  spliter.
  split; [|split].
    intro; Between.
    apply l11_24; assumption.
    apply conga_sym; assumption.
Qed.

Lemma halfa__nbet : forall A O B P, HalfA P A O B -> ~ Bet A O P.
Proof.
  unfold HalfA.
  intros A O B P H.
  spliter.
  intro HBet.
  apply (not_bet_and_out A O P).
  split.
    assumption.
  apply in_angle_out with B; trivial.
  assert_diffs.
  apply l6_2 with P; auto.
  apply (bet_conga__bet A O P); assumption.
Qed.

Lemma out_preserves_halfa : forall P A O B P' A' B', 
 Out O A A' -> Out O B B' -> Out O P P' ->
 HalfA P A O B -> HalfA P' A' O B'.
Proof.
  intros P A O B P' A' B' HA HB HP [HNBet []].
  apply l6_6 in HA.
  apply l6_6 in HB.
  apply l6_6 in HP.
  split; [|split].
    intro; apply HNBet, bet_out_out_bet with A' B'; assumption.
    apply l11_25 with P A B; assumption.
    apply l11_10 with A P B P; assumption.
Qed.

Lemma halfa__nbet2 : forall A O B P, HalfA P A O B -> ~ Bet A O P /\ ~ Bet B O P.
Proof.
  intros A O B P.
  split.
  apply (halfa__nbet A O B P); auto.
  apply halfa_sym in H.
  apply (halfa__nbet B O A P); auto.
Qed.


Lemma halfa_chara1 : forall P A O B, HalfA P A O B -> 
  exists A', exists M, Cong O A' O A /\ Out O A' B /\ Midpoint M A A' /\ Out O M P.
Proof.
  unfold HalfA.
  intros P A O B H.
  spliter.
  assert_diffs.
  destruct (l6_11_existence O O A B) as [A' []]; auto.
  destruct (midpoint_existence A A') as [M].
  exists A', M.
  split.
    assumption.
  split.
    assumption.
  split.
    assumption.
  destruct (col_dec A O B) as [|HNCol].
  { assert (Out O A B). apply not_bet_out; assumption.
    assert (A = A') by (apply (l6_11_uniqueness O O A B); Cong).
    treat_equalities.
    apply in_angle_out with B; trivial.
  }
  assert (InAngle M A O B).
  { assert_diffs.
    assert (O <> M).
    { intro.
      subst M.
      absurd (Bet A O B); trivial.
      apply between_symmetry, l6_2 with A'; Between.
    }
    apply l11_25 with M A A'; [|apply out_trivial|apply l6_6|apply out_trivial]; auto.
    repeat split; auto.
    exists M.
    split; Between.
    right.
    apply out_trivial; auto.
  }
  apply col_inangle2__out with A B; trivial.
  apply conga2_cop2__col_1 with A B; [| |apply conga_comm; assumption|Cop..].
    intro; destruct (or_bet_out A O B) as [|[|]]; auto.
  assert_diffs.
  destruct (l11_51 O M A O M A'); Cong.
    intro; treat_equalities; apply HNCol; Col.
  apply l11_10 with M A M A'; [|apply out_trivial..|apply l6_6]; auto.
Qed.

Lemma halfa_chara2 : forall P A O B,
  (exists A', exists M, Cong O A' O A /\ Out O A' B /\ Midpoint M A A' /\ Out O M P) -> HalfA P A O B.
Proof.
  intros P A O B H.
  destruct H as [A' [M [HCong [HOut [HM1 HM2]]]]].
  assert_diffs.
  apply out_preserves_halfa with M A A'; trivial.
    apply out_trivial; auto.
  split; [|split].
  - intro.
    absurd (O = M); auto.
    apply l7_17 with A A'; trivial.
    split; Cong.
  - repeat split; auto.
    exists M.
    split.
      Between.
      right; apply out_trivial; auto.
  - destruct (eq_dec_points A A').
      subst; apply conga_refl; auto.
    assert_diffs.
    destruct (l11_51 O A M O A' M); Cong.
Qed.

Lemma halfa_uniqueness : forall O A B P P', HalfA P A O B -> HalfA P' A O B -> Out O P P'.
Proof.
  intros O A B P P' HP HP'.
  apply halfa_chara1 in HP.
  apply halfa_chara1 in HP'.
  destruct HP as [A1 [M1]].
  destruct HP' as [A2 [M2]].
  spliter.
  assert (A1 = A2).
  { assert_diffs.
    apply (l6_11_uniqueness O O A B); auto.
  }
  subst A2.
  assert(M1 = M2) by (apply (l7_17 A A1); assumption).
  subst M2.
  apply l6_7 with M1; [apply l6_6|]; assumption.
Qed.

Lemma halfa_not_null : forall P A O B, ~ Col A O B -> HalfA P A O B -> ~ Col A O P.
Proof.
  intros P A O B HNCol [_ [HIn HConga]] HCol.
  assert (Col B O P).
    apply (col_conga_col A O P); assumption.
  apply HNCol.
  assert_diffs.
  ColR.
Qed.

Lemma null_halfa__null : forall P A O B, Col A O B -> HalfA P A O B -> Out O A P.
Proof.
  unfold HalfA.
  intros P A O B HCol H.
  spliter.
  assert (Out O A B) by (apply not_bet_out; assumption).
  apply(in_angle_out A O B P); assumption.
Qed.

Lemma halfa1123__out : forall A O B, HalfA A A O B -> Out O A B.
Proof.
  intros A O B [_ [_ HCongA]].
  apply eq_conga_out with A O; CongA.
Qed.

Lemma halfa3123__out : forall A O B, HalfA B A O B -> Out O A B.
Proof.
  intros A O B HHalf.
  apply l6_6, halfa1123__out, halfa_sym, HHalf.
Qed.

Lemma halfa__sams : forall P A O B, HalfA P A O B -> SAMS A O P A O P.
Proof.
  unfold HalfA.
  intros P A O B H.
  spliter.
  assert_diffs.
  apply (conga2_sams__sams A O P P O B); [CongA..|SumA].
Qed.

Lemma halfa__acute : forall P A O B, HalfA P A O B -> Acute A O P.
Proof.
  intros P A O B HHalfa.
  apply nbet_sams_suma__acute with A O B.
    destruct HHalfa; assumption.
    apply halfa__sams with B; assumption.
    apply halfa__suma; assumption.
Qed.

Lemma halfa__lea : forall P A O B, HalfA P A O B -> LeA A O P A O B.
Proof.
  unfold HalfA.
  intros.
  spliter.
  apply (inangle__lea); assumption.
Qed.

Lemma halfa2_lea__lea1 : forall P A O B P' A' O' B',
  HalfA P A O B -> HalfA P' A' O' B' -> LeA A' O' P' A O P -> LeA A' O' B' A O B.
Proof.
  intros P A O B P' A' O' B' HP HP' HLea.
  apply sams_lea2_suma2__lea with A' O' P' A' O' P' A O P A O P; trivial.
    apply halfa__sams with B; assumption.
    apply halfa__suma; assumption.
    apply halfa__suma; assumption.
Qed.

Lemma halfa__ts : forall P A O B, ~ Col A O B -> HalfA P A O B -> TS O P A B.
Proof.
  intros P A O B HNCol HHalfa.
  assert(~ Col A O P) by (apply halfa_not_null with B; assumption).
  assert(~ Col B O P).
    apply halfa_not_null with A; Col.
    apply halfa_sym; assumption.
  destruct HHalfa as [_ []].
  apply invert_two_sides, in_angle_two_sides; Col.
Qed.

Lemma conga_halfa__conga1 : forall P A O B P' A' O' B', 
 HalfA P A O B -> HalfA P' A' O' B' ->
 CongA A O P A' O' P' -> 
 CongA A O B A' O' B'.
Proof.
  intros P A O B P' A' O' B' HP HP' HConga.
  apply (suma2__conga A O P A O P).
    apply halfa__suma; assumption.
  assert (Hd := HP').
  apply halfa_distincts in Hd.
  spliter.
  apply (conga3_suma__suma A' O' P' A' O' P' A' O' B'); [|CongA..].
  apply halfa__suma; assumption.
Qed.

Lemma conga_halfa__conga2 : forall P A O B P' A' O' B', 
 HalfA P A O B -> HalfA P' A' O' B' -> CongA A O B A' O' B' -> CongA A O P A' O' P'.
Proof.
  intros P A O B P' A' O' B' HP HP' HConga.
  apply sams2_suma2__conga with A O B.
    apply halfa__sams with B; assumption.
    apply halfa__suma; assumption.
    apply halfa__sams with B'; assumption.
  apply halfa__suma in HP'.
  assert_diffs.
  apply (conga3_suma__suma A' O' P' A' O' P' A' O' B'); CongA.
Qed.

Lemma halfa2_lta__lta1 : forall P A O B P' A' O' B',
  HalfA P A O B -> HalfA P' A' O' B' -> LtA A' O' P' A O P -> LtA A' O' B' A O B.
Proof.
  intros P A O B P' A' O' B' HP HP' [HLea HNCong].
  split.
    apply halfa2_lea__lea1 with P P'; assumption.
  intro.
  apply HNCong.
  apply conga_halfa__conga2 with B' B; assumption.
Qed.

Lemma halfa2_lea__lea2 : forall P A O B P' A' O' B',
  HalfA P A O B -> HalfA P' A' O' B' -> LeA A' O' B' A O B -> LeA A' O' P' A O P.
Proof.
  intros P A O B P' A' O' B' HP HP' HLeA.
  assert (Hd := HP).
  apply halfa_distincts in Hd.
  assert (Hd' := HP').
  apply halfa_distincts in Hd'.
  spliter.
  destruct (lea_total A O P A' O' P'); auto.
  apply conga__lea.
  apply conga_halfa__conga2 with B' B; [assumption..|].
  apply lea_asym; [assumption|].
  apply halfa2_lea__lea1 with P' P; assumption.
Qed.

Lemma halfa2_lta__lta2 : forall P A O B P' A' O' B',
  HalfA P A O B -> HalfA P' A' O' B' -> LtA A' O' B' A O B -> LtA A' O' P' A O P.
Proof.
  intros P A O B P' A' O' B' HP HP' [HLea HNCong].
  split.
    apply halfa2_lea__lea2 with B B'; assumption.
  intro.
  apply HNCong.
  apply conga_halfa__conga1 with P' P; assumption.
Qed.

Lemma col_halfa__out : forall P A O B, Col A O B -> HalfA P A O B -> Out O A B.
Proof.
  unfold HalfA.
  intros.
  spliter.
  apply not_bet_out; assumption.
Qed.

(*
Lemma lta_nbet__ncol : forall A B C X Y Z, ~ Bet X Y Z -> LtA A B C X Y Z -> ~ Col X Y Z.
Proof.
  intros A B C X Y Z HNBet HLta HCol.
  apply HNBet.
  apply (col_lta__bet A B C); assumption.
Qed.
*)

Lemma halfa__coplanar : forall A B C D, 
  HalfA A B C D -> Coplanar A B C D.
Proof.
  unfold HalfA.
  intros.
  spliter.
  apply inangle__coplanar; assumption.
Qed.

Lemma cop_halfa_perp__os : forall P A O B T, HalfA P A O B -> Perp O P T O -> Coplanar A O P T ->
  OS O T P A.
Proof.
  intros P A O B T HP HPerp HCop.
  apply acute_cop_perp__one_side.
    apply acute_sym, halfa__acute with B; assumption.
    assumption.
    Cop.
Qed.

Lemma cop_halfa_perp__os2 : forall P A O B T, HalfA P A O B -> Perp O P T O -> Coplanar A O P T ->
  OS O T P A /\ OS O T P B.
Proof.
  intros P A O B T HP HPerp HCop.
  split.
    apply cop_halfa_perp__os with B; assumption.
  apply cop_halfa_perp__os with A.
    apply halfa_sym; assumption.
    assumption.
  destruct (col_dec A O P).
  { assert (Col B O P); [|Cop].
    destruct HP as [_ []].
    apply (col_conga_col A O P); assumption.
  }
  apply halfa__coplanar in HP.
  apply coplanar_perm_12, coplanar_trans_1 with A; Cop.
Qed.

Lemma inangle_halfa2__inangle : forall O A B C A' C',
  ~ Col A O B -> InAngle C A O B ->
  HalfA A' A O B -> HalfA C' C O B ->
  InAngle C' A' O B.
Proof.
  intros O A B C A' C' HNCol HC HA' HC'.
  apply halfa_sym in HA'.
  apply halfa_sym in HC'.
  destruct (col_dec B O C).
  { apply out341__inangle.
      apply halfa_distincts in HA'; spliter; auto.
    apply null_halfa__null with C; assumption.
  }
  apply l11_24, lea_in_angle.
    apply halfa2_lea__lea2 with A C; [assumption..|].
    apply inangle__lea, l11_24, HC.
  apply one_side_transitivity with A; [|apply one_side_transitivity with C; apply one_side_symmetry];
    apply in_angle_one_side; Col.
    apply halfa_not_null in HA'; Col.
    destruct HA' as [_ []]; assumption.
    apply l11_24, HC.
    apply halfa_not_null in HC'; Col.
    destruct HC' as [_ []]; Col.
Qed.

Definition gHalfA A' O' B' A O B := exists P, HalfA P A O B /\ CongA A' O' B' A O P.

Lemma ghalfa_distincts : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  O' <> A' /\ O' <> B' /\ O <> A /\ O <> B.
Proof.
  intros A' O' B' A O B [P [HP]].
  apply halfa_distincts in HP.
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma halfa__ghalfa : forall P A O B, HalfA P A O B -> gHalfA A O P A O B.
Proof.
  intros P A O B HP.
  exists P.
  split; [assumption|].
  apply halfa_distincts in HP.
  spliter.
  apply conga_refl; auto.
Qed.

Lemma ghalfa_left_comm : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  gHalfA B' O' A' A O B.
Proof.
  intros A' O' B' A O B [P [HP]].
  exists P.
  split; CongA.
Qed.

Lemma ghalfa_right_comm : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  gHalfA A' O' B' B O A.
Proof.
  intros A' O' B' A O B [P [[HNBet [HP1 HP2]] HP3]].
  exists P.
  split; [split; [|split]|].
    Between.
    apply l11_24, HP1.
    CongA.
    apply conga_trans with A O P; assumption.
Qed.

Lemma ghalfa_comm : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  gHalfA B' O' A' B O A.
Proof.
  intros A' O' B' A O B H.
  apply ghalfa_left_comm, ghalfa_right_comm, H.
Qed.

Lemma ghalfa_exists : forall A O B, ~ Bet A O B -> exists A' O' B', gHalfA A' O' B' A O B.
Proof.
  intros A O B H.
  destruct (halfa_exists A O B H) as [P HP].
  exists A, O, P.
  apply halfa__ghalfa, HP.
Qed.


Lemma ghalfa__suma : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  SumA A' O' B' A' O' B' A O B.
Proof.
  intros A' O' B' A O B [P [HHalf HConga]].
  assert (Hd := HHalf).
  apply halfa_distincts in HHalf.
  spliter.
  apply (conga3_suma__suma A O P A O P A O B); [|CongA..].
  apply halfa__suma; assumption.
Qed.

Lemma ghalfa__acute : forall A' O' B' A O B, gHalfA A' O' B' A O B ->
  Acute A' O' B'.
Proof.
  intros A' O' B' A O B [P [HHalf HConga]].
  apply (acute_conga__acute A O P); CongA.
  apply halfa__acute with B, HHalf.
Qed.

Lemma ghalfa_chara : forall A' O' B' A O B,
  gHalfA A' O' B' A O B <-> (Acute A' O' B' /\ SumA A' O' B' A' O' B' A O B).
Proof.
  intros A' O' B' A O B.
  split.
    intro HHalf; split; [eapply ghalfa__acute, HHalf|apply ghalfa__suma, HHalf].
  intros [HAcute HSuma].
  destruct (halfa_exists A O B) as [P HP].
    apply (acute_suma__nbet A' O' B'); assumption.
  exists P; split; [assumption|].
  apply sams2_suma2__conga with A O B; [SumA..| |].
    eapply halfa__sams, HP.
    apply halfa__suma, HP.
Qed.

Lemma ghalfa__out : forall A O B, gHalfA A O B A O B -> Out O A B.
Proof.
  intros A O B HHalf.
  rewrite ghalfa_chara in HHalf; spliter.
  apply (sams_suma__out546 A O B); SumA.
Qed.

Lemma ghalfa_preserves_lta : forall A B C X Y Z A' B' C' X' Y' Z',
  gHalfA A' B' C' A B C -> gHalfA X' Y' Z' X Y Z -> LtA A B C X Y Z -> LtA A' B' C' X' Y' Z'.
Proof.
  intros A B C X Y Z A' B' C' X' Y' Z' [P1 []] [P2 []] HLta.
  apply (conga_preserves_lta A B P1 X Y P2); [CongA..|].
  apply halfa2_lta__lta2 with Z C; assumption.
Qed.

(** Given two angles a and b, a/2 = b/2 -> a = b *)

Lemma ghalfa_preserves_conga_1 : forall A B C A' B' C' X Y Z X' Y' Z', 
  gHalfA X Y Z A B C -> gHalfA X' Y' Z' A' B' C' -> CongA X Y Z X' Y' Z' ->
  CongA A B C A' B' C'.
Proof.
  intros A B C A' B' C' X Y Z X' Y' Z' [P []] [P' []] HConga.
  apply conga_halfa__conga1 with P P'; [assumption..|].
  apply conga_trans with X Y Z.
    apply conga_sym; assumption.
  apply conga_trans with X' Y' Z'; assumption.
Qed.

(** Given two angles a and b, a = b -> a/2 = b/2 *)

Lemma ghalfa_preserves_conga_2 : forall A B C A' B' C' X Y Z X' Y' Z',
  gHalfA X Y Z A B C -> gHalfA X' Y' Z' A' B' C' -> CongA A B C A' B' C' ->
  CongA X Y Z X' Y' Z'.
Proof.
  intros A B C A' B' C' X Y Z X' Y' Z' [P []] [P' []] HConga.
  apply conga_trans with A B P.
    assumption.
  apply conga_trans with A' B' P'; [|apply conga_sym; assumption].
  apply conga_halfa__conga2 with C C'; assumption.
Qed.

(** Unicity of the double angle *)

Lemma ghalfa2__conga_1 : forall A B C A' B' C' A'' B'' C'',
  gHalfA A B C A' B' C' -> gHalfA A B C A'' B'' C'' -> CongA A' B' C' A'' B'' C''.
Proof.
  intros A B C A' B' C' A'' B'' C''.
  rewrite 2 ghalfa_chara.
  intros [HAcute' HSuma'] [HAcute'' HSuma''].
  apply (suma2__conga A B C A B C); assumption.
Qed.

(** Unicity of the half angle *)

Lemma ghalfa2__conga_2 : forall A B C A' B' C' A'' B'' C'',
  gHalfA A' B' C' A B C -> gHalfA A'' B'' C'' A B C -> CongA A' B' C' A'' B'' C''.
Proof.
  intros A B C A' B' C' A'' B'' C'' [P' []] [P'' []].
  apply conga_trans with A B P'; [assumption|].
  apply conga_trans with A B P''; [|CongA].
  apply out2__conga.
    apply out_trivial; assert_diffs; auto.
  apply halfa_uniqueness with A C; assumption.
Qed.

(** CongA preserves gHalfA *)

Lemma conga2_ghalfa__ghalfa : forall A B C A' B' C' D E F D' E' F',
  CongA A B C D E F -> CongA A' B' C' D' E' F' -> gHalfA A B C A' B' C' ->
  gHalfA D E F D' E' F'.
Proof.
  intros A B C A' B' C' D E F D' E' F' HConga HConga1.
  rewrite 2 ghalfa_chara.
  intros [HAcute HSuma].
  split.
    apply (acute_conga__acute A B C); assumption.
    apply (conga3_suma__suma A B C A B C A' B' C'); assumption.
Qed.

(** Out preserves gHalfA *)

Lemma ghalfa_out4__ghalfa : forall A B C D E F A' C' D' F',
  Out B A' A -> Out B C' C -> Out E D' D -> Out E F' F -> gHalfA A B C D E F ->
  gHalfA A' B C' D' E F'.
Proof.
  intros A B C D E F A' C' D' F' HA HC HE HF HHalf.
  apply conga2_ghalfa__ghalfa with A B C D E F; [apply out2__conga..|]; assumption.
Qed.

(** Given two angles a and b such that a/2 + b/2 is acute, a/2 + b/2 = (a+b)/2 *)

Lemma suma_preserves_ghalfa : forall A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z',
  Acute X Y Z ->
  SumA A B C D E F X Y Z -> SumA A' B' C' D' E' F' X' Y' Z' ->
  gHalfA A B C A' B' C' -> gHalfA D E F D' E' F' ->
  gHalfA X Y Z X' Y' Z'.
Proof.
  intros A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z' HAcute HSuma HSuma'.
  rewrite 3 ghalfa_chara.
  intros [HAcute1 HSuma1] [HAcute2 HSuma2].
  split; [apply HAcute|].
  assert_diffs.
  destruct (ex_suma A' B' C' D E F) as [G [H [I]]]; auto.
  assert (SumA A B C X Y Z G H I) by (apply suma_assoc_1 with A B C D E F A' B' C'; SumA).
  apply suma_assoc_1 with A B C D E F G H I; [SumA..|].
  apply suma_assoc_2 with A' B' C' D E F D' E' F'; [|SumA..].
  apply sams_assoc_2 with A B C A B C X Y Z; SumA.
Qed.

(** Given two angles a and b, a/2 - b/2 = (a-b)/2 *)

Lemma acute_ghalfa2_sams_suma2__ghalfa456 : forall A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z',
  SAMS A' B' C' D' E' F' -> Acute D E F ->
  SumA A B C D E F X Y Z -> SumA A' B' C' D' E' F' X' Y' Z' ->
  gHalfA A B C A' B' C' -> gHalfA X Y Z X' Y' Z' ->
  gHalfA D E F D' E' F'.
Proof.
  intros A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z' HSams HAcute HSuma HSuma'.
  rewrite 3 ghalfa_chara.
  intros [HAcute1 HSuma1] [HAcute2 HSuma2].
  split; [apply HAcute|].
  assert_diffs.
  destruct (ex_suma D E F D E F) as [D'' [E'' [F'' HSuma3]]]; auto.
  apply (conga3_suma__suma D E F D E F D'' E'' F''); try apply conga_refl; auto.
  destruct (ex_suma A' B' C' D E F) as [G [H [I]]]; auto.
  assert (SumA A B C X Y Z G H I) by (apply suma_assoc_1 with A B C D E F A' B' C'; SumA).
  assert (SAMS A' B' C' D E F) by (apply sams_assoc_2 with A B C A B C X Y Z; SumA).
  apply sams2_suma2__conga456 with A' B' C' X' Y' Z'; trivial; clear dependent D'; clear dependent E'.
    apply sams_assoc_1 with D E F D E F G H I; [..|apply sams_assoc_2 with X Y Z A B C X Y Z]; SumA.
    apply suma_assoc_1 with D E F D E F G H I; [..|apply suma_assoc_2 with X Y Z A B C X Y Z]; SumA.
Qed.

Lemma acute_ghalfa2_sams_suma2__ghalfa123 : forall A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z',
  SAMS A' B' C' D' E' F' -> Acute A B C ->
  SumA A B C D E F X Y Z -> SumA A' B' C' D' E' F' X' Y' Z' ->
  gHalfA D E F D' E' F' -> gHalfA X Y Z X' Y' Z' ->
  gHalfA A B C A' B' C'.
Proof.
  intros A B C D E F X Y Z A' B' C' D' E' F' X' Y' Z' HSams HAcute HSuma HSuma' HHalf1 HHalf2.
  apply acute_ghalfa2_sams_suma2__ghalfa456 with D E F X Y Z D' E' F' X' Y' Z'; SumA.
Qed.

End HalfAngle.

Section HalfAngle_2D.

Context `{T2D:Tarski_2D}.

Lemma halfa_perp__os : forall P A O B T, HalfA P A O B -> Perp O P T O -> OS O T P A.
Proof.
  intros P A O B T HP HT.
  assert (HCop := all_coplanar A O P T).
  apply cop_halfa_perp__os with B; assumption.
Qed.

Lemma halfa_perp__os2 : forall P A O B T, HalfA P A O B -> Perp O P T O ->
  OS O T P A /\ OS O T P B.
Proof.
  intros P A O B T HP HT.
  assert (HCop := all_coplanar A O P T).
  apply cop_halfa_perp__os2; assumption.
Qed.

End HalfAngle_2D.