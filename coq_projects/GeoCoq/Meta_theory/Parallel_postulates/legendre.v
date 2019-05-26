Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Export GeoCoq.Meta_theory.Parallel_postulates.SPP_ID.
Require Export GeoCoq.Meta_theory.Parallel_postulates.TCP_tarski.
Require Export GeoCoq.Meta_theory.Parallel_postulates.alternate_interior_angles_proclus.
Require Export GeoCoq.Meta_theory.Continuity.angle_archimedes.
Require Export GeoCoq.Meta_theory.Continuity.archimedes.
Require Export GeoCoq.Meta_theory.Continuity.aristotle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.euclid_5_original_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.existential_triangle_rah.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_perp_perp_TCP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_alternate_interior_angles.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_bis_playfair.
Require Export GeoCoq.Meta_theory.Parallel_postulates.playfair_universal_posidonius_postulate.
Require Export GeoCoq.Meta_theory.Parallel_postulates.proclus_SPP.
Require Export GeoCoq.Meta_theory.Parallel_postulates.rah_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.tarski_euclid.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_playfair_bis.
Require Export GeoCoq.Meta_theory.Parallel_postulates.triangle_existential_triangle.
Require Export GeoCoq.Meta_theory.Parallel_postulates.universal_posidonius_postulate_par_perp_perp.
Require Export GeoCoq.Tarski_dev.Annexes.defect.

Section Legendre.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Theorem stronger_legendre_s_first_theorem :
  aristotle_s_axiom ->
  forall A B C D E F,
    SumA C A B A B C D E F ->
    SAMS D E F B C A.
Proof.
  intros ari A B C D E F.
  apply (t22_20 (aristotle__obtuse_case_elimination ari)).
Qed.

Theorem legendre_s_first_theorem :
  archimedes_axiom ->
  forall A B C D E F,
    SumA C A B A B C D E F ->
    SAMS D E F B C A.
Proof.
  intros archi A B C D E F.
  apply (t22_20 (archi__obtuse_case_elimination archi)).
Qed.

Theorem legendre_s_second_theorem :
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights ->
  triangle_postulate.
Proof.
  assert (H:=existential_triangle__rah); assert (I:=rah__triangle); tauto.
Qed.

Lemma legendre_s_third_theorem_aux :
  aristotle_s_axiom ->
  triangle_postulate ->
  euclid_s_parallel_postulate.
Proof.
  assert (I:=aristotle__greenberg).
  assert (J:playfair_s_postulate->greenberg_s_axiom->decidability_of_intersection).
  { intro HP; assert (J:=playfair__alternate_interior HP).
    assert(K:=alternate_interior__proclus).
    assert(L:proclus_postulate->decidability_of_intersection); [|tauto].
    assert(M:=proclus_s_postulate_implies_strong_parallel_postulate).
    assert(N:=strong_parallel_postulate_implies_inter_dec); tauto.
  }
  assert (K:=triangle__playfair_bis).
  assert (L:=playfair_bis__playfair).
  assert (M:=playfair__universal_posidonius_postulate).
  assert (N:=universal_posidonius_postulate__perpendicular_transversal_postulate).
  assert (O:=inter_dec_plus_par_perp_perp_imply_triangle_circumscription).
  assert (P:=triangle_circumscription_implies_tarski_s_euclid).
  assert (Q:=tarski_s_euclid_implies_euclid_5).
  assert (R:=euclid_5__original_euclid); tauto.
Qed.

Theorem legendre_s_third_theorem :
  archimedes_axiom ->
  triangle_postulate ->
  euclid_s_parallel_postulate.
Proof.
  assert (H:=t22_24); assert (I:=legendre_s_third_theorem_aux); tauto.
Qed.

Lemma legendre_aux :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D B1 C1 P Q R S T U V W X,
    ~ Col A B C -> CongA A C B C B D ->
    Cong A C B D -> TS B C A D -> Out A B B1 -> Out A C C1 -> Bet B1 D C1 ->
    Defect A B C P Q R -> Defect A B1 C1 S T U -> SumA P Q R P Q R V W X ->
    SAMS P Q R P Q R /\ LeA V W X S T U.
Proof.
  intros noah A B C D B1 C1 P Q R S T U V W X HNCol HConga HCong HTS HOutB HOutC HBet HDef HDef1 HSuma.
  destruct (l11_49 A C B D B C) as [HCong1 [HConga1 HConga2]]; CongA; Cong.
    assert_diffs; auto.
  assert (HPar : Par_strict A C B D).
  { apply par_not_col_strict with B; Col.
    apply par_left_comm, l12_21_b; Side; CongA.
  }
  assert (HPar' : Par_strict A B C D).
  { apply par_not_col_strict with C; Col.
    apply par_left_comm, l12_21_b; Side; CongA.
  }
  assert (HNCol2:= HPar'); assert (HNCol3 := HPar'); assert (HNCol4 := HPar').
  apply par_strict_not_col_2 in HNCol2; apply par_strict_not_col_3 in HNCol3; apply par_strict_not_col_4 in HNCol4.
  assert (HB : ~ Col B1 B D /\ TS B D B1 C1 /\ Bet A B B1).
  { assert_diffs.
    apply par_strict_symmetry, (par_strict_col_par_strict B D A C C1) in HPar; Col.
    assert (HNCol' := par_strict_not_col_4 B D A C1 HPar).
    assert (B <> B1) by (intro; subst B1; apply HNCol'; Col).
    assert (~ Col B1 B D) by (intro; apply HNCol4; ColR).
    assert (TS B D B1 C1) by (repeat split; Col; exists D; Col).
    repeat (split; auto).
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with C1; Side.
  }
  destruct HB as [HNCol5 [HTS1 HBetB]].
  assert (HC : ~ Col C D B1 /\ C <> C1 /\ Bet A C C1).
  { assert_diffs.
    apply par_strict_symmetry, (par_strict_col_par_strict C D A B B1) in HPar'; Col.
    assert (HNCol' := par_strict_not_col_4 C D A B1 HPar').
    assert (C <> C1) by (intro; subst C1; apply HNCol'; Col).
    repeat split; auto.
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with B1; Side.
    repeat split; Col.
      intro; apply HNCol3; ColR.
    exists D; Col.
  }
  destruct HC as [HNCol6 [HCC1 HBetC]].
  assert_diffs.
  destruct (ts2__ex_bet2 B C D B1) as [Z [HZ1 HZ2]].
    apply l9_8_2 with C1; Side; apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    { apply l9_31.
        apply l9_17 with C1; trivial.
        exists A; assert_diffs; repeat split; Col; try (intro; apply HNCol; ColR);
        [exists B|exists C]; split; Col; Between.
      apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    }

  rename H into HAB1.
  destruct (ex_defect A B1 C) as [G [H [I HDef2]]]; auto.
  destruct (ex_defect B1 C C1) as [J [K [L HDef3]]]; auto.
  destruct (ex_defect C B B1) as [M [N [O HDef4]]]; auto.
  destruct (ex_defect B1 C D) as [A' [B' [C' HDef5]]]; auto.
  destruct (ex_defect C D C1) as [D' [E' [F' HDef6]]]; auto.
  destruct (ex_defect B1 B D) as [M' [N' [O' HDef7]]]; auto.
  assert (Hd := defect_distincts A B1 C G H I HDef2).
  assert (Hd2 := defect_distincts C B B1 M N O HDef4).
  assert (Hd3 := defect_distincts B1 C D A' B' C' HDef5).
  spliter; clean.
  destruct (ex_suma G H I A' B' C') as [G' [H' [I' HSuma1]]]; auto.
  destruct (ex_suma M N O A' B' C') as [J' [K' [L' HSuma2]]]; auto.

  destruct (t22_16_1bis noah A B1 C1 C G H I J K L S T U) as [HIsi3 HSuma3]; trivial.
  destruct (t22_16_1bis noah B1 C C1 D A' B' C' D' E' F' J K L) as [HIsi4 HSuma4]; trivial.
  destruct (t22_16_1bis noah A C B1 B P Q R M N O G H I) as [HIsi5 HSuma5]; trivial.
    apply defect_perm_132, HDef.
    apply defect_perm_132, HDef2.
  assert (HIsi1 : SAMS G H I A' B' C').
    apply sams_lea2__sams with G H I J K L; Lea.
    apply sams_suma__lea123789 with D' E' F'; trivial.
  assert (HIsi2 : SAMS M N O A' B' C').
    apply sams_lea2__sams with G H I A' B' C'; Lea.
    apply sams_suma__lea456789 with P Q R; trivial.
  assert (HSuma6 : SumA G' H' I' D' E' F' S T U).
    apply suma_assoc_2 with G H I A' B' C' J K L; trivial.
  assert (HIsi6 : SAMS G' H' I' D' E' F').
    apply sams_assoc_2 with G H I A' B' C' J K L; trivial.
  assert (HSuma7 : SumA P Q R J' K' L' G' H' I').
    apply suma_assoc_1 with M N O A' B' C' G H I; trivial.
  assert (HIsi7 : SAMS P Q R J' K' L').
    apply sams_assoc_1 with M N O A' B' C' G H I; trivial.
  destruct (t22_16_2 noah C B B1 D M' N' O' A' B' C' P Q R M N O Z J' K' L') as [HIsi8 HSuma8]; trivial.
    apply defect_perm_231, (conga3_defect__defect A B C); CongA.
    apply defect_perm_231, HDef5.
  assert (HLea : LeA P Q R J' K' L') by (apply sams_suma__lea123789 with M' N' O'; trivial).

  split.
    suma.assert_diffs.
    apply sams_lea2__sams with P Q R J' K' L'; Lea.
  apply lea_trans with G' H' I'.
    apply sams_lea456_suma2__lea with P Q R P Q R J' K' L'; trivial.
  apply sams_suma__lea123789 with D' E' F'; trivial.
Qed.

Lemma legendre_aux1 : forall A B C B' C',
  ~ Col A B C -> Out A B B' -> Out A C C' ->
  exists D', InAngle D' B A C /\ CongA A C' B' C' B' D' /\
             Cong A C' B' D' /\ TS B' C' A D'.
Proof.
  intros A B C B' C' HNCol HOutB HOutC.
  assert_diffs.
  assert (HNCol' : ~ Col A B' C') by (intro; assert_diffs; apply HNCol; ColR).
  destruct (midpoint_existence B' C') as [M HM].
  destruct (symmetric_point_construction A M) as [D' HD].
  assert (HNCol1 : ~ Col A M B') by (intro; assert_diffs; apply HNCol'; ColR).
  assert (HNCol2 : ~ Col D' B' C') by (intro; assert_diffs; apply HNCol'; ColR).
  exists D'.
  assert_diffs; destruct HM; destruct HD; split.
    apply l11_25 with D' B' C'; try (apply out_trivial); auto.
    repeat split; auto.
    exists M; split; trivial.
    right; apply bet_out; auto.
  destruct (l11_49 A M C' D' M B') as [HCong1 [HConga1 HConga2]]; Cong.
    apply l11_14; Between.
  split.
    apply (out_conga A C' M M B' D'); try (apply out_trivial); try (apply bet_out); Between; CongA.
  split; Cong.
  repeat split; Col.
  exists M; split; Col.
Qed.

Lemma legendre_aux2 :
  ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C,
    ~ Col A B C ->  Acute B A C ->
    (forall T,
       InAngle T B A C ->
       exists X Y : Tpoint, Out A B X /\ Out A C Y /\ Bet X T Y) ->
    forall P Q R S T U,
      Defect A B C P Q R -> GradAExp P Q R S T U ->
      exists B' C' P' Q' R',
        (Out A B B' /\ Out A C C' /\
         Defect A B' C' P' Q' R' /\ LeA S T U P' Q' R').
Proof.
  intros noah A B C HNCol HAcute legendre P Q R S T U HDef.
  induction 1; rename A0 into P; rename B0 into Q; rename C0 into R.
    exists B; exists C; exists P; exists Q; exists R; assert_diffs.
    repeat split; (try apply out_trivial); Lea.
  rename D into S; rename E into T; rename F into U.
  destruct IHGradAExp as [B' [C' [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]]]]; trivial.
  destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
  assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
  destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
  assert (Hd := defect_distincts A B' C' P' Q' R' HDef'); spliter; assert_diffs.
  destruct (ex_defect A B'' C'') as [P'' [Q'' [R'' HDef'']]]; auto.
    intro; subst; apply HNCol; ColR.
  exists B''; exists C''; exists P''; exists Q''; exists R''.
  repeat (split; trivial).
  destruct (ex_suma P' Q' R' P' Q' R') as [V [W [X HSuma1]]]; auto.
  destruct (legendre_aux noah A B' C' D' B'' C'' P' Q' R' P'' Q'' R'' V W X) as [HIsi1 HLea1]; trivial.
    apply l6_7 with B; trivial; apply l6_6; trivial.
    apply l6_7 with C; trivial; apply l6_6; trivial.
  apply lea_trans with V W X; trivial.
  apply sams_lea2_suma2__lea with S T U S T U P' Q' R' P' Q' R'; trivial.
Qed.

Lemma legendre_s_fourth_theorem_aux :
  archimedes_axiom ->
  legendre_s_parallel_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros archi legendre.
  destruct legendre as [B [A [C [HNCol [HAcute legendre]]]]].
  assert_diffs.
  destruct (ex_defect A B C) as [P [Q [R HDef]]]; auto.
  destruct (col_dec P Q R) as [HCol|HNCol1].
  - apply archi__obtuse_case_elimination in archi.
    apply (defect_ncol_out__rah A B C P Q R); Col.
    apply not_bet_out; Col.
    intro HBet.
    apply HNCol.
    apply defect_perm_213 in HDef.
    destruct HDef as [D [E [F [[G [H [I [HSuma1 HSuma2]]]] HSuppa]]]].
    apply out_col, l6_6, out_lea__out with D E F.
      apply (bet_suppa__out P Q R); [|apply suppa_sym]; assumption.
    apply sams_suma__lea456789 with G H I; trivial.
    apply (t22_20 archi); trivial.
  - destruct (archi__gradaexp_destruction archi P Q R HNCol1) as [S [T [U [HGAE HObtuse]]]].
    apply archi__obtuse_case_elimination in archi.
    apply not_col_permutation_4 in HNCol.
    destruct (legendre_aux2 archi A B C HNCol HAcute legendre P Q R S T U HDef HGAE) as [B' [C' HInter]].
    destruct HInter as [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]].
    apply (obtuse_gea_obtuse P' Q' R'), obtuse__nsams in HObtuse; auto.
    exfalso.
    apply HObtuse.
    destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
    assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
    destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
    assert_diffs.
    destruct (ex_defect A B'' C'') as [S' [T' [U' HDef'']]]; auto.
      intro; subst; apply HNCol; ColR.
    destruct (ex_suma P' Q' R' P' Q' R') as [V [W [X HSuma]]]; auto.
    destruct (legendre_aux archi A B' C' D' B'' C'' P' Q' R' S' T' U' V W X); trivial;
    [apply l6_7 with B|apply l6_7 with C]; trivial; apply l6_6; trivial.
Qed.

Theorem legendre_s_fourth_theorem :
  archimedes_axiom ->
  legendre_s_parallel_postulate ->
  postulate_of_existence_of_a_triangle_whose_angles_sum_to_two_rights.
Proof.
  assert (H:=legendre_s_fourth_theorem_aux).
  assert (I:=rah__triangle).
  assert (J:=triangle__existential_triangle); tauto.
Qed.

End Legendre.