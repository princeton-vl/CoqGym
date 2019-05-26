Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Meta_theory.Parallel_postulates.rah_thales_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_converse_postulate_weak_triangle_circumscription_principle.
Require Import GeoCoq.Meta_theory.Parallel_postulates.thales_postulate_thales_converse_postulate.
Require Import GeoCoq.Meta_theory.Parallel_postulates.weak_triangle_circumscription_principle_bachmann_s_lotschnittaxiom.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section universal_posidonius_postulate_perpendicular_transversal_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma universal_posidonius_postulate__perpendicular_transversal_postulate :
  universal_posidonius_postulate -> perpendicular_transversal_postulate.
Proof.
intros HP A B C D P Q HPar HPerp1 HCop.
elim HPar; intro HParS; [|destruct HParS as [_ [_ [HC1 HC2]]]; assert_diffs;
                          apply perp_sym; apply perp_col0 with A B; Col; ColR].
assert (H := HPerp1); destruct H as [R HR];
apply perp_in_col in HR; destruct HR as [HC1 HC2].
assert (HEF : exists E F, Col A B E /\ Col C D F /\ Perp A B E F /\ E <> R).
  {
  destruct (l8_18_existence A B C) as [E1 [HC3 HPerp2]];
  [apply par_strict_not_col_1 with D; Par|].
  destruct (l8_18_existence A B D) as [E2 [HC4 HPerp3]];
  [apply par_strict_not_col_1 with C; Par|].
  elim (eq_dec_points E1 R); intro; treat_equalities;
  [|exists E1, C; repeat (split; Col; Perp)].
  elim (eq_dec_points E1 E2); intro; treat_equalities;
  [|exists E2, D; repeat (split; Col; Perp)].
  assert (HC4 : Col E1 C D)
    by (apply cop_perp2__col with A B; Perp; apply par__coplanar in HPar; Cop).
  destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists E1; Col.
  }
destruct HEF as [E [F [HC3 [HC4 [HPerp2 HD1]]]]].
assert (HGH : exists G H,
                Col A B G /\ Col C D H /\ Perp A B G H /\ E <> G /\ F <> H).
  {
  destruct (l8_18_existence A B C) as [E1 [HC5 HPerp3]];
  [apply par_strict_not_col_1 with D; Par|].
  destruct (l8_18_existence A B D) as [E2 [HC6 HPerp4]];
  [apply par_strict_not_col_1 with C; Par|].
  elim (eq_dec_points E1 E); intro HD; treat_equalities;
  [|exists E1, C; repeat (split; Col; Perp); intro; treat_equalities; apply HD;
    apply l6_21 with A B F E; assert_diffs; Col;
    [elim (perp_not_col2 _ _ _ _ HPerp2); Col|
     apply cop_perp2__col with A B; Perp]]; Cop.
  elim (eq_dec_points E1 E2); intro HD'; treat_equalities;
  [assert (HC7 : Col E1 C D)
     by (apply cop_perp2__col with A B; Perp; apply par__coplanar in HPar; Cop);
   destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists E1; Col|].
  exists E2, D; repeat (split; Col; Perp); intro; treat_equalities; apply HD'.
  apply l6_21 with A B F E1; assert_diffs; Col;
  [elim (perp_not_col2 _ _ _ _ HPerp2); Col|apply cop_perp2__col with A B; Perp;
                                            apply par__coplanar in HPar; Cop].
  }
destruct HGH as [G [H [HC5 [HC6 [HPerp3 [HD2 HD3]]]]]].
assert (HSacc1 : Saccheri E F H G).
  {
  split; [apply perp_per_1; apply perp_col0 with A B; Perp|].
  split; [apply perp_per_1; apply perp_sym; apply perp_col0 with A B; Perp|].
  split; [assert (Cong E F G H); Cong; apply HP with A B C D; Col|].
  apply l12_6; apply par_strict_col2_par_strict with C D; Col.
  apply par_strict_symmetry;
  apply par_strict_col2_par_strict with A B; Col; Par.
  }
destruct (midpoint_existence E G) as [M1 HMid1].
destruct (midpoint_existence F H) as [M2 HMid2].
assert (HLamb := mid2_sac__lam6521 _ _ _ _ _ _ HSacc1 HMid2 HMid1).
assert (HSacc2 : Saccheri E F M2 M1).
  {
  split; [unfold Lambert in *; spliter; Perp|].
  split; [unfold Lambert in *; spliter; Perp|].
  assert (HCong : Cong E F M1 M2); [|split; Cong].
    {
    apply HP with A B C D; Col; try solve [assert_diffs; assert_cols; ColR].
    apply perp_sym; apply perp_col0 with E M1;
    try solve [assert_diffs; assert_cols; Col; ColR].
    apply per_perp; unfold Lambert in *; spliter; Perp.
    }
  apply l12_6; apply par_strict_col2_par_strict with C D; Col;
  try solve [assert_diffs; assert_cols; Col; ColR].
  apply par_strict_symmetry;
  apply par_strict_col2_par_strict with A B; Col; Par;
  assert_diffs; assert_cols; Col; ColR.
  }
assert (HRAH : postulate_of_right_saccheri_quadrilaterals)
  by (apply per_sac__rah with M1 M2 F E; try apply sac_perm;
      unfold Lambert in *; spliter; auto).
assert (HP' : forall A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD,
        Perp A1 A2 B1 B2 -> Perp A1 A2 C1 C2 -> Perp B1 B2 D1 D2 ->
        Col A1 A2 IAB -> Col B1 B2 IAB ->
        Col A1 A2 IAC -> Col C1 C2 IAC ->
        Col B1 B2 IBD -> Col D1 D2 IBD ->
        Coplanar IAB IAC IBD C1 -> Coplanar IAB IAC IBD C2 ->
        Coplanar IAB IAC IBD D1 -> Coplanar IAB IAC IBD D2 ->
       ~ Col IAB IAC IBD ->
        exists I, Col C1 C2 I /\ Col D1 D2 I).
  {
  cut bachmann_s_lotschnittaxiom.

    {
    clear HP; clear dependent P; clear dependent Q; clear dependent R.
    intros bla A1 A2 B1 B2 C1 C2 D1 D2 IAB IAC IBD HPerpAB HPerpAC HPerpBD.
    intros HCol1 HCol2 HCol3 HCol4 HCol5 HCol6 HCop1 HCop2 HCop3 HCop4 HNC1.
    assert (Col IAB IAC A1) by (assert_diffs; ColR).
    assert (Col IAB IAC A2) by (assert_diffs; ColR).
    assert (Col IAB IBD B1) by (assert_diffs; ColR).
    assert (Col IAB IBD B2) by (assert_diffs; ColR).
    assert (Coplanar IAB IAC IBD A1) by Cop.
    assert (Coplanar IAB IAC IBD A2) by Cop.
    assert (Coplanar IAB IAC IBD B1) by Cop.
    assert (Coplanar IAB IAC IBD B2) by Cop.
    assert (HNC2 : ~ Col A1 A2 D1).
      {
      apply par_strict_not_col_1 with D2; apply par_not_col_strict with IBD;
      Col; try (intro; apply HNC1; assert_diffs; ColR).
      apply l12_9 with B1 B2; Perp; CopR.
      }
    assert (HNC3 : ~ Col B1 B2 C1).
      {
      apply par_strict_not_col_1 with C2; apply par_not_col_strict with IAC;
      Col; try (intro; apply HNC1; assert_diffs; ColR).
      apply l12_9 with A1 A2; Perp; CopR.
      }
    assert (HParA : Par_strict A1 A2 D1 D2).
      apply par_not_col_strict with D1; Col; apply l12_9 with B1 B2; Perp; CopR.
    assert (HParB : Par_strict B1 B2 C1 C2).
      apply par_not_col_strict with C1; Col; apply l12_9 with A1 A2; Perp; CopR.
    assert (HNCol3 : ~ Col IAC B1 B2) by (apply par_not_col with C1 C2; Par; ColR).
    assert (HNCol4 : ~ Col IBD A1 A2) by (apply par_not_col with D1 D2; Par; ColR).
    assert (HPQ : IAC <> IAB) by (assert_diffs; auto).
    assert (HQR : IAB <> IBD) by (assert_diffs; auto).
    destruct (diff_col_ex3 C1 C2 IAC) as [P1 [HC1P1 [HC2P1 [HPP1 HCP1]]]]; Col.
    destruct (diff_col_ex3 D1 D2 IBD) as [R1 [HD1R1 [HD2R1 [HRR1 HDR1]]]]; Col.
    destruct (bla IAC IAB IBD P1 R1) as [I [HI1 HI2]]; auto.
      apply perp_per_2; apply perp_col2 with A1 A2; Col;
      apply perp_sym; apply perp_col2 with B1 B2; Col; Perp.
      apply perp_per_2; apply perp_col2 with A1 A2; Col;
      apply perp_sym; apply perp_col2 with C1 C2; Col; Perp.
      apply perp_per_2; apply perp_col2 with B1 B2; Col;
      apply perp_sym; apply perp_col2 with D1 D2; Col; Perp.
      assert_diffs; apply col_cop2__cop with C1 C2; Col; CopR.
      assert_diffs; apply col_cop2__cop with D1 D2; Col; CopR.
    exists I.
    split; assert_diffs; ColR.
    }

    {
    apply weak_triangle_circumscription_principle__bachmann_s_lotschnittaxiom.
    apply thales_converse_postulate__weak_triangle_circumscription_principle.
    apply thales_postulate__thales_converse_postulate.
    apply rah__thales_postulate; assumption.
    }
  }
assert (HNC : ~ Col E R F).
  {
  assert_diffs; intro; destruct HParS as [_ [_ [_ HF]]];
  apply HF; exists F; split; Col; ColR.
  }
assert (~ Col C D R).
  {
  assert_diffs; intro; destruct HParS as [_ [_ [_ HF]]];
  apply HF; exists R; split; Col; ColR.
  }
assert (Col E R A) by (assert_diffs; ColR).
assert (Coplanar E R F A) by Cop.
assert (Col E R B) by (assert_diffs; ColR).
assert (Coplanar E R F B) by Cop.
assert (~ Col A B F) by (assert_diffs; intro; apply HNC; ColR).
assert (Coplanar A B F C)
  by (assert_diffs; apply col2_cop__cop with C D;
      try (apply pars__coplanar); Col).
assert (Coplanar A B F D)
  by (assert_diffs; apply col2_cop__cop with C D;
      try (apply pars__coplanar); Col).
assert (Coplanar C D R P)
  by (assert_diffs; apply col2_cop__cop with P Q; Col; Cop).
assert (Coplanar C D R Q)
  by (assert_diffs; apply col2_cop__cop with P Q; Col; Cop).
assert (Coplanar A B Q F) by CopR.
assert (Coplanar E R F P) by CopR.
assert (Coplanar E R F Q) by CopR.
assert (Coplanar E R F C) by CopR.
assert (Coplanar E R F D) by CopR.
assert (Coplanar A B Q E) by Cop.
destruct (HP' A B E F P Q C D E R F) as [S [HC7 HC8]]; Col;
[apply perp_col0 with F M2; try (apply perp_sym; apply per_perp);
 try solve [assert_diffs; assert_cols; Col; ColR];
 rewrite (lam_per__rah M1 _ _ _); try apply lam_perm; assumption|].
assert (HSacc3 : Saccheri E F S R).
  {
  split; [apply perp_per_1; apply perp_col0 with A B; Perp|].
  split; [apply perp_per_1; apply perp_col0 with P Q; try apply perp_col0 with A B; Perp;
          intro; treat_equalities; destruct HParS as [_ [_ [_ HF]]];
          exfalso; apply HF; exists S; Col|].
  split; [assert (Cong E F R S); Cong; apply HP with A B C D; Col;
          apply perp_col0 with P Q; Perp; intro; treat_equalities;
          destruct HParS as [_ [_ [_ HF]]]; exfalso; apply HF; exists R; Col|].
  apply l12_6; apply par_strict_col2_par_strict with C D; Col;
  try solve [assert_diffs; assert_cols; Col; ColR];
  try apply par_strict_symmetry;
  try apply par_strict_col2_par_strict with A B; Col; Par.
  intro; treat_equalities; assert (HC8 : Col E P Q)
    by (apply col_cop2_perp2__col with F A B; Col; Perp; Cop).
  apply HD1; elim (perp_not_col2 _ _ _ _ HPerp2); intro;
  [apply l6_21 with A B E F|apply l6_21 with A B F E];
  assert_diffs; Col; try ColR.
  }
apply perp_col0 with S R; try solve [assert_diffs; assert_cols; Col; ColR].
apply perp_col0 with F S; try solve [assert_diffs; assert_cols; Col; ColR].
apply per_perp; try solve[apply sac_distincts in HSacc3; spliter; auto].
apply l8_2; apply HRAH with E; apply sac_perm; assumption.
Qed.

End universal_posidonius_postulate_perpendicular_transversal_postulate.