Require Export GeoCoq.Meta_theory.Parallel_postulates.parallel_postulates.
Require Export GeoCoq.Meta_theory.Parallel_postulates.par_trans_NID.

Section T13.

Context `{TE:Tarski_euclidean}.

Lemma cop_npar__inter_exists : forall A1 B1 A2 B2,
  Coplanar A1 B1 A2 B2 -> ~ Par A1 B1 A2 B2 -> exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
intros.
induction (eq_dec_points A1 B1).
subst; exists A2; Col.
induction (eq_dec_points A2 B2).
subst; exists A1; Col.
induction (inter_dec A1 B1 A2 B2).

  assumption.

  exfalso.
  apply H0.
  unfold Par.
  left.
  unfold Par_strict.
  repeat split; assumption.
Qed.

Lemma cop_npar__inter : forall A1 B1 A2 B2, A1 <> B1 -> A2 <> B2 ->
  Coplanar A1 B1 A2 B2 -> ~ Par A1 B1 A2 B2 -> exists X, Inter A1 B1 A2 B2 X.
Proof.
intros.
destruct (cop_npar__inter_exists A1 B1 A2 B2) as [X []].
  assumption.
  assumption.
exists X.
split.
  assumption.
split.
  induction (col_dec A2 A1 B1).
    exists B2.
    split.
      Col.
    intro.
    apply H2.
    right.
    repeat split; ColR.
  exists A2.
  split; Col.
split; Col.
Qed.

Lemma parallel_uniqueness :
 forall A1 A2 B1 B2 C1 C2 P : Tpoint,
  Par A1 A2 B1 B2 -> Col P B1 B2 ->
  Par A1 A2 C1 C2 -> Col P C1 C2 ->
  Col C1 B1 B2 /\ Col C2 B1 B2.
Proof.
    apply tarski_s_euclid_implies_playfair.
    unfold tarski_s_parallel_postulate; apply euclid.
Qed.

Lemma par_trans : forall A1 A2 B1 B2 C1 C2,
  Par A1 A2 B1 B2 -> Par B1 B2 C1 C2 -> Par A1 A2 C1 C2.
Proof.
    intros.
    apply playfair_implies_par_trans with B1 B2; [|assumption..].
    unfold playfair_s_postulate.
    apply parallel_uniqueness.
Qed.

Lemma inter__npar : forall A1 A2 B1 B2 X,
  Inter A1 A2 B1 B2 X -> ~ Par A1 A2 B1 B2.
Proof.
    intros.
    destruct H as [HA [[P []] []]].
    induction 1.
    apply (par_not_col A1 A2 B1 B2 X); Col.
    spliter.
    apply H0, (col3 B1 B2); Col.
Qed.

Lemma l12_16 : forall A1 A2 B1 B2 C1 C2 X,
  Par A1 A2 B1 B2 -> Coplanar B1 B2 C1 C2 -> Inter A1 A2 C1 C2 X -> exists Y, Inter B1 B2 C1 C2 Y.
Proof.
    intros.
    assert_diffs.
    apply cop_npar__inter; auto.
      destruct H1.
      auto.
    intro.
    apply inter__npar in H1.
    apply H1.
    apply par_trans with B1 B2; assumption.
Qed.

Lemma par_dec : forall A B C D, Par A B C D \/ ~ Par A B C D.
Proof. exact (par_trans__par_dec par_trans). Qed.

Lemma par_not_par : forall A B C D P Q, Par A B C D -> ~Par A B P Q -> ~Par C D P Q.
Proof.
intros A B C D P Q HPar HNPar.
intro HNPar'.
apply HNPar.
apply par_trans with C D; Par.
Qed.

Lemma cop_par__inter : forall A B C D P Q,
  Par A B C D -> ~Par A B P Q -> Coplanar C D P Q ->
  exists Y, Col P Q Y /\ Col C D Y.
Proof.
    intros A B C D P Q HPar HNPar HCop.
    destruct (cop_npar__inter_exists C D P Q) as [Y []].
      assumption.
      intro.
      apply HNPar, par_trans with C D; assumption.
    exists Y; split; Col.
Qed.

Lemma l12_19 :
  forall A B C D ,
   ~Col A B C -> Par A B C D -> Par B C D A ->
   Cong A B C D /\ Cong B C D A /\ TS B D A C /\ TS A C B D.
Proof.
    intros.
    assert(exists P, Midpoint P A C) by (eapply midpoint_existence).
    ex_and H2 P.
    double B P D'.
    assert(Cong C D' A B).
      apply (l7_13 P); assumption.
    assert(Cong B C D' A).
      apply (l7_13 P); Midpoint.
    assert(Par A B C D').
      assert_diffs; apply l12_17 with P; auto.
    assert(Par C D C D').
      eapply par_trans.
        apply par_symmetry.
        apply H0.
      apply H6.
    assert(Col C D D').
      apply par_id.
      assumption.
    assert(Par B C D' A).
      assert_diffs; apply l12_17 with P; Midpoint.
    assert(Par D A D' A).
      eapply par_trans.
        apply par_symmetry.
        apply H1.
      assumption.
    assert(Col A D D').
      apply par_id.
      Par.
    assert(D = D').
      assert_diffs; apply (l6_21 A D C D); Col.
        intro.
        apply H.
        assert(Col P C D).
          apply col_permutation_2.
          apply (col_transitivity_1 _ A); Col.
        assert(Col P C D').
          apply col_permutation_2.
          apply (col_transitivity_1 _ D); Col.
        assert(Col P A D').
          apply (col_transitivity_1 _ C); Col.
        apply (col3 P D'); Col.
        intro; treat_equalities; assert_cols; Col.
    subst D'.
    split.
      Cong.
    split.
      Cong.
    assert(B <> D).
      intro; treat_equalities; assert_cols; Col.
    split.
      apply l12_18_c with P; Cong; Col.
    apply l12_18_d with P; Cong; Col.
Qed.

Lemma l12_20_bis :
  forall A B C D,
   Par A B C D -> Cong A B C D -> TS B D A C ->
   Par B C D A /\ Cong B C D A /\ TS A C B D.
Proof.
    intros.
    assert(B <> C) by (assert_diffs; auto).
    assert(A <> D) by (assert_diffs; auto).
    assert(~ Col A B C).
      intro.
      assert(Col A B D).
        apply not_strict_par1 with C C; Col; Par.
      unfold TS in H1.
      spliter.
      contradiction.
    assert(exists P, Midpoint P A C) by (apply midpoint_existence).
    ex_and H5 P.
    double B P D'.
    assert(Par B C D' A).
      eapply l12_17.
        assumption.
        apply H5.
      apply l7_2.
      assumption.
    assert(Par A B C D').
      assert_diffs; apply l12_17 with P; auto.
    assert(Cong C D' A B).
      apply (l7_13 P); assumption.
    assert(Cong B C D' A).
      apply (l7_13 P); Midpoint.
    assert(Par C D C D').
      eapply par_trans.
        apply par_symmetry.
        apply H.
      assumption.
    assert(Col C D D').
      apply par_id; assumption.
    assert(Cong C D C D').
      apply (cong_transitivity _ _ A B); Cong.
    assert(D = D' \/ Midpoint C D D').
      apply l7_20; Col.
    induction H14.
    { subst D'.
      assert(Par B C D A) by Par.
      split.
        assumption.
      assert(HH:=l12_19 A B C D H4 H H14).
      spliter.
      split; assumption.
    }
    (************)
    exfalso.
    assert(TS A C B D).
      apply par_two_sides_two_sides; assumption.
    assert(~ Col A C D).
      apply (par_not_col A B C D A); Col.
      apply par_not_col_strict with C; Col.
    assert(~ Col D' A C).
      intro.
      apply H16.
      ColR.
    assert(TS A C B D').
      repeat split; Col.
      exists P.
      split.
        Col.
      Between.
    assert (TS A C D D').
      repeat split; Col.
      exists C.
      split.
        Col.
      Between.
    apply (l9_9 A C B D).
      assumption.
    apply l9_8_1 with D'; assumption.
Qed.

Lemma l12_20 :
 forall A B C D,
  Par A B C D -> Cong A B C D -> TS A C B D ->
  Par B C D A /\ Cong B C D A /\ TS A C B D.
Proof.
    intros.
    assert(TS B D A C).
      apply par_two_sides_two_sides.
        apply par_comm.
        assumption.
      assumption.
    assert(HH:=l12_20_bis A B C D H H0 H2).
    spliter.
    split.
      assumption.
    split.
      assumption.
    assumption.
Qed.

Lemma l12_21_a :
 forall A B C D,
  TS A C B D ->
  (Par A B C D -> CongA B A C D C A).
Proof.
    apply postulates_in_euclidean_context; simpl; repeat (try (left; reflexivity); right).
Qed.

Lemma l12_21 : forall A B C D,
 TS A C B D ->
 (CongA B A C D C A <-> Par A B C D).
Proof.
    intros.
    split.
      intro.
      apply l12_21_b ; assumption.
    intro.
    apply l12_21_a; assumption.
Qed.

Lemma l12_22_a : forall A B C D P,
 Out P A C -> OS P A B D -> Par A B C D ->
 CongA B A P D C P.
Proof.
    cut (forall A B C D P,
         A <> P -> Bet P A C -> OS P A B D -> Par A B C D ->
         CongA B A P D C P).
    { intros Haux A B C D P HOut HOS HPar.
      destruct HOut as [HAP [HCP [|]]].
        apply Haux; trivial.
      apply conga_sym, Haux; Par.
      apply col_one_side with A; Col; Side.
    }
    intros A B C D P HAP HBet HOS HPar.
    destruct (eq_dec_points A C).
    { subst C.
      apply out2__conga; [|apply out_trivial; auto].
      apply col_one_side_out with P; Side.
      apply par_id; Par.
    }
    destruct (segment_construction B A B A) as [B' []].
    assert_diffs.
    apply conga_trans with B' A C.
      apply l11_14; auto.
    apply l11_10 with B' C D A; try (apply out_trivial); auto; [|apply l6_6, bet_out; Between].
    apply l12_21_a; [|apply par_col_par_2 with B; Col].
    apply l9_2, l9_8_2 with B; [|apply col_one_side with P; Side; Col].
    assert (HNCol : ~ Col P A B) by (apply one_side_not_col123 with D, HOS).
    assert (HNCol1 : ~ Col B A C) by (intro; apply HNCol; ColR).
    repeat split; trivial.
      intro; apply HNCol1; ColR.
    exists A; Col.
Qed.

Lemma l12_22 :
  forall A B C D P,
  Out P A C -> OS P A B D ->
  (CongA B A P D C P <-> Par A B C D).
Proof.
    intros.
    split; intro.
      apply (l12_22_b _ _ _ _ P); assumption.
      apply l12_22_a; assumption.
Qed.

Lemma l12_23 :
 forall A B C,
  ~Col A B C ->
  exists B', exists C',
  TS A C B B' /\ TS A B C C' /\
      Bet B' A C' /\ CongA A B C B A C' /\ CongA A C B C A B'.
Proof.
    intros.
    assert(exists B0, Midpoint B0 A B) by (apply midpoint_existence).
    assert(exists C0, Midpoint C0 A C) by (apply midpoint_existence).
    ex_and H0 B0.
    ex_and H1 C0.
    prolong B C0 B' B C0.
    prolong C B0 C' C B0.
    exists B'.
    exists C'.
    assert(TS A C B B').
      apply mid_two_sides with C0; Col.
      split.
        assumption.
      Cong.
    assert(TS A B C C').
      eapply mid_two_sides with B0; Col.
      split.
        assumption.
      Cong.
    split.
      assumption.
    split.
      assumption.
    assert(Par A B' C B).
      eapply l12_17.
        intro.
        treat_equalities.
        assert(C0 = B0).
          eapply l7_17.
            2: apply H2.
          split.
            apply between_symmetry.
            assumption.
          Cong.
        treat_equalities.
        Col.
        apply H0.
      split.
        apply between_symmetry.
        assumption.
      Cong.
    assert(Par A C' B C).
      eapply l12_17.
        intro.
        treat_equalities.
        assert(C0 = B0).
          eapply l7_17.
            apply H0.
          split.
            apply between_symmetry.
            assumption.
          Cong.
        treat_equalities.
        Col.
        apply H2.
      split.
        apply between_symmetry.
        assumption.
      Cong.
    assert(Par A B' A C').
      eapply par_trans.
        apply H8.
      apply par_symmetry.
      apply par_right_comm.
      assumption.
    apply par_id in H10.
    assert(OS A C B0 C').
      eapply out_one_side_1.
        intro.
        apply H.
        assert_diffs.
        eapply (col_transitivity_1 _ B0); Col.
        apply col_trivial_2.
      apply bet_out.
        intro.
        treat_equalities.
        assert_diffs; auto.
      assumption.
    assert(OS A C B0 B).
      eapply out_one_side_1.
        intro.
        apply H.
        eapply (col_transitivity_1 _ B0); Col.
          intro.
          treat_equalities.
          Col.
        apply col_trivial_3.
      assert_diffs; apply bet_out; Between.
    assert(OS A C B C').
      eapply one_side_transitivity.
        2:apply H11.
      apply one_side_symmetry.
      assumption.
    assert(TS A C B' C').
      apply l9_2.
      eapply l9_8_2.
        apply H6.
      assumption.
    split.
      apply col_two_sides_bet with C; assumption.
    split.
      apply l9_2 in H7.
      assert(HH:= l12_21_a A C' B C H7 H9); CongA.
    apply par_symmetry in H8.
    apply invert_two_sides in H6.
    assert(HH:= l12_21_a C B A B' H6 H8); CongA.
Qed.

Lemma cop_npars__inter_exists :
 forall A1 B1 A2 B2,
  Coplanar A1 B1 A2 B2 -> ~ Par_strict A1 B1 A2 B2 ->
  exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
    intros.
    induction (eq_dec_points A1 B1).
      subst.
      exists A2.
      Col.
    induction (eq_dec_points A2 B2).
      subst.
      exists A1.
      Col.
    induction (inter_dec A1 B1 A2 B2).
      assumption.
    exfalso.
    apply H0.
    repeat split; assumption.
Qed.

Lemma cop2_npar__inter : forall A B A' B' X Y,
  Coplanar A B X Y -> Coplanar A' B' X Y -> ~ Par A B A' B' ->
  (exists P, Col P X Y /\ (Col P A B \/ Col P A' B')).
Proof.
    intros.
    induction(par_dec A B X Y).
      assert(~ Par A' B' X Y).
        intro.
        apply H1.
        apply(par_trans _ _ X Y); Par.
      destruct(cop_npar__inter_exists A' B' X Y) as [P []].
        assumption.
        assumption.
      exists P.
      split.
        Col.
      right.
      Col.
    destruct(cop_npar__inter_exists A B X Y) as [P []].
      assumption.
      assumption.
    exists P.
    split.
      Col.
    left.
    Col.
Qed.

Lemma not_par_one_not_par : forall A B A' B' X Y, ~Par A B A' B' -> ~Par A B X Y \/ ~Par A' B' X Y.
Proof.
    intros.
    destruct (par_dec A B X Y).
      right.
      intro.
      apply H.
      apply par_trans with X Y; Par.
    left.
    assumption.
Qed.

Lemma col_par_par_col : forall A B C A' B' C', Col A B C -> Par A B A' B' -> Par B C B' C' -> Col A' B' C'.
Proof.
    intros.
    apply par_distincts in H0.
    apply par_distincts in H1.
    spliter.
    assert(Par A B B C).
      right.
      repeat split; Col.
    assert(Par A' B' B' C').
      apply (par_trans _ _ A' B').
        Par.
      apply (par_trans _ _ B C).
        apply (par_trans _ _ A B); Par.
      Par.
    induction H7.
      apply False_ind.
      apply H7.
      exists B'.
      split; Col.
    spliter.
    Col.
Qed.

Lemma cop_par_perp__perp : forall A B C D P Q, Par A B C D -> Perp A B P Q -> Coplanar C D P Q ->
  Perp C D P Q.
Proof.
    apply universal_posidonius_postulate__perpendicular_transversal_postulate.
    apply playfair__universal_posidonius_postulate.
    unfold playfair_s_postulate; apply parallel_uniqueness.
Qed.

Lemma cop4_par_perp2__par : forall A B C D E F G H,
  Par A B C D -> Perp A B E F -> Perp C D G H ->
  Coplanar A B E G -> Coplanar A B E H ->
  Coplanar A B F G -> Coplanar A B F H ->
  Par E F G H.
Proof.
    apply par_perp_perp_implies_par_perp_2_par.
    intros A B; intros.
    apply (cop_par_perp__perp A B); assumption.
Qed.

End T13.

Section T13_2D.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma not_par_inter_exists : forall A1 B1 A2 B2,
  ~ Par A1 B1 A2 B2 -> exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
intros.
apply cop_npar__inter_exists.
apply all_coplanar.
assumption.
Qed.

Lemma l12_16_2D : forall A1 A2 B1 B2 C1 C2 X,
  Par A1 A2 B1 B2 -> Inter A1 A2 C1 C2 X -> exists Y, Inter B1 B2 C1 C2 Y.
Proof.
    intros.
    assert (HC := all_coplanar B1 B2 C1 C2).
    apply l12_16 with A1 A2 X; assumption.
Qed.

Lemma par_inter : forall A B C D P Q,
  Par A B C D -> ~Par A B P Q ->
  exists Y, Col P Q Y /\ Col C D Y.
Proof.
    intros.
    assert (HC := all_coplanar C D P Q).
    apply (cop_par__inter A B); assumption.
Qed.

Lemma not_par_strict_inter_exists :
 forall A1 B1 A2 B2,
  ~Par_strict A1 B1 A2 B2 ->
  exists X, Col X A1 B1 /\ Col X A2 B2.
Proof.
    intros.
    apply (cop_npars__inter_exists).
    apply all_coplanar.
    assumption.
Qed.

Lemma not_par_inter : forall A B A' B' X Y, ~Par A B A' B' -> (exists P, Col P X Y /\ (Col P A B \/ Col P A' B')).
Proof.
    intros.
    assert (HC := all_coplanar).
    apply (cop2_npar__inter); auto.
Qed.

Lemma par_perp__perp : forall A B C D P Q, Par A B C D -> Perp A B P Q ->
  Perp C D P Q.
Proof.
intros A B C D P Q HPar HPer.
assert (HCop := all_coplanar C D P Q).
apply (cop_par_perp__perp A B); assumption.
Qed.

Lemma par_perp2__par : forall A B C D E F G H,
  Par A B C D -> Perp A B E F -> Perp C D G H ->
  Par E F G H.
Proof.
intros A B C D; intros.
apply (cop4_par_perp2__par A B C D); try (apply all_coplanar); assumption.
Qed.

End T13_2D.