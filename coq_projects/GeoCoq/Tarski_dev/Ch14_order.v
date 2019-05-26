Require Export GeoCoq.Tarski_dev.Ch14_prod.

Section Order.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma l14_36_a : forall O E E' A B C,
 Sum O E E' A B C -> Out O A B -> Bet O A C.
Proof.
    intros.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    unfold Out in H0.
    spliter.
    assert(Parallelogram_flat O A C B).
      apply(sum_cong O E E' H A B C HS).
      tauto.
    assert(Parallelogram O A C B).
      right.
      auto.
    induction(eq_dec_points A B).
      subst B.
      unfold Parallelogram_flat in H7.
      spliter.
      assert(O = C \/ Midpoint A O C).
        apply(l7_20 A O C).
          ColR.
        Cong.
      induction H13.
        subst C.
        apply False_ind.
        apply HS.
        apply (double_null_null O E E') in HS; auto.
        tauto.
      unfold Midpoint in H13.
      tauto.
    induction H3.
      apply plg_permut in H8.
      apply plg_permut in H8.
      apply plg_permut in H8.
      assert(Bet A B C).
        apply between_symmetry.
        apply(plg_bet1 B O A C).
          assumption.
        apply between_symmetry.
        assumption.
      apply (outer_transitivity_between O A B C); auto.
    assert(Bet B A C).
      apply between_symmetry.
      apply(plg_bet1 A O B C).
        apply plg_comm2.
        assumption.
      apply between_symmetry.
      assumption.
    apply (outer_transitivity_between2 O B A C); auto.
Qed.

Lemma l14_36_b : forall O E E' A B C,
 Sum O E E' A B C -> Out O A B -> O <> A /\ O <> C /\ A <> C.
Proof.
    intros.
    assert(HH:= l14_36_a O E E' A B C H H0).
    unfold Out in H0.
    spliter.
    split; auto.
    split.
      intro.
      subst C.
      apply between_identity in HH.
      subst A.
      tauto.
    intro.
    subst C.
    assert(HS:= H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(Sum O E E' A O A).
      apply (sum_A_O). assumption.
    assumption.
    assert(B = O).
        apply (sum_uniquenessB O E E' H A B O A); auto.
      contradiction.
Qed.

(** Lemma 14.37 *)
Lemma O_not_positive : forall O E, ~ Ps O E O.
Proof.
    intros.
    unfold Ps.
    unfold Out.
    intuition.
Qed.

Lemma pos_null_neg : forall O E E' A MA,
 Opp O E E' A MA -> Ps O E A \/ O = A \/ Ps O E MA.
Proof.
    intros.
    unfold Opp in H.
    induction (eq_dec_points A O).
      right; left; auto.
    assert(HS:= H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(Parallelogram_flat O MA O A).
      apply(sum_cong O E E' H MA A O HS); tauto.
    unfold Parallelogram_flat in H5.
    spliter.
    assert(HG:=grid_not_par O E E' H).
    spliter.
    assert(A = MA \/ Midpoint O A MA).
      apply(l7_20 O A MA); try ColR.
      Cong.
    induction H16.
      subst MA.
      tauto.
    induction(out_dec O E A).
      left.
      unfold Ps.
      apply l6_6.
      assumption.
    right; right.
    assert(MA <> O).
      intro.
      subst MA.
      apply is_midpoint_id_2 in H16.
      subst A.
      tauto.
    unfold Midpoint in H16.
    spliter.
    unfold Ps.
    unfold Col in H2.
    induction H2.
      unfold Out.
      repeat split; auto.
    induction H2.
      unfold Out.
      repeat split; Col.
      left.
      apply between_symmetry.
      auto.
    apply False_ind.
    apply H17.
    unfold Out.
    repeat split; auto.
    apply between_symmetry in H16.
    assert(HH:= l5_2 MA O A E H18 H16 H2).
    tauto.
Qed.

Lemma sum_pos_pos : forall O E E' A B AB,
  Ps O E A -> Ps O E B -> Sum O E E' A B AB -> Ps O E AB.
Proof.
    intros.
    unfold Ps in *.
    assert(Out O A B).
      apply l6_6 in H0.
      apply(l6_7 O A E B); auto.
    assert(HH:=l14_36_b O E E' A B AB H1 H2).
    spliter.
    assert(HH:=l14_36_a O E E' A B AB H1 H2).
    apply l6_6 in H.
    assert(Out O A AB).
      apply bet_out; auto.
    assert(HP:=l6_7 O E A AB H H6).
    apply l6_6.
    assumption.
Qed.

Lemma prod_pos_pos : forall O E E' A B AB,
 Ps O E A -> Ps O E B -> Prod O E E' A B AB -> Ps O E AB.
Proof.
    intros.
    assert(HP:= H1).
    unfold Prod in H1.
    spliter.
    unfold Ar2 in H1.
    spliter.
    ex_and H2 B'.
    assert(HG:= grid_not_par O E E' H1).
    spliter.
    unfold Ps in H.
    unfold Ps in H0.
    unfold Out in *.
    spliter.
    assert(E' <> A).
      intro.
      subst A.
      contradiction.
    assert(~Col O E' A).
      intro.
      apply H1.
      ColR.
    assert(~Par O E E' A).
      intro.
      induction H20.
        apply H20.
        exists A.
        split; Col.
      spliter.
      contradiction.
    assert(Proj E E' O E' E E').
      apply(pj_col_project); Col.
      left; right.
      repeat split; Col.
    assert(Proj B B' O E' E E').
      apply(pj_col_project); Col.
    assert(Proj O O O E' E E').
      apply(pj_col_project); Col.
      right.
      auto.
    assert(Proj E' A O E E' A).
      apply(pj_col_project); Col.
      left; right.
      repeat split; Col.
    assert(Proj B' AB O E E' A).
      apply(pj_col_project); Col.
    assert(Proj O O O E E' A).
      apply(pj_col_project); Col.
      right.
      auto.
    assert(AB <> O).
      intro.
      subst AB.
      apply prod_null in HP.
      induction HP; contradiction.
    unfold Ps.
    repeat split; auto.
    induction H15.
      assert(Bet O B' E').
        apply(project_preserves_bet O E' E E' O B E O B' E'); auto.
      assert(Bet O AB A).
        apply(project_preserves_bet O E E' A O B' E' O AB A); auto.
      induction H17.
        left.
        apply(between_exchange4 _ _ A); auto.
      apply(l5_3 O AB E A); auto.
    assert(Bet O E' B').
      apply(project_preserves_bet O E' E E' O E B O E' B'); auto.
    assert(Bet O A AB).
      apply(project_preserves_bet O E E' A O E' B' O A AB); auto.
    induction H17.
      assert(Bet O E AB \/ Bet O AB E).
        apply(l5_1 O A E AB); auto.
      tauto.
    right.
    apply (between_exchange4 O E A AB); auto.
Qed.

Lemma pos_not_neg : forall O E A, Ps O E A -> ~Ng O E A.
Proof.
    intros.
    intro.
    unfold Ps in H.
    unfold Ng in H0.
    unfold Out in H.
    spliter.
    induction H4.
      apply H.
      apply (between_equality _ _ E); Between.
    apply H1.
    apply (between_equality _ _ A); Between.
Qed.

Lemma neg_not_pos : forall O E A, Ng O E A -> ~Ps O E A.
Proof.
    intros.
    intro.
    unfold Ps in H0.
    unfold Ng in H.
    unfold Out in H0.
    spliter.
    induction H2.
      apply H0.
      apply (between_equality _ _ E); Between.
    apply H1.
    apply (between_equality _ _ A); Between.
Qed.

Lemma opp_pos_neg : forall O E E' A MA, Ps O E A ->  Opp O E E' A MA -> Ng O E MA.
Proof.
    intros.
    assert(HH:=opp_midpoint O E E' A MA H0).
    unfold Ng.
    unfold Ps in H.
    unfold Out in H.
    unfold Midpoint in HH.
    spliter.
    repeat split; auto.
      intro.
      subst MA.
      apply cong_identity in H2.
      contradiction.
    induction H4.
      apply(outer_transitivity_between MA O A E); Between.
    apply(between_inner_transitivity MA O E A); Between.
Qed.

Lemma opp_neg_pos : forall O E E' A MA, Ng O E A ->  Opp O E E' A MA -> Ps O E MA.
Proof.
    intros.
    assert(HH:=opp_midpoint O E E' A MA H0).
    unfold Ng in H.
    unfold Ps.
    unfold Midpoint in HH.
    spliter.
    apply l6_6.
    unfold Out.
    repeat split; auto.
      intro.
      subst MA.
      apply cong_identity in H2.
      contradiction.
    apply (l5_2 A O E MA); auto.
Qed.

Lemma ltP_ar2 : forall O E E' A B, LtP O E E' A B -> Ar2 O E E' A B A.
Proof.
    intros.
    unfold LtP in H.
    ex_and H D.
    apply diff_ar2 in H.
    unfold Ar2 in H.
    spliter.
    repeat split; auto.
Qed.

Lemma ltP_neq : forall O E E' A B, LtP O E E' A B -> A <> B.
Proof.
    intros.
    assert(HH:=ltP_ar2 O E E' A B H).
    unfold Ar2 in HH.
    spliter.
    unfold LtP in H.
    intro.
    subst B.
    ex_and H OO.
    assert(OO=O).
      apply (diff_uniqueness O E E' A A).
        assumption.
      apply diff_null; Col.
    subst OO.
    unfold Ps in H4.
    unfold Out in H4.
    tauto.
Qed.

Lemma leP_refl : forall O E E' A, LeP O E E' A A.
Proof.
    intros.
    right.
    tauto.
Qed.

Lemma ltP_sum_pos : forall O E E' A B C , Ps O E B -> Sum O E E' A B C -> LtP O E E' A C.
Proof.
    intros.
    unfold LtP.
    exists B.
    split; auto.
    apply sum_diff in H0.
    assumption.
Qed.

Lemma pos_opp_neg : forall O E E' A mA, Ps O E A -> Opp O E E' A mA -> Ng O E mA.
Proof.
    intros.
    assert(Ar2 O E E' mA A O).
      unfold Opp in H0.
      apply sum_ar2; auto.
    unfold Ar2 in H1.
    apply opp_midpoint in H0.
    unfold Midpoint in H0.
    unfold Ps in H.
    unfold Out in H.
    spliter.
    unfold Ng.
    repeat split.
      intro.
      subst mA.
      apply H.
      apply cong_identity in H5.
      assumption.
      auto.
    induction H7.
      apply(outer_transitivity_between mA O A E); Between.
    apply between_symmetry.
    apply(between_exchange3 A E O mA); Between.
Qed.

Lemma diff_pos_diff_neg : forall O E E' A B AmB BmA,
  Diff O E E' A B AmB -> Diff O E E' B A BmA -> Ps O E AmB -> Ng O E BmA.
Proof.
    intros.
    assert(Opp O E E' AmB BmA).
      apply (diff_opp O E E' A B); auto.
    eapply (pos_opp_neg O E E' AmB); auto.
Qed.


Lemma not_pos_and_neg : forall O E A, ~(Ps O E A /\ Ng O E A).
Proof.
    intros.
    intro.
    spliter.
    unfold Ps in H.
    unfold Ng in H0.
    unfold Out in H.
    spliter.
    clean_duplicated_hyps.
    induction H4.
      apply H.
      apply (between_equality _  _ E); Between.
    apply H3.
    apply (between_equality _  _ A); Between.
Qed.

Lemma leP_asym : forall O E E' A B, LeP O E E' A B -> LeP O E E' B A -> A = B.
Proof.
    intros.
    unfold LeP in *.
    induction H; induction H0.
      unfold LtP in *.
      ex_and H BmA.
      ex_and H0 AmB.
      assert(HH:=diff_pos_diff_neg O E E' A B AmB BmA H0 H H2).
      assert(HT:=diff_pos_diff_neg O E E' B A BmA AmB  H H0 H1).
      apply False_ind.
      assert(HN:=not_pos_and_neg O E AmB).
      apply HN.
      split; auto.
      auto.
      auto.
    auto.
Qed.

Lemma leP_trans : forall O E E' A B C, LeP O E E' A B -> LeP O E E' B C -> LeP O E E' A C.
Proof.
    intros.
    unfold LeP in *.
    induction H; induction H0.
      left.
      unfold LtP in *.
      ex_and H dBA.
      ex_and H0 dCB.
      assert(Ar2 O E E' B A dBA).
        apply diff_ar2; auto.
      assert(Ar2 O E E' C B dCB).
        apply diff_ar2; auto.
      unfold Ar2 in *.
      spliter.
      clean_duplicated_hyps.
      assert(HH:= sum_exists O E E' H3 dBA dCB H10 H7).
      ex_and HH dCA.
      exists dCA.
      assert(HH:= sum_diff_diff_b O E E' A B C dBA dCB dCA H H0).
      split.
        apply HH.
        apply sum_comm; auto.
      apply(sum_pos_pos O E E' dBA dCB); auto.
      subst C.
      left; auto.
      subst B.
      left; auto.
    subst C.
    subst B.
    right; auto.
Qed.

(* sum_preserves leP : a <= x /\ b <= y => a + b <= x + y *)

Lemma leP_sum_leP : forall O E E' A B C X Y Z,
  LeP O E E' A X -> LeP O E E' B Y -> Sum O E E' A B C -> Sum O E E' X Y Z ->
  LeP O E E' C Z.
Proof.
    intros.
    unfold LeP in *.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    induction H; induction H0.
      unfold LtP in *.
      ex_and H dXA.
      ex_and H0 dYB.
      assert(HH:= diff_exists O E E' Z C  H3 H7 H10).
      ex_and HH dZC.
      left.
      exists dZC.
      split; auto.
      assert(Sum O E E' dXA dYB dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C X Y Z dXA dYB dZC H1 H2 H H0); auto.
      apply(sum_pos_pos O E E' dXA dYB); auto.
      subst Y.
      left.
      unfold LtP in *.
      ex_and H dXA.
      assert(HH:=diff_exists O E E' Z C H3 H7 H10).
      ex_and HH dZC.
      exists dZC.
      split; auto.
      assert(Sum O E E' dXA O dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C X B Z dXA O dZC); auto.
        apply diff_null; auto.
      assert(dXA = dZC).
        apply(sum_A_O_eq O E E'); auto.
      subst dXA.
      assumption.
      subst X.
      left.
      unfold LtP in *.
      ex_and H0 dYB.
      assert(HH:=diff_exists O E E' Z C H3 H7 H10).
      ex_and HH dZC.
      exists dZC.
      split; auto.
      assert(Sum O E E' O dYB dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C A Y Z O dYB dZC); auto.
        apply diff_null; auto.
      assert(dYB = dZC).
        apply(sum_O_B_eq O E E'); auto.
      subst dYB.
      assumption.
    subst X.
    subst Y.
    right.
    apply(sum_uniqueness O E E' A B); auto.
Qed.

Lemma square_pos : forall O E E' A A2,
  O <> A -> Prod O E E' A A A2 -> Ps O E A2.
Proof.
intros O E E' A A2 HDiff HA2.
assert (HNC : ~ Col O E E') by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (opp_exists O E E' HNC A) as [MA HMA]; Col.
assert (HElim := HMA); apply pos_null_neg in HElim.
elim HElim; clear HElim; intro HElim; [apply prod_pos_pos with E' A A; auto|].
elim HElim; clear HElim; intro HPs;
[intuition|apply prod_pos_pos with E' MA MA; auto].
destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
apply prod_assoc1 with A ME A; auto; [|apply prod_comm]; apply opp_prod; auto.
apply opp_comm; Col.
Qed.

(** Lemma 14.40 states that we have an ordered field. *)

Lemma col_pos_or_neg : forall O E X,
  O <> E -> O <> X -> Col O E X -> Ps O E X \/ Ng O E X.
Proof.
intros O E X HOE HOX HCol.
unfold Ps, Ng, Out.
unfold Col in HCol; intuition.
Qed.

Lemma ltP_neg : forall O E E' A, LtP O E E' A O -> Ng O E A.
Proof.
intros O E E' A HLt.
destruct HLt as [MA [HDiff HPs]].
apply opp_pos_neg with E' MA; auto.
apply diff_O_A_opp; apply sum_diff; apply sum_comm; try apply diff_sum; auto.
unfold Diff, Opp, Sum, Ar2 in HDiff; destruct HDiff as [MB HXMY]; spliter; Col.
Qed.

Lemma ps_le : forall O E E' X,
  ~ Col O E E' -> Bet O X E \/ Bet O E X -> LeP O E E' O X.
Proof.
intros O E E' X HNC HBet.
elim (eq_dec_points O X); intro HOX; [right; auto|left].
exists X; split; [apply diff_A_O; induction HBet; Col|].
assert_diffs; repeat (split; Col).
Qed.

Lemma lt_diff_ps : forall O E E' X Y XMY,
  Col O E X -> Col O E Y -> LtP O E E' Y X -> Diff O E E' X Y XMY -> Ps O E XMY.
Proof.
intros O E E' X Y XMY HCol1 HCol2 HLt HXMY.
destruct HLt as [XMY' [HDiff HPs]].
apply (diff_uniqueness _ _ _ _ _ XMY) in HDiff; treat_equalities; auto.
Qed.

Lemma col_2_le_or_ge : forall O E E' A B,
  ~ Col O E E' -> Col O E A -> Col O E B -> LeP O E E' A B \/ LeP O E E' B A.
Proof.
intros O E E' A B HNC HColA HColB.
assert (HDiff1 : O <> E) by (assert_diffs; auto).
elim (eq_dec_points A B); intro HDiff2; treat_equalities; [left; right; auto|].
destruct (diff_exists O E E' B A) as [D HD]; Col.
assert (HColD : Col O E D) by (apply diff_ar2 in HD; unfold Ar2 in *; spliter; Col).
assert (HDiff3 : O <> D)
  by (intro; treat_equalities; apply diff_null_eq in HD; intuition).
apply col_pos_or_neg in HColD; auto.
elim HColD; clear HColD; intro HNgD; [left; left; exists D; auto|].
destruct (diff_exists O E E' A B) as [MD HMD]; Col.
right; left; exists MD; split; auto; apply opp_neg_pos with E' D; auto.
apply diff_opp with B A; auto.
Qed.

Lemma compatibility_of_sum_with_order : forall O E E' A B C APC BPC,
  LeP O E E' A B -> Sum O E E' A C APC -> Sum O E E' B C BPC ->
  LeP O E E' APC BPC.
Proof.
intros O E E' A B C APC BPC HLe HAPC HBPC.
elim HLe; clear HLe; intro HLe.

  {
  left; destruct HLe as [D [HDiff HPs]]; exists D; split; auto.
  assert (HNC : ~ Col O E E')
    by (apply diff_ar2 in HDiff; unfold Ar2 in *; spliter; Col).
  apply sum_diff; apply diff_sum in HDiff;
  apply sum_assoc_1 with C A B; auto;
  apply sum_comm; auto.
  }

  {
  treat_equalities.
  assert (APC = BPC) by (apply sum_uniqueness with O E E' A C; auto).
  treat_equalities; apply leP_refl.
  }
Qed.

Lemma compatibility_of_prod_with_order : forall O E E' A B AB,
  LeP O E E' O A -> LeP O E E' O B -> Prod O E E' A B AB ->
  LeP O E E' O AB.
Proof.
intros O E E' A B AB HLeA HLeB HAB.
elim HLeA; clear HLeA; intro HLeA;
elim HLeB; clear HLeB; intro HLeB; treat_equalities;
try (apply prod_O_l_eq in HAB); try (apply prod_O_r_eq in HAB);
treat_equalities; try (apply leP_refl).
assert (HNC : ~ Col O E E') by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColAB : Col O E AB) by (unfold Prod, Ar2 in *; spliter; Col).
left; exists AB; split; try (apply diff_A_O); Col.
destruct HLeA as [A' [HDiff1 HPsA]]; destruct HLeB as [B' [HDiff2 HPsB]].
assert (A = A')
  by (apply diff_uniqueness with O E E' A O; auto; apply diff_A_O; Col).
assert (B = B')
  by (apply diff_uniqueness with O E E' B O; auto; apply diff_A_O; Col).
treat_equalities; apply prod_pos_pos with E' A B; auto.
Qed.

Lemma pos_inv_pos : forall O E E' A IA,
  O <> A -> LeP O E E' O A -> Prod O E E' IA A E -> LeP O E E' O IA.
Proof.
intros O E E' A IA HOA HLe HIA.
elim HLe; clear HLe; intro HLe; treat_equalities; [|intuition].
assert (HNC : ~ Col O E E') by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColIA : Col O E IA) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' IA O) as [IA' HIA']; Col.
assert (IA = IA') by (apply diff_uniqueness with O E E' IA O; auto; apply diff_A_O; Col).
treat_equalities; left; exists IA; split; auto; clear HIA'.
destruct HLe as [A' [HDiff HPs1]].
assert (A = A') by (apply diff_uniqueness with O E E' A O; auto; apply diff_A_O; Col).
treat_equalities; clear HDiff; destruct (opp_exists O E E' HNC IA) as [MIA HMIA]; Col.
assert (HElim := HMIA); apply pos_null_neg in HElim.
elim HElim; clear HElim; intro HElim; auto.
elim HElim; clear HElim; intro HPs2; treat_equalities.

  {
  assert (O = E)
    by (apply prod_uniqueness with O E E' O A; auto; apply prod_0_l; Col).
  treat_equalities; intuition.
  }

  {
  destruct (opp_exists O E E' HNC E) as [ME HME]; Col.
  assert (HColME : Col O E ME) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
  assert (HProd1 : Prod O E E' IA ME MIA) by (apply opp_prod; auto).
  assert (HProd2 : Prod O E E' MIA A ME).
    {
    apply prod_assoc1 with ME IA E; auto;
    apply prod_comm; auto; apply prod_1_l; Col.
    }
  assert (HFalse : Ps O E ME) by (apply prod_pos_pos with E' MIA A; auto).
  apply opp_pos_neg with O E E' ME E in HFalse; try apply opp_comm; auto.
  exfalso; apply neg_not_pos in HFalse; apply HFalse.
  assert_diffs; repeat (split; Between).
  }
Qed.

Unset Regular Subst Tactic.

Lemma le_pos_prod_le : forall O E E' A B C AC BC,
  LeP O E E' A B -> LeP O E E' O C ->
  Prod O E E' A C AC -> Prod O E E' B C BC ->
  LeP O E E' AC BC.
Proof.
intros O E E' A B C AC BC HALeB HPsC HAC HBC.
assert (HNC : ~ Col O E E') by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColC : Col O E C) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColAC : Col O E AC) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColBC : Col O E BC) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' BC AC) as [BCMAC HBCMAC]; Col.
apply compatibility_of_sum_with_order with O BCMAC AC;
try apply sum_O_B; try (apply sum_comm; try apply diff_sum); Col.
destruct (diff_exists O E E' B A) as [BMA HBMA]; Col.
assert (HColBMA : Col O E BMA)
  by (apply diff_ar2 in HBMA; unfold Ar2 in *; spliter; Col).
destruct (prod_exists O E E' HNC BMA C) as [BCMAC' HBCMAC']; Col.
assert (H : Diff O E E' BC AC BCMAC').
  {
  apply sum_diff; apply diff_sum in HBMA;
  apply distr_r with A BMA C B; auto.
  }
assert (BCMAC = BCMAC') by (apply diff_uniqueness with O E E' BC AC; auto).
clear H; treat_equalities;
apply compatibility_of_prod_with_order with BMA C; auto.
destruct (opp_exists O E E' HNC A) as [MA HMA]; Col.
assert (HColMA : Col O E MA) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
apply compatibility_of_sum_with_order with A B MA; auto;
try (apply diff_sum; apply diff_O_A; Col).
apply diff_O_A in HMA; Col; apply diff_sum in HBMA; apply diff_sum in HMA.
apply sum_assoc_1 with BMA A O; auto; try apply sum_A_O; Col.
apply sum_comm; auto.
Qed.

Lemma bet_lt12_le23 : forall O E E' A B C,
  Bet A B C -> LtP O E E' A B -> LeP O E E' B C.
Proof.
intros O E E' A B C HBet HLt.
assert (HNC : ~ Col O E E')
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
assert (HDiff1 : O <> E) by (assert_diffs; auto).
elim (eq_dec_points B C); intro HDiff2; [right; auto|].
assert (HDiff3 : A <> B) by (apply ltP_neq with O E E'; auto).
assert (HColA : Col O E A)
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
assert (HColB : Col O E B)
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
assert (HColC : Col O E C) by (assert_diffs; assert_cols; ColR).
destruct (diff_exists O E E' C B) as [CMB HCMB]; Col.
elim (eq_dec_points O A); intro HDiff4; elim (eq_dec_points O B); intro HDiff5;
elim (eq_dec_points O C); intro HDiff6; treat_equalities;
[intuition|intuition|intuition| |right; auto| | |].

  {
  destruct HLt as [B' [HB' HPs]].
  assert (B = B') by (apply diff_uniqueness with O E E' B O; auto; apply diff_A_O; Col).
  treat_equalities; left; exists CMB; split; auto.
  split; try (intro; treat_equalities; apply HDiff2; apply eq_sym;
              apply diff_null_eq with CMB E E'; auto).
  split; auto; apply diff_sum in HCMB; apply sum_cong in HCMB;
  Col; apply plgf_bet in HCMB.
  do 3 (try (elim HCMB; clear HCMB; intro HCMB;
             try destruct HCMB as [HBet1 HBet2])).

    {
    exfalso; apply HDiff5; apply between_equality with C; Between.
    }

    {
    exfalso; apply HDiff2; apply between_equality with O; Between.
    }

    {
    destruct HPs as [H [H' HElim]]; clear H; clear H'.
    elim HElim; clear HElim; intro HElim; [eBetween|].
    elim (l5_3 O CMB E B); Between.
    }

    {
    destruct HPs as [H [H' HElim]]; clear H; clear H'.
    elim HElim; clear HElim; intro HElim; [|eBetween].
    elim (l5_2 O B CMB E); eBetween.
    }
  }

  {
  apply ltP_neg in HLt; apply ps_le; Col.
  unfold Ng in *; spliter.
  elim (l5_2 A O C E); Between.
  }

  {
  rename CMB into MB.
  left; exists MB; split; auto; apply opp_neg_pos with E' B;
  try apply diff_O_A_opp; auto.
  apply col_pos_or_neg in HColB; try (intro; treat_equalities; Col).
  elim HColB; clear HColB; intro HPsB; auto; exfalso.
  apply col_pos_or_neg in HColA; try (intro; treat_equalities; Col).
  elim HColA; clear HColA; [intro HPsA|intro HNgA].

    {
    destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
    elim (eq_dec_points A BMA); intro HDiff6; treat_equalities;
    [apply l14_36_a in HBMA; try apply out_trivial; auto;
     apply HDiff3; apply between_equality with O; Between|].
    apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
    do 3 (try (elim HBMA; clear HBMA; intro HBMA;
               try destruct HBMA as [HBet1 HBet2])).

      {
      apply HDiff5; apply between_equality with A; Between.
      }

      {
      apply not_pos_and_neg with O E BMA; split; auto.
      split; try (intro; treat_equalities; apply O_not_positive with BMA E; auto).
      split; auto; destruct HPsB as [H [H' HElim]]; clear H; clear H'.
      elim HElim; clear HElim; intro HElim; eBetween.
      }

      {
      apply HDiff3; apply between_equality with O; Between.
      apply between_symmetry; apply outer_transitivity_between2 with BMA; auto.
      }

      {
      apply HDiff3; apply between_equality with O; Between.
      apply outer_transitivity_between2 with BMA; Between.
      }
    }

    {
    apply not_pos_and_neg with O E A; split; auto.
    do 2 (split; auto); destruct HPsB as [H [H' HElim]]; clear H; clear H'.
    elim HElim; clear HElim; intro HBet'; [|eBetween].
    elim (l5_2 O B A E); eBetween.
    }
  }

  {
  left; exists CMB; split; auto; apply diff_sum in HCMB; assert (HCMB' := HCMB).
  split; try (intro; treat_equalities; apply HDiff2;
              apply sum_uniqueness with CMB E E' B CMB; auto; apply sum_A_O; Col).
  split; auto; apply sum_cong in HCMB; Col; apply plgf_bet in HCMB.
  apply col_pos_or_neg in HColA; try (intro; treat_equalities; Col).
  apply col_pos_or_neg in HColB; try (intro; treat_equalities; Col).
  elim HColA; clear HColA; [intro HPsA|intro HNgA].

    {
    do 3 (try (elim HCMB; clear HCMB; intro HCMB;
               try destruct HCMB as [HBet1 HBet2])).

      {
      elim HColB; clear HColB; [intro HPsB|intro HNgB].

        {
        destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
        destruct HPsB as [H [H' HElim2]]; clear H; clear H'.
        elim HElim1; clear HElim1; intro HBet3;
        elim HElim2; clear HElim2; intro HBet4.

          {
          elim (l5_3 O A B E); Between; intro HBet5.

            {
            assert (HBet6 : Bet O B C) by eBetween.
            exfalso; apply HDiff5; apply between_equality with C; Between.
            }

            {
            destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
            elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
            [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
             apply HDiff3; apply between_equality with O; Between|].
            apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
            do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                       try destruct HBMA as [HBet6 HBet7])).

              {
              exfalso; apply HDiff5; apply between_equality with A; Between.
              }

              {
              destruct HPsBMA as [HDiff8 [H HElim]]; clear H.
              elim HElim; clear HElim; intro HBet8.

                {
                assert (HBet9 : Bet E O B)
                  by (apply outer_transitivity_between2 with BMA; Between).
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }

                {
                assert (HBet9 : Bet E O B) by eBetween.
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }
              }

              {
              assert (HBet8 : Bet O A B)
                by (apply outer_transitivity_between2 with BMA; Between).
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }

              {
              assert (HBet8 : Bet O A B) by eBetween.
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }
            }
          }

          {
          assert (HBet5 : Bet O B C) by eBetween.
          exfalso; apply HDiff5; apply between_equality with C; Between.
          }

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
           apply HDiff3; apply between_equality with O; eBetween|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet5 HBet6])).

            {
            assert (HBet7 : Bet O B A) by eBetween.
            exfalso; apply HDiff5; apply between_equality with A; Between.
            }

            {
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H';
            elim HElim; clear HElim; intro HBet7.

              {
              elim (l5_3 O B BMA E); Between; intro HBet8; exfalso;
              [apply HDiff5; apply between_equality with BMA|
               apply HDiff8; apply between_equality with B]; Between.
              }

              {
              assert (HBet8 : Bet O B BMA) by eBetween.
              exfalso; apply HDiff5; apply between_equality with BMA; Between.
              }
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }
          }

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
           apply HDiff3; apply between_equality with O; eBetween|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet5 HBet6])).

            {
            assert (HBet7 : Bet A O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with A; Between.
            }

            {
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H';
            elim HElim; clear HElim; intro HBet7.

              {
              assert (HBet8 : Bet BMA O E) by eBetween.
              exfalso; apply HDiff8; apply between_equality with E; Between.
              }

              {
              assert (HBet8 : Bet BMA O E) by eBetween.
              exfalso; apply HDiff1; apply between_equality with BMA; Between.
              }
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet B A C) by eBetween.
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet B A C) by eBetween.
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }
          }
        }

        {
        exfalso; apply neg_not_pos in HNgB; apply HNgB; clear HNgB.
        do 2 (split; auto).
        destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
        elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
        [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
         apply HDiff3; apply between_equality with O; eBetween|].
        apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
        do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                   try destruct HBMA as [HBet3 HBet4])).

          {
          assert (HBet5 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet6;
          elim HElim2; clear HElim2; intro HBet7.

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          assert (HBet5 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet6;
          elim HElim2; clear HElim2; intro HBet7.

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet5; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet5; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }
        }
      }

      {
      elim HColB; clear HColB; [intro HPsB|intro HNgB].

        {
        destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
        destruct HPsB as [H [H' HElim2]]; clear H; clear H'.
        elim HElim1; clear HElim1; intro HBet3;
        elim HElim2; clear HElim2; intro HBet4.

          {
          elim (l5_3 O A B E); Between; intro HBet5.

            {
            assert (HBet6 : Bet O B C) by eBetween.
            exfalso; apply HDiff2; apply between_equality with O; Between.
            }

            {
            destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
            elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
            [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
             apply HDiff3; apply between_equality with O; Between|].
            apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
            do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                       try destruct HBMA as [HBet6 HBet7])).

              {
              exfalso; apply HDiff5; apply between_equality with A; Between.
              }

              {
              destruct HPsBMA as [HDiff8 [H HElim]]; clear H.
              elim HElim; clear HElim; intro HBet8.

                {
                assert (HBet9 : Bet E O B)
                  by (apply outer_transitivity_between2 with BMA; Between).
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }

                {
                assert (HBet9 : Bet E O B) by eBetween.
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }
              }

              {
              assert (HBet8 : Bet O A B)
                by (apply outer_transitivity_between2 with BMA; Between).
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }

              {
              assert (HBet8 : Bet O A B) by eBetween.
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }
            }
          }

          {
          assert (HBet5 : Bet O B C) by eBetween.
          exfalso; apply HDiff2; apply between_equality with O; Between.
          }

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
           apply HDiff3; apply between_equality with O; eBetween|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet5 HBet6])).

            {
            assert (HBet7 : Bet O B A) by eBetween.
            exfalso; apply HDiff5; apply between_equality with A; Between.
            }

            {
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H';
            elim HElim; clear HElim; intro HBet7.

              {
              elim (l5_3 O B BMA E); Between; intro HBet8; exfalso;
              [apply HDiff5; apply between_equality with BMA|
               apply HDiff8; apply between_equality with B]; Between.
              }

              {
              assert (HBet8 : Bet O B BMA) by eBetween.
              exfalso; apply HDiff5; apply between_equality with BMA; Between.
              }
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }
          }

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
           apply HDiff3; apply between_equality with O; eBetween|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet5 HBet6])).

            {
            assert (HBet7 : Bet A O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with A; Between.
            }

            {
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H';
            elim HElim; clear HElim; intro HBet7.

              {
              assert (HBet8 : Bet BMA O E) by eBetween.
              exfalso; apply HDiff8; apply between_equality with E; Between.
              }

              {
              assert (HBet8 : Bet BMA O E) by eBetween.
              exfalso; apply HDiff1; apply between_equality with BMA; Between.
              }
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet B A C) by eBetween.
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet B A C) by eBetween.
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }
          }
        }

        {
        exfalso; apply neg_not_pos in HNgB; apply HNgB; clear HNgB.
        do 2 (split; auto).
        destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
        elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
        [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
         apply HDiff3; apply between_equality with O; eBetween|].
        apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
        do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                   try destruct HBMA as [HBet3 HBet4])).

          {
          assert (HBet5 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet6;
          elim HElim2; clear HElim2; intro HBet7.

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          assert (HBet5 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet6;
          elim HElim2; clear HElim2; intro HBet7.

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet8 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet5; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet5; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }
        }
      }

      {
      elim HColB; clear HColB; [intro HPsB|intro HNgB].

        {
        destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
        destruct HPsB as [H [H' HElim2]]; clear H; clear H'.
        elim HElim1; clear HElim1; intro HBet3;
        elim HElim2; clear HElim2; intro HBet4.

          {
          elim (l5_3 O A B E); Between; intro HBet5.

            {
            left; eBetween.
            }

            {
            destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
            elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
            [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
             apply HDiff3; apply between_equality with O; Between|].
            apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
            do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                       try destruct HBMA as [HBet6 HBet7])).

              {
              exfalso; apply HDiff5; apply between_equality with A; Between.
              }

              {
              destruct HPsBMA as [HDiff8 [H HElim]]; clear H.
              elim HElim; clear HElim; intro HBet8.

                {
                assert (HBet9 : Bet E O B)
                  by (apply outer_transitivity_between2 with BMA; Between).
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }

                {
                assert (HBet9 : Bet E O B) by eBetween.
                exfalso; apply HDiff5; apply between_equality with E; Between.
                }
              }

              {
              assert (HBet8 : Bet O A B)
                by (apply outer_transitivity_between2 with BMA; Between).
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }

              {
              assert (HBet8 : Bet O A B) by eBetween.
              exfalso; apply HDiff3; apply between_equality with O; Between.
              }
            }
          }

          {
          elim (l5_3 O CMB E B); Between.
          }

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
           apply HDiff3; apply between_equality with O; eBetween|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet5 HBet6])).

            {
            assert (HBet7 : Bet O B A) by eBetween.
            exfalso; apply HDiff5; apply between_equality with A; Between.
            }

            {
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H';
            elim HElim; clear HElim; intro HBet7.

              {
              elim (l5_3 O B BMA E); Between; intro HBet8; exfalso;
              [apply HDiff5; apply between_equality with BMA|
               apply HDiff8; apply between_equality with B]; Between.
              }

              {
              assert (HBet8 : Bet O B BMA) by eBetween.
              exfalso; apply HDiff5; apply between_equality with BMA; Between.
              }
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }

            {
            assert (HBet7 : Bet O A B) by eBetween.
            assert (HBet8 : Bet O B A) by eBetween.
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }
          }

          {
          elim (l5_3 O CMB E B); Between.
          }
        }

        {
        assert (HBet3 : Bet B O A).
          {
          destruct HPsA as [H'' [H' H]]; unfold Ng in *; spliter;
          induction H; eBetween.
          }
        exfalso; apply neg_not_pos in HNgB; apply HNgB; clear HNgB.
        do 2 (split; auto).
        destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
        elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
        [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
         apply HDiff4; apply between_equality with B; eBetween|].
        apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
        do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                   try destruct HBMA as [HBet4 HBet5])).

          {
          assert (HBet6 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet7;
          elim HElim2; clear HElim2; intro HBet8.

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          assert (HBet6 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet7;
          elim HElim2; clear HElim2; intro HBet8.

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet6; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet6; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }
        }
      }

      {
      elim HColB; clear HColB; [intro HPsB|intro HNgB].

        {
        destruct HPsB as [H [H' HElim]]; clear H; clear H'.
        elim HElim; clear HElim; intro HBet3.

          {
          elim (l5_2 O B CMB E); eBetween.
          }

          {
          right; eBetween.
          }
        }

        {
        assert (HBet3 : Bet B O A).
          {
          destruct HPsA as [H'' [H' H]]; unfold Ng in *; spliter;
          induction H; eBetween.
          }
        exfalso; apply neg_not_pos in HNgB; apply HNgB; clear HNgB.
        do 2 (split; auto).
        destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
        elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
        [apply l14_36_a in HBMA; try apply out_trivial; auto; exfalso;
         apply HDiff4; apply between_equality with B; eBetween|].
        apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
        do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                   try destruct HBMA as [HBet4 HBet5])).

          {
          assert (HBet6 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet7;
          elim HElim2; clear HElim2; intro HBet8.

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          assert (HBet6 : Bet BMA O A) by eBetween.
          destruct HPsA as [H [H' HElim1]]; clear H; clear H'.
          destruct HPsBMA as [HDiff8 [H' HElim2]]; clear H'.
          elim HElim1; clear HElim1; intro HBet7;
          elim HElim2; clear HElim2; intro HBet8.

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff8; apply between_equality with E; Between.
            }

            {
            assert (HBet9 : Bet BMA O E) by eBetween.
            exfalso; apply HDiff1; apply between_equality with BMA; Between.
            }
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet6; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }

          {
          destruct HPsA as [H [H' HElim]]; clear H; clear H'.
          elim HElim; clear HElim; intro HBet6; [|eBetween].
          elim (l5_2 O A B E); eBetween.
          }
        }
      }
    }

    {
    elim HColB; clear HColB; [intro HPsB|intro HNgB].

      {
      do 3 (try (elim HCMB; clear HCMB; intro HCMB;
               try destruct HCMB as [HBet1 HBet2])).

        {
        destruct HNgA as [H [H' HBet3]]; clear H; clear H'.
        destruct HPsB as [H [H' HElim]]; clear H; clear H'.
        elim HElim; clear HElim; intro HBet4;
        assert (HBet5 : Bet O B C) by eBetween;
        exfalso; apply HDiff5; apply between_equality with C; Between.
        }

        {
        destruct HNgA as [H [H' HBet3]]; clear H; clear H'.
        destruct HPsB as [H [H' HElim]]; clear H; clear H'.
        elim HElim; clear HElim; intro HBet4;
        assert (HBet5 : Bet O B C) by eBetween;
        exfalso; apply HDiff2; apply between_equality with O; Between.
        }

        {
        destruct HPsB as [H [H' HElim]]; clear H; clear H'.
        elim HElim; clear HElim; intro HBet4; [left; eBetween|].
        elim (l5_3 O CMB E B); eBetween.
        }

        {
        destruct HPsB as [H [H' HElim]]; clear H; clear H'.
        elim HElim; clear HElim; intro HBet4; [|right; eBetween].
        elim (l5_2 O B CMB E); eBetween.
        }
      }

      {
      do 3 (try (elim HCMB; clear HCMB; intro HCMB;
               try destruct HCMB as [HBet1 HBet2])).

        {
        destruct HNgB as [H [H' HBet3]]; clear H; clear H'.
        elim (l5_2 B O C E); Between; [|right; eBetween]; intro HBet4.
        elim (l5_2 O C CMB E); eBetween.
        }

        {
        destruct HNgB as [H [H' HBet3]]; clear H; clear H'.
        assert (HBet4 : Bet E O C) by eBetween.
        elim (l5_2 C O CMB E); Between.
        }

        {
        destruct HNgA as [H [H' HBet3]]; clear H; clear H'.
        destruct HNgB as [H [H' HBet4]]; clear H; clear H'.
        elim (l5_2 E O A B); Between; intro HBet5.

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [destruct HPsBMA as [H [H' HElim]]; clear H; clear H';
           elim HElim; clear HElim; intro HBet6; exfalso;
           [apply HDiff4; apply between_equality with E|
            apply HDiff1; apply between_equality with A]; Between|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet6 HBet7])).

            {
            exfalso; apply HDiff4; apply between_equality with B; Between.
            }

            {
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }

            {
            assert (HBet8 : Bet E O BMA) by eBetween.
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H'.
            exfalso; elim HElim; clear HElim; intro HBet9;
            [apply HDiff8; apply between_equality with E|
             apply HDiff1; apply between_equality with BMA]; Between.
            }

            {
            assert (HBet8 : Bet E O BMA) by eBetween.
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H'.
            exfalso; elim HElim; clear HElim; intro HBet9;
            [apply HDiff8; apply between_equality with E|
             apply HDiff1; apply between_equality with BMA]; Between.
            }
          }

          {
          assert (HBet6 : Bet O B C).
            {
            elim (eq_dec_points B CMB); intro HDiff7; treat_equalities; [|eBetween].
            apply l14_36_a in HCMB'; try apply out_trivial; auto.
            }
          elim (l5_2 O B A C); Between; intro HBet7.

            {
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }

            {
            exfalso; apply HDiff2; apply between_equality with A; Between.
            }
          }
        }

        {
        destruct HNgA as [H [H' HBet3]]; clear H; clear H'.
        destruct HNgB as [H [H' HBet4]]; clear H; clear H'.
        elim (l5_2 E O A B); Between; intro HBet5.

          {
          destruct HLt as [BMA [HBMA HPsBMA]]; apply diff_sum in HBMA.
          elim (eq_dec_points A BMA); intro HDiff7; treat_equalities;
          [destruct HPsBMA as [H [H' HElim]]; clear H; clear H';
           elim HElim; clear HElim; intro HBet6; exfalso;
           [apply HDiff4; apply between_equality with E|
            apply HDiff1; apply between_equality with A]; Between|].
          apply sum_cong in HBMA; Col; apply plgf_bet in HBMA.
          do 3 (try (elim HBMA; clear HBMA; intro HBMA;
                     try destruct HBMA as [HBet6 HBet7])).

            {
            exfalso; apply HDiff4; apply between_equality with B; Between.
            }

            {
            exfalso; apply HDiff3; apply between_equality with O; Between.
            }

            {
            assert (HBet8 : Bet E O BMA) by eBetween.
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H'.
            exfalso; elim HElim; clear HElim; intro HBet9;
            [apply HDiff8; apply between_equality with E|
             apply HDiff1; apply between_equality with BMA]; Between.
            }

            {
            assert (HBet8 : Bet E O BMA) by eBetween.
            destruct HPsBMA as [HDiff8 [H' HElim]]; clear H'.
            exfalso; elim HElim; clear HElim; intro HBet9;
            [apply HDiff8; apply between_equality with E|
             apply HDiff1; apply between_equality with BMA]; Between.
            }
          }

          {
          assert (HBet6 : Bet O B C).
            {
            elim (eq_dec_points B CMB); intro HDiff7; treat_equalities; [|eBetween].
            apply l14_36_a in HCMB'; try apply out_trivial; auto.
            }

          elim (l5_2 O B A C); Between; intro HBet7.

            {
            exfalso; apply HDiff3; apply between_equality with C; Between.
            }

            {
            exfalso; apply HDiff2; apply between_equality with A; Between.
            }
          }
        }
      }
    }
  }
Qed.

Lemma bet_lt12_le13 : forall O E E' A B C,
  Bet A B C -> LtP O E E' A B -> LeP O E E' A C.
Proof.
intros O E E' A B C HBet HLt.
apply leP_trans with B; [left; auto|].
apply bet_lt12_le23 with A; auto.
Qed.

Lemma bet_lt21_le32 : forall O E E' A B C,
  Bet A B C -> LtP O E E' B A -> LeP O E E' C B.
Proof.
intros O E E' A B C HBet HLt.
assert (HNC : ~ Col O E E')
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
elim (eq_dec_points B C); intro HDiff2; [right; auto|].
assert (HDiff3 : B <> A) by (apply ltP_neq with O E E'; auto).
assert (HColA : Col O E A)
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
assert (HColB : Col O E B)
  by (destruct HLt as [D [H H']]; apply diff_ar2 in H; unfold Ar2 in *; spliter; Col).
assert (HColC : Col O E C) by (assert_diffs; assert_cols; ColR).
destruct (diff_exists O E E' B C) as [BMC HBMC]; Col.
destruct (opp_exists O E E' HNC A) as [MA HMA]; Col.
destruct (opp_exists O E E' HNC B) as [MB HMB]; Col.
destruct (opp_exists O E E' HNC C) as [MC HMC]; Col.
assert (HColMA : Col O E MA) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColMB : Col O E MB) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColMC : Col O E MC) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColBMC : Col O E BMC)
  by (apply diff_ar2 in HBMC; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' A B) as [AMB HAMB]; Col.
assert (HColAMB : Col O E AMB)
  by (apply diff_ar2 in HAMB; unfold Ar2 in *; spliter; Col).
destruct (diff_exists O E E' MA MB) as [MAMMB HMAMMB]; Col.
assert (HColMAMMB : Col O E MAMMB)
  by (apply diff_ar2 in HMAMMB; unfold Ar2 in *; spliter; Col).
assert (HOppAMB : Opp O E E' AMB MAMMB).
  {
  apply sum_opp; apply sum_assoc_1 with MB A B;
  [| |apply sum_comm; Col; apply diff_sum; apply diff_O_A; Col].

    {
    apply diff_sum in HAMB.
    apply sum_assoc_2 with B AMB O; auto.
    apply sum_O_B; Col.
    }

    {
    apply diff_sum in HMAMMB.
    apply sum_assoc_2 with MA B O; auto; try apply sum_O_B; Col;
    [apply diff_sum; apply diff_O_A; Col|].
    apply sum_assoc_1 with MAMMB MB O; auto; [apply sum_comm; auto|].
    apply sum_A_O; Col.
    }
  }
destruct (diff_exists O E E' MB MA) as [MBMMA HMBMMA]; Col.
assert (HColMBMMA : Col O E MBMMA)
  by (apply diff_ar2 in HMBMMA; unfold Ar2 in *; spliter; Col).
assert (HOppMAMMB : Opp O E E' MAMMB MBMMA) by (apply diff_opp with MA MB; auto).
assert (AMB = MBMMA)
  by (apply opp_uniqueness with O E E' MAMMB; auto; apply opp_comm; auto).
treat_equalities.
assert (HBet' : Bet MA MB MC)
  by (apply l7_15 with A B C O; auto; try apply opp_midpoint with E E'; auto).
destruct (diff_exists O E E' MB MC) as [MBMMC HMBMMC]; Col.
assert (HColMAMMC : Col O E MBMMC)
  by (apply diff_ar2 in HMBMMC; unfold Ar2 in *; spliter; Col).
assert (HOppAMC : Opp O E E' BMC MBMMC).
  {
  apply sum_opp; apply sum_assoc_1 with MC B C;
  [| |apply sum_comm; Col; apply diff_sum; apply diff_O_A; Col].

    {
    apply diff_sum in HBMC.
    apply sum_assoc_2 with C BMC O; auto.
    apply sum_O_B; Col.
    }

    {
    apply diff_sum in HMBMMC.
    apply sum_assoc_2 with MB C O; auto; try apply sum_O_B; Col;
    [apply diff_sum; apply diff_O_A; Col|].
    apply sum_assoc_1 with MBMMC MC O; auto; [apply sum_comm; auto|].
    apply sum_A_O; Col.
    }
  }
destruct (diff_exists O E E' MC MB) as [MCMMB HMCMMB]; Col.
assert (HOppMBMMC : Opp O E E' MBMMC MCMMB) by (apply diff_opp with MB MC; auto).
assert (BMC = MCMMB)
  by (apply opp_uniqueness with O E E' MBMMC; auto; apply opp_comm; auto).
treat_equalities.
assert (HLt' : LtP O E E' MA MB)
  by (exists AMB; split; auto; apply lt_diff_ps with E' A B; auto).
assert (HLe : LeP O E E' MB MC) by (apply bet_lt12_le23 with MA; auto).
left; exists BMC; split; auto; apply lt_diff_ps with E' MC MB; auto.
elim HLe; clear HLe; intro HFalse; auto; treat_equalities.
assert (O = BMC)
  by (apply diff_uniqueness with O E E' MB MB; auto; apply diff_null; Col).
treat_equalities; apply diff_null_eq in HBMC; treat_equalities; intuition.
Qed.

Lemma bet_lt21_le31 : forall O E E' A B C,
  Bet A B C -> LtP O E E' B A -> LeP O E E' C A.
Proof.
intros O E E' A B C HBet HLt.
apply leP_trans with B; [|left; auto].
apply bet_lt21_le32 with A; auto.
Qed.

Lemma opp_2_le_le : forall O E E' A MA B MB,
  Opp O E E' A MA -> Opp O E E' B MB -> LeP O E E' A B -> LeP O E E' MB MA.
Proof.
intros O E E' A MA B MB HOppA HOppB HLe.
assert (HNC : ~ Col O E E') by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColMA : Col O E MA) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HColMB : Col O E MB) by (unfold Opp, Sum, Ar2 in *; spliter; Col).
destruct (sum_exists O E E' HNC MA MB) as [MAMB HMAMB]; Col.
assert (HMA : Sum O E E' B MAMB MA)
  by (apply sum_assoc_2 with MB MA O; apply sum_comm; Col; apply sum_A_O; auto).
assert (HMB : Sum O E E' A MAMB MB)
  by (apply sum_assoc_2 with MA MB O; try apply sum_O_B; auto; apply sum_comm; auto).
eapply compatibility_of_sum_with_order in HLe; [|apply HMB|apply HMA]; auto.
Qed.

Lemma diff_2_le_le : forall O E E' A B C AMC BMC,
  Diff O E E' A C AMC -> Diff O E E' B C BMC -> LeP O E E' A B ->
  LeP O E E' AMC BMC.
intros O E E' A B C AMC BMC HAMC HBMC HLe.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HAMC; unfold Ar2 in *; spliter; Col).
assert (HColC : Col O E C)
  by (apply diff_ar2 in HAMC; unfold Ar2 in *; spliter; Col).
assert (HColAMC : Col O E AMC)
  by (apply diff_ar2 in HAMC; unfold Ar2 in *; spliter; Col).
assert (HColBMC : Col O E BMC)
  by (apply diff_ar2 in HBMC; unfold Ar2 in *; spliter; Col).
destruct (opp_exists O E E' HNC C) as [MC HMC]; Col.
assert (HAMC' : Sum O E E' A MC AMC).
  {
  apply diff_sum in HAMC; apply sum_assoc_1 with AMC C O;
  apply sum_comm; auto; apply sum_O_B; Col.
  }
assert (HBMC' : Sum O E E' B MC BMC).
  {
  apply diff_sum in HBMC; apply sum_assoc_1 with BMC C O;
  apply sum_comm; auto; apply sum_O_B; Col.
  }
apply compatibility_of_sum_with_order with A B MC; auto.
Qed.

End Order.
