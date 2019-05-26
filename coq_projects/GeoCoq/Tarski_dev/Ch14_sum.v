Require Export GeoCoq.Tarski_dev.Ch13_6_Desargues_Hessenberg.

Section T14_sum.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma Pj_exists : forall A B C,
 exists D, Pj A B C D.
Proof.
    intros.
    unfold Pj in *.
    elim (eq_dec_points A B);intro.
      subst.
      exists C.
      tauto.
    assert (T:=parallel_existence A B C H).
    decompose [and ex] T;clear T.
    exists x0.
    induction (eq_dec_points C x0).
      tauto.
    eauto using par_col2_par with col.
Qed.

Lemma sum_to_sump : forall O E E' A B C, Sum O E E' A B C -> Sump O E E' A B C.
Proof.
    intros.
    unfold Sum in H.
    unfold Ar2 in H.
    spliter.
    repeat split; Col.
    ex_and H0 A'.
    ex_and H4 C'.
    exists A'.
    exists C'.
    assert(O <> E /\ O <> E').
      repeat split; intro; subst O; apply H; Col.
    spliter.
    assert(HH:=parallel_existence1 O E A' H8).
    ex_and HH P'.
    exists P'.
    assert( E <> E').
      intro.
      subst E'.
      apply H.
      Col.
    repeat split; Col.
      intro.
      induction H12.
        apply H12.
        exists E'.
        split; Col.
      spliter.
      contradiction.
      unfold Pj in H0.
      induction H0.
        left.
        apply par_symmetry.
        assumption.
      right.
      auto.
      apply par_distincts in H10.
      spliter.
      auto.
      intro.
      assert(Par O E O E').
        apply (par_trans _ _ A' P'); auto.
      induction H13.
        apply H13.
        exists O.
        split; Col.
      spliter.
      apply H.
      Col.
      unfold Pj in H5.
      induction H5.
        assert(Par A' C' A' P').
          apply (par_trans _ _ O E).
            apply par_symmetry.
            auto.
          auto.
        induction H12.
          apply False_ind.
          apply H12.
          exists A'.
          split; Col.
        spliter.
        Col.
      subst C'.
      Col.
      unfold Pj in H6.
      induction H6.
        left.
        apply par_symmetry.
        auto.
      right.
      auto.
      intro.
      induction H12.
        apply H12.
        exists E.
        split; Col.
      spliter.
      contradiction.
    unfold Pj in H7.
    induction H7.
      left.
      apply par_symmetry.
      apply par_left_comm.
      auto.
    tauto.
Qed.


Lemma sump_to_sum : forall O E E' A B C, Sump O E E' A B C -> Sum O E E' A B C.
Proof.
    intros.
    unfold Sump in H.
    spliter.
    ex_and H1 A'.
    ex_and H2 C'.
    ex_and H1 P'.
    unfold Sum.
    split.
      repeat split; Col.
        intro.
        unfold Proj in H1.
        spliter.
        apply H7.
        right.
        repeat split; Col.
      unfold Proj in H4.
      spliter.
      Col.
    exists A'.
    exists C'.
    unfold Pj.
    repeat split.
      unfold Proj in H1.
      spliter.
      induction H8.
        left.
        apply par_symmetry.
        auto.
      tauto.
      unfold Proj in H1.
      tauto.
      induction(eq_dec_points A' C').
        tauto.
      left.
      unfold Proj in H3.
      spliter.
      apply (par_col_par _  _ _ P'); Col.
      unfold Proj in H3.
      spliter.
      induction H8.
        left.
        apply par_symmetry.
        auto.
      tauto.
    unfold Proj in H4.
    spliter.
    induction H8.
      left.
      apply par_symmetry.
      apply par_right_comm.
      auto.
    tauto.
Qed.

(* a inclure dans project.v *)

Lemma project_col_project : forall A B C P P' X Y,
  A <> C -> Col A B C ->
  Proj P P' A B X Y ->
  Proj P P' A C X Y.
Proof with finish.
    intros.
    unfold Proj in *.
    spliter.
    repeat split; auto.
      intro.
      apply H3.
      eapply (par_col_par_2 _ C); Col; Par.
    (*perm_apply (par_col_par X Y A C).*)
    ColR.
Qed.

Lemma project_trivial : forall P A B X Y,
  A <> B -> X <> Y ->
  Col A B P -> ~ Par A B X Y ->
  Proj P P A B X Y.
Proof.
    intros.
    unfold Proj.
    repeat split; Col.
Qed.

Lemma pj_col_project : forall P P' A B X Y,
 A <> B -> X <> Y ->
 Col P' A B ->
 ~ Par A B X Y ->
 Pj X Y P P' ->
 Proj P P' A B X Y.
Proof.
    intros.
    unfold Pj in H3.
    induction H3.
      unfold Proj.
      repeat split; Col.
      left.
      apply par_symmetry.
      assumption.
    subst P'.
    apply project_trivial; Col.
Qed.

(** Lemma 14.6 *)

Section Grid.

Variable O E E' : Tpoint.

Variable grid_ok : ~ Col O E E'.

Lemma sum_exists : forall A B,
 Col O E A -> Col O E B ->
 exists C, Sum O E E' A B C.
Proof.
    intros.
    assert(NC:= grid_ok).
    assert(O <> E).
      intro.
      subst E.
      apply NC.
      Col.
    assert(O <> E').
      intro.
      subst E'.
      apply NC.
      Col.
    induction(eq_dec_points O A).
      subst A.
      exists B.
      unfold Sum.
      split.
        unfold Ar2.
        split; Col.
      exists O.
      exists B.
      unfold Pj.
      repeat split.
        right.
        auto.
        Col.
        induction(eq_dec_points O B).
          right; auto.
        left.
        right.
        repeat split; Col.
        right; auto.
      right; auto.
    assert(exists! A' , Proj A A' O E' E E').
      apply(project_existence A O E' E E'); intro; try (subst E' ; apply NC; Col).
      induction H4.
        apply H4.
        exists E'.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H4 A'.
    assert(HH:=parallel_existence1 O E A' H1).
    ex_and HH P.
    unfold unique in H5.
    spliter.
    assert(A <> A').
      intro.
      subst A'.
      apply project_col in H5.
      apply NC.
      apply (col_transitivity_1 _ A); Col.
    induction(eq_dec_points B O).
      subst B.
      exists A.
      unfold Sum.
      split.
        unfold Ar2.
        repeat split; Col.
      exists A'.
      exists A'.
      unfold Pj.
      unfold Proj in H5.
      spliter.
      repeat split.
        spliter.
        induction H11.
          left.
          apply par_symmetry.
          auto.
        contradiction.
        Col.
        right.
        auto.
        left.
        right.
        repeat split; Col.
        intro.
        subst A'.
        induction H11.
          induction H11.
            apply H11.
            exists E.
            split; Col.
          spliter.
          contradiction.
        contradiction.
      induction H11.
        left.
        apply par_symmetry.
        apply par_comm.
        auto.
      contradiction.
    assert(exists! C', Proj B C' A' P O E').
      apply(project_existence B A' P O E'); auto.
      apply par_distincts in H4.
      spliter.
      auto.
      intro.
      assert(Par O E O E').
        apply (par_trans _ _ A' P).
          auto.
        apply par_symmetry.
        auto.
      induction H10.
        apply H10.
        exists O.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H9 C'.
    unfold unique in H10.
    spliter.
    assert(exists! C : Tpoint, Proj C' C O E A A').
      apply(project_existence C' O E A A'); auto.
      intro.
      induction H11.
        apply H11.
        exists A.
        split; Col.
      spliter.
      assert(HH:=project_par_dir A A' O E' E E' H11 H5).
      assert(Col E A A').
        ColR.
      induction HH.
        apply H16.
        exists E.
        split; Col.
      spliter.
      apply NC.
      apply col_permutation_2.
      apply(col_transitivity_1 _ A'); Col.
      intro.
      subst A'.
      clean_trivial_hyps.
      unfold Proj in H5.
      spliter.
      apply NC.
      Col.
    ex_and H11 C.
    unfold unique in H12.
    spliter.
    unfold Proj in *.
    spliter.
    exists C.
    unfold Sum.
    split.
      unfold Ar2.
      repeat split; Col.
    exists A'.
    exists C'.
    unfold Pj.
    repeat split.
      left.
      induction H24.
        apply par_symmetry.
        auto.
      contradiction.
      Col.
      left.
      eapply (par_col_par _ _ _ P).
        intro.
        subst C'.
        induction H16.
          induction H16.
            apply H16.
            exists A'.
            split; Col.
          spliter.
          induction H20.
            induction H20.
              apply H20.
              exists A'.
              split; Col.
            spliter.
            apply NC.
            apply (col_transitivity_1 _ B); Col.
          subst A'.
          apply H14.
          right.
          repeat split; try finish; ColR.
        subst A'.
        apply H14.
        right.
        repeat split; try finish; ColR.
        assumption.
      ColR.
      induction H20.
        left.
        apply par_symmetry.
        auto.
      right; auto.
    induction H24.
      induction H16.
        left.
        apply (par_trans _ _ A A').
          apply par_symmetry.
          apply par_right_comm.
          auto.
        apply par_symmetry.
        auto.
      subst C'.
      right.
      auto.
    contradiction.
Qed.

(** We are not faithful to Tarski's def because for uniqueness we do not need the assumption that
 A and B are on line OE as it is implied by the definition of sum. *)

Lemma sum_uniqueness : forall A B C1 C2,
 Sum O E E' A B C1 ->
 Sum O E E' A B C2 ->
 C1 = C2.
Proof.
    intros.
    apply sum_to_sump in H.
    apply sum_to_sump in H0.
    unfold Sump in H.
    unfold Sump in H0.
    spliter.
    clean_duplicated_hyps.
    ex_and H4 A'.
    ex_and H0 C'.
    ex_and H1 P'.
    ex_and H2 A''.
    ex_and H6 C''.
    ex_and H2 P''.
    assert(A'=A'').
      apply(project_uniqueness A A' A'' O E' E E');auto.
    subst A''.
    assert(Col A' P' P'').
      assert(Par A' P' A' P'').
        apply (par_trans _ _ O E).
          apply par_symmetry.
          auto.
        auto.
      induction H9.
        apply False_ind.
        apply H9.
        exists A'.
        split; Col.
      spliter.
      Col.
    assert(Proj B C'' A' P' O E').
      eapply (project_col_project _ P''); Col.
      unfold Proj in H4.
      tauto.
    assert(C' = C'').
      apply(project_uniqueness B C' C'' A' P' O E');auto.
    subst C''.
    apply(project_uniqueness C' C1 C2 O E E E');auto.
Qed.

Lemma opp_exists : forall A,
 Col O E A ->
 exists MA, Opp O E E' A MA.
Proof.
    intros.
    assert(NC:= grid_ok).
    induction(eq_dec_points A O).
      subst A.
      exists O.
      unfold Opp.
      unfold Sum.
      split.
        unfold Ar2.
        repeat split; Col.
      exists O.
      exists O.
      repeat split; Col; try right; auto.
    prolong A O MA A O.
    exists MA.
    unfold Opp.
    apply sump_to_sum.
    unfold Sump.
    repeat split.
      apply bet_col in H1.
      apply (col_transitivity_1 _ A);Col.
      Col.
    assert(E <> E' /\ O <> E').
      split; intro; subst E'; apply NC; Col.
    spliter.
    assert(exists! P' : Tpoint, Proj MA P' O E' E E').
      apply(project_existence MA O E' E E'); auto.
      intro.
      induction H5.
        apply H5.
        exists E'.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H5 A'.
    unfold unique in H6.
    spliter.
    exists A'.
    assert(O <> E).
      intro.
      subst E.
      apply NC.
      Col.
    assert(HH:= parallel_existence1 O E A' H7).
    ex_and HH P'.
    assert(exists! C' : Tpoint, Proj A C' A' P' O E').
      apply(project_existence A A' P' O E'); auto.
      apply par_distincts in H8.
      spliter.
      auto.
      intro.
      assert(Par O E O E').
        apply (par_trans _ _ A' P').
          auto.
        apply par_symmetry; auto.
      induction H10.
        apply H10.
        exists O.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H9 C'.
    unfold unique in H10.
    spliter.
    exists C'.
    exists P'.
    split; auto.
    split; auto.
    split; auto.
    unfold Proj in H5.
    spliter.
    unfold Proj.
    repeat split; Col.
      intro.
      induction H15.
        apply H15.
        exists E.
        split; Col.
      apply NC.
      tauto.
    left.
    unfold Proj in H9.
    spliter.
    assert(Par O E' O A').
      right.
      repeat split; Col.
      intro.
      subst A'.
      clean_trivial_hyps.
      induction H14.
        induction H13.
          apply H13.
          exists E.
          split; Col.
          apply col_permutation_1.
          apply bet_col in H1.
          apply(col_transitivity_1 _ A); Col.
        apply NC.
        tauto.
      subst MA.
      apply cong_symmetry in H2.
      apply cong_identity in H2.
      contradiction.
    assert(Plg A C' A' O).
      apply pars_par_plg.
        induction H18.
          assert(Par A C' A' O).
            apply (par_trans _ _ O E').
              Par.
            Par.
          induction H20.
            auto.
          spliter.
          apply False_ind.
          apply NC.
          apply (col_transitivity_1 _ A'); Col.
          apply (col_transitivity_1 _ A); Col.
        subst C'.
        apply False_ind.
        induction H8.
          apply H8.
          exists A.
          split; Col.
        spliter.
        apply NC.
        apply (col_transitivity_1 _ A'); Col.
          intro.
          subst A'.
          apply par_distincts in H19.
          tauto.
        apply col_permutation_2.
        apply (col_transitivity_1 _ P'); Col.
      apply par_comm.
      apply (par_col_par _ _ _ P').
        intro.
        subst C'.
        induction H18.
          induction H18.
            apply H18.
            exists A'.
            split; Col.
          spliter.
          apply NC.
          apply (col_transitivity_1 _ A); Col.
        subst A'.
        induction H19.
          apply H18.
          exists O.
          split; Col.
        spliter.
        apply NC.
        apply (col_transitivity_1 _ A); Col.
        apply par_symmetry.
        apply (par_col_par _ _ _ E); Col.
        apply par_symmetry.
        Par.
      Col.
    assert(Parallelogram A O MA O).
      right.
      unfold Parallelogram_flat.
      repeat split; Col; Cong.
      left.
      intro.
      subst MA.
      apply between_identity in H1.
      contradiction.
    apply plg_to_parallelogram in H20.
    apply plg_permut in H20.
    apply plg_comm2 in H21.
    assert(Parallelogram C' A' MA O).
      assert(HH:= plg_pseudo_trans C' A' O A O MA H20 H21).
      induction HH.
        auto.
      spliter.
      subst MA.
      apply cong_symmetry in H2.
      apply cong_identity in H2.
      contradiction.
    apply plg_par in H22.
      spliter.
      induction H14.
        apply (par_trans _ _ A' MA).
          auto.
        Par.
      subst MA.
      apply par_distincts in H23.
      tauto.
      intro.
      subst C'.
      unfold Parallelogram in H20.
      induction H20.
        unfold Parallelogram_strict in H20.
        spliter.
        apply par_distincts in H23.
        tauto.
      unfold Parallelogram_flat in H20.
      spliter.
      apply cong_symmetry in H24.
      apply cong_identity in H24.
      subst A.
      tauto.
    intro.
    subst MA.
    unfold Parallelogram in H21.
    induction H21.
      unfold Parallelogram_strict in H21.
      spliter.
      unfold TS in H21; unfold Parallelogram.
      spliter; Col.
    unfold Parallelogram_flat in H21.
    spliter.
    apply NC.
    apply (col_transitivity_1 _ A); Col.
    apply (col_transitivity_1 _ A'); Col.
    intro.
    subst A'.
    apply cong_identity in H24.
    subst A.
    tauto.
Qed.

Lemma opp0 : Opp O E E' O O.
Proof.
    assert(NC:=grid_ok).
    assert(O <> E' /\ E <> E').
      split; intro ; subst E'; apply NC; Col.
    spliter.
    assert(O <> E).
      intro.
      subst E.
      apply NC; Col.
    unfold Opp.
    apply sump_to_sum.
    unfold Sump.
    repeat split; Col.
    exists O.
    exists O.
    exists E.
    split.
      apply project_trivial; Col.
      intro.
      induction H2.
        apply H2.
        exists E'.
        split; Col.
      spliter.
      contradiction.
    split.
      apply par_reflexivity; auto.
    split.
      apply project_trivial; Col.
      intro.
      induction H2.
        apply H2.
        exists O.
        split; Col.
      spliter.
      apply NC.
      Col.
    apply project_trivial; Col.
    intro.
    induction H2.
      apply H2.
      exists E.
      split; Col.
    spliter.
    contradiction.
Qed.

Lemma pj_trivial : forall A B C, Pj A B C C.
Proof.
    intros.
    unfold Pj.
    right.
    auto.
Qed.

Lemma sum_O_O : Sum O E E' O O O.
Proof.
    unfold Sum.
    assert(O <> E' /\ E <> E').
      split; intro ; subst E'; apply grid_ok; Col.
    split.
      spliter.
      unfold Ar2.
      repeat split; Col.
    exists O.
    exists O.
    repeat split;try (apply pj_trivial).
    Col.
Qed.

Lemma sum_A_O : forall A, Col O E A -> Sum O E E' A O A.
Proof.
    intros.
    unfold Sum.
    split.
      repeat split; Col.
    assert(O <> E' /\ E <> E').
      split; intro; subst E'; apply grid_ok; Col.
    spliter.
    induction (eq_dec_points A O).
      exists O.
      exists O.
      repeat split;  Col; unfold Pj ; try auto.
    assert(~ Par E E' O E').
      intro.
      induction H3.
        apply H3.
        exists E'.
        split; Col.
      spliter.
      apply grid_ok.
      Col.
    assert(HH:= project_existence A O E' E E' H1 H0 H3).
    ex_and HH A'.
    unfold unique in H4.
    spliter.
    exists A'.
    exists A'.
    unfold Proj in H4.
    spliter.
    repeat split; Col.
      unfold Pj.
      induction H9.
        left.
        apply par_symmetry.
        Par.
      tauto.
      unfold Pj.
      tauto.
      unfold Pj.
      left.
      right.
      repeat split; Col.
      intro.
      subst A'.
      induction H9.
        induction H9.
          apply H9.
          exists E.
          split; Col.
        spliter.
        contradiction.
      contradiction.
    unfold Pj.
    induction H9.
      left.
      apply par_symmetry.
      Par.
    right.
    auto.
Qed.

Lemma sum_O_B : forall B, Col O E B -> Sum O E E' O B B.
Proof.
    intros.
    induction(eq_dec_points B O).
      subst B.
      apply sum_O_O.
    unfold Sum.
    split.
      repeat split; Col.
    assert(O <> E' /\ E <> E').
      split; intro; subst E'; apply grid_ok; Col.
    spliter.
    assert(~ Par E E' O E').
      intro.
      induction H3.
        apply H3.
        exists E'.
        split; Col.
      spliter.
      apply grid_ok.
      Col.
    exists O.
    exists B.
    repeat split; try(apply pj_trivial).
      Col.
    left.
    right.
    repeat split; Col.
    intro.
    subst E.
    apply grid_ok.
    Col.
Qed.

Lemma opp0_uniqueness : forall M, Opp O E E' O M -> M = O.
Proof.
    intros.
    assert(NC:= grid_ok).
    unfold Opp in H.
    apply sum_to_sump in H.
    unfold Sump in H.
    spliter.
    ex_and H1 A'.
    ex_and H2 C'.
    ex_and H1 P'.
    unfold Proj in *.
    spliter.
    induction H8.
      induction H12.
        assert(Par O E' E E').
          apply (par_trans _ _ C' O).
            apply par_symmetry.
            Par.
          Par.
        apply False_ind.
        induction H17.
          apply H17.
          exists E'.
          split; Col.
        spliter.
        contradiction.
      subst C'.
      apply par_distincts in H8.
      tauto.
    subst C'.
    assert( A' = O).
      apply (l6_21 O E E' O); Col.
      induction H2.
        apply False_ind.
        apply H2.
        exists O.
        split; Col.
      spliter.
      apply col_permutation_1.
      apply(col_transitivity_1 _ P'); Col.
    subst A'.
    induction H16.
      induction H8.
        apply False_ind.
        apply H8.
        exists E.
        split; Col.
      spliter.
      contradiction.
    assumption.
Qed.

Lemma proj_pars : forall A A' C' , A <> O -> Col O E A -> Par O E A' C' -> Proj A A' O E' E E' -> Par_strict O E A' C'.
Proof.
    intros.
    unfold Par_strict.
    assert(HH:=grid_ok).
    repeat split; try apply all_coplanar.
      intro.
      subst E.
      apply HH.
      Col.
      apply par_distincts in H1.
      tauto.
    intro.
    ex_and H3 X.
    unfold Proj in H2.
    spliter.
    induction H1.
      apply H1.
      exists X.
      split; Col.
    spliter.
    assert(Col A' O E).
      apply (col_transitivity_1 _ C'); Col.
    induction(eq_dec_points A' O).
      subst A'.
      clean_trivial_hyps.
      induction H8.
        induction H7.
          apply H7.
          exists E.
          split; Col.
        spliter.
        contradiction.
      contradiction.
    apply grid_ok.
    apply(col_transitivity_1 _ A'); Col.
Qed.

Lemma proj_col : forall A A' C' , A = O -> Col O E A -> Par O E A' C' -> Proj A A' O E' E E' -> A' = O.
Proof.
    intros.
    assert(HH:=grid_ok).
    unfold Proj in H2.
    spliter.
    subst A.
    induction H6.
      apply False_ind.
      apply H4.
      apply par_symmetry.
      eapply (par_col_par _ _ _ A'); Col.
      apply par_symmetry.
      Par.
    auto.
Qed.

Lemma grid_not_par : ~Par O E E E' /\ ~Par O E O E' /\ ~Par O E' E E' /\ O <> E /\ O <> E' /\ E <> E'.
Proof.
    repeat split.
      intro.
      unfold Par in H.
      induction H.
        apply H.
        exists E.
        split; Col.
      spliter.
      contradiction.
      intro.
      induction H.
        apply H.
        exists O.
        split; Col.
      spliter.
      apply grid_ok.
      Col.
      intro.
      induction H.
        apply H.
        exists E'.
        split; Col.
      spliter.
      contradiction.
      intro.
      subst E.
      apply grid_ok.
      Col.
      intro.
      subst E'.
      apply grid_ok.
      Col.
    intro.
    subst E'.
    apply grid_ok.
    Col.
Qed.

Lemma proj_id : forall A A', Proj A A' O E' E E' -> Col O E A -> Col O E A' -> A = O.
Proof.
    intros.
    assert(HH:=grid_not_par).
    spliter.
    unfold Proj in H.
    spliter.
    induction H11.
      apply(l6_21 O E E' O); Col.
        assert(Col O A' A).
          apply(col_transitivity_1 _ E); Col.
        apply col_permutation_2.
        apply (col_transitivity_1 _ A'); Col.
        intro.
        subst A'.
        induction H11.
          apply H11.
          exists E.
          split; Col.
        spliter.
        contradiction.
    subst.
    apply(l6_21 O E E' O); Col.
Qed.

Lemma sum_O_B_eq : forall B C, Sum O E E' O B C -> B = C.
Proof.
    intros.
    assert (HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HH:=sum_O_B B H2).
    apply (sum_uniqueness O B); auto.
Qed.

Lemma sum_A_O_eq : forall A C, Sum O E E' A O C -> A = C.
Proof.
    intros.
    assert (HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HH:=sum_A_O A H1).
    apply (sum_uniqueness A O); auto.
Qed.

Lemma sum_par_strict : forall A B C A' C', Ar2 O E E' A B C -> A <> O -> Pj E E' A A' -> Col O E' A' -> Pj O E A' C' -> Pj O E' B C' -> Pj E' E C' C
                                           -> A' <> O /\ (Par_strict O E A' C' \/ B = O).
Proof.
    intros.
    assert(Sum O E E' A B C).
      unfold Sum.
      split.
        auto.
      exists A'.
      exists C'.
      repeat split; auto.
    unfold Ar2 in H.
    unfold Pj in *.
    spliter.
    assert(A' <> O).
      intro.
      subst A'.
      induction H3.
        induction H3.
          apply H3.
          exists O.
          split; Col.
        spliter.
        induction H1.
          induction H1.
            apply H1.
            exists E.
            split; Col.
          spliter.
          apply grid_ok.
          apply(col_transitivity_1 _ A); Col.
        contradiction.
      subst C'.
      induction H1.
        induction H1.
          apply H1.
          exists E.
          split; Col.
        spliter.
        apply grid_ok.
        apply(col_transitivity_1 _ A); Col.
      contradiction.
    split.
      auto.
    induction(eq_dec_points B O).
      tauto.
    left.
    induction H3.
      induction H3.
        assumption.
      spliter.
      apply False_ind.
      apply grid_ok.
      assert(Col A' O E ).
        apply(col_transitivity_1 _ C'); Col.
      apply(col_transitivity_1 _ A'); Col.
    subst C'.
    apply False_ind.
    induction H4.
      induction H3.
        apply H3.
        exists A'.
        split; Col.
      spliter.
      assert(Col O B E').
        apply (col_transitivity_1 _ A'); Col.
      apply grid_ok.
      apply (col_transitivity_1 _ B); Col.
    subst A'.
    assert(HH:= grid_not_par).
    spliter.
    induction H5.
      apply H3.
      apply par_symmetry.
      apply (par_col_par _ _ _ B); Col.
      apply par_right_comm.
      apply (par_col_par _ _ _ C); Par.
      apply col_permutation_1.
      apply(col_transitivity_1 _ E); Col.
    subst C.
    apply grid_ok.
    apply(col_transitivity_1 _ B); Col.
Qed.

Lemma sum_A_B_A : forall A B, Sum O E E' A B A -> B = O.
Proof.
    intros.
    unfold Sum in H.
    spliter.
    ex_and H0 A'.
    ex_and H1 C'.
    assert(HH:= grid_not_par).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      unfold Pj in *.
      unfold Ar2 in H.
      spliter.
      induction H0.
        induction H0.
          apply False_ind.
          apply H0.
          exists E'.
          split; Col.
        spliter.
        apply False_ind.
        apply grid_ok.
        ColR.
      subst A'.
      induction H2.
        induction H4.
          apply False_ind.
          apply H5.
          apply (par_trans _ _ O C') ; Par.
        subst C'.
        apply par_distincts in H0.
        tauto.
      subst C'.
      induction H3.
        induction H0.
          apply False_ind.
          apply H0.
          exists O.
          split; Col.
        spliter.
        induction(eq_dec_points B O).
          auto.
        apply False_ind.
        apply grid_ok.
        ColR.
      assumption.
    assert(A' <> O /\ (Par_strict O E A' C' \/ B = O)).
      apply(sum_par_strict A B A A' C');auto.
    spliter.
    induction(eq_dec_points B O).
      auto.
    induction H13.
      unfold Pj in *.
      unfold Ar2 in H.
      spliter.
      induction H0.
        induction H4.
          assert(Par A A' A C').
            apply (par_trans _ _ E E'); Par.
          apply False_ind.
          induction H18.
            apply H18.
            exists A.
            split; Col.
          spliter.
          apply H13.
          exists A.
          split; Col.
        subst C'.
        apply False_ind.
        apply H13.
        exists A.
        split; Col.
      subst A'.
      apply False_ind.
      apply grid_ok.
      apply(col_transitivity_1 _ A);Col.
    contradiction.
Qed.

Lemma sum_A_B_B : forall A B, Sum O E E' A B B -> A = O.
Proof.
    intros.
    unfold Sum in H.
    spliter.
    ex_and H0 A'.
    ex_and H1 C'.
    assert(HH:= grid_not_par).
    spliter.
    unfold Pj in *.
    unfold Ar2 in H.
    spliter.
    induction H3.
      induction H4.
        apply False_ind.
        apply H7.
        apply(par_trans _ _ B C'); Par.
      subst C'.
      apply par_distincts in H3.
      tauto.
    subst C'.
    induction(eq_dec_points A O).
      auto.
    assert(A' <> O /\ (Par_strict O E A' B \/ B = O)).
      apply(sum_par_strict A B B A' B);auto.
        repeat split; auto.
      unfold Pj.
      auto.
    spliter.
    induction H15.
      apply False_ind.
      apply H15.
      exists B.
      split; Col.
    subst B.
    induction H2.
      induction H2.
        apply False_ind.
        apply H2.
        exists O.
        split; Col.
      spliter.
      apply False_ind.
      apply H.
      ColR.
    subst A'.
    tauto.
Qed.

Lemma sum_uniquenessB : forall A X Y C, Sum O E E' A X C -> Sum O E E' A Y C -> X = Y.
Proof.
    intros.
    induction (eq_dec_points A O).
      subst A.
      assert(X = C).
        apply(sum_O_B_eq X C H).
      assert(Y = C).
        apply(sum_O_B_eq Y C H0).
      subst X.
      subst Y.
      auto.
    assert(HSx:= H).
    assert(HSy:= H0).
    unfold Sum in H.
    unfold Sum in H0.
    spliter.
    assert(Hx:=H).
    assert(Hy:=H0).
    unfold Ar2 in H.
    unfold Ar2 in H0.
    spliter.
    ex_and H2 A''.
    ex_and H10 C''.
    ex_and H3 A'.
    ex_and H14 C'.
    clean_duplicated_hyps.
    assert(A' <> O /\ (Par_strict O E A' C' \/ X = O)).
      apply(sum_par_strict A X C A' C'); auto.
    assert(A'' <> O /\ (Par_strict O E A'' C'' \/ Y = O)).
      apply(sum_par_strict A Y C A'' C''); auto.
    spliter.
    unfold Pj in *.
    induction(eq_dec_points X O).
      subst X.
      assert(HH:=sum_A_O A H7).
      assert(C = A).
        apply (sum_uniqueness A O); auto.
      subst C.
      assert(Y=O).
        apply (sum_A_B_A A ); auto.
      subst Y.
      auto.
    induction H2.
      induction H3.
        assert(Par A A' A A'').
          apply (par_trans _ _ E E'); Par.
        induction H19.
          apply False_ind.
          apply H19.
          exists A.
          split; Col.
        spliter.
        assert(A' = A'').
          apply (l6_21 O E' A A'); Col.
          intro.
          apply grid_ok.
          apply(col_transitivity_1 _ A); Col.
        subst A''.
        induction H4.
          induction H6.
            assert(Par A' C' A' C'').
              apply(par_trans _ _ O E); left; Par.
            induction H23.
              apply False_ind.
              apply H23.
              exists A'.
              split; Col.
            spliter.
            induction H13.
              induction H17.
                assert(Par C C' C C'').
                  apply(par_trans _ _ E' E); Par.
                induction H27.
                  apply False_ind.
                  apply H27.
                  exists C.
                  split; Col.
                spliter.
                assert(C' = C'').
                  apply (l6_21 A' C' C C'); Col.
                  intro.
                  apply H6.
                  exists C.
                  split; Col.
                subst C''.
                clean_trivial_hyps.
                induction H12.
                  induction H16.
                    assert(Par Y C' X C').
                      apply (par_trans _ _ O E'); Par.
                    induction H21.
                      apply False_ind.
                      apply H21.
                      exists C'.
                      split; Col.
                    spliter.
                    apply(l6_21 O E C' X); Col.
                    intro.
                    apply H4.
                    exists C'.
                    split; Col.
                  subst X.
                  clean_duplicated_hyps.
                  apply False_ind.
                  apply H6.
                  exists C'.
                  split; Col.
                subst Y.
                apply False_ind.
                apply H6.
                exists C'.
                split; Col.
              subst C'.
              clean_duplicated_hyps.
              clean_trivial_hyps.
              apply False_ind.
              apply H6.
              exists C.
              split; Col.
            subst C''.
            apply False_ind.
            apply H4.
            exists C.
            split; Col.
          subst X.
          tauto.
        subst Y.
        assert(A = C).
          apply(sum_A_O_eq A C HSy).
        subst C.
        clean_duplicated_hyps.
        clean_trivial_hyps.
        apply(sum_A_B_A A); auto.
      subst A'.
      clean_duplicated_hyps.
      induction H15.
        induction H6.
          apply False_ind.
          apply H3.
          exists A.
          split; Col.
        subst X.
        tauto.
      subst C'.
      induction H6.
        apply False_ind.
        apply H.
        exists A.
        split; Col.
      contradiction.
    subst A''.
    induction H4.
      apply False_ind.
      apply H2.
      exists A.
      split; Col.
    subst Y.
    assert(A = C).
      apply (sum_A_O_eq A C HSy).
    subst C.
    apply (sum_A_B_A A _ HSx).
Qed.

Lemma sum_uniquenessA : forall B X Y C, Sum O E E' X B C -> Sum O E E' Y B C -> X = Y.
Proof.
    intros.
    induction (eq_dec_points B O).
      subst B.
      assert(X = C).
        apply(sum_A_O_eq X C H).
      subst X.
      assert(Y = C).
        apply(sum_A_O_eq Y C H0).
      subst Y.
      auto.
    assert(HSx:= H).
    assert(HSy:= H0).
    unfold Sum in H.
    unfold Sum in H0.
    spliter.
    assert(Hx:=H).
    assert(Hy:=H0).
    unfold Ar2 in H.
    unfold Ar2 in H0.
    spliter.
    ex_and H2 A''.
    ex_and H10 C''.
    ex_and H3 A'.
    ex_and H14 C'.
    clean_duplicated_hyps.
    unfold Pj in *.
    induction(eq_dec_points X O).
      subst X.
      assert(HH:=sum_O_B B H8).
      assert(B = C).
        apply (sum_uniqueness O B); auto.
      subst C.
      apply sym_equal.
      apply (sum_A_B_B Y B); auto.
    induction(eq_dec_points Y O).
      subst Y.
      assert(HH:=sum_O_B B H8).
      assert(B = C).
        apply (sum_uniqueness O B); auto.
      subst C.
      apply (sum_A_B_B X B); auto.
    assert(A' <> O /\ (Par_strict O E A' C' \/ B = O)).
      apply(sum_par_strict X B C A' C'); auto.
    assert(A'' <> O /\ (Par_strict O E A'' C'' \/ B = O)).
      apply(sum_par_strict Y B C A'' C''); auto.
    spliter.
    induction H12.
      induction H16.
        assert(Par B C' B C'').
          apply (par_trans _ _ O E'); Par.
        induction H20.
          apply False_ind.
          apply H20.
          exists B.
          split; Col.
        spliter.
        clean_trivial_hyps.
        induction H13.
          induction H17.
            assert(Par C C' C C'').
              apply (par_trans _ _ E E'); Par.
            induction H22.
              apply False_ind.
              apply H22.
              exists C.
              split; Col.
            spliter.
            assert(C' = C'').
              apply(l6_21 C C' B C'); Col.
              intro.
              induction H19.
                apply H19.
                exists C'.
                split.
                  assert(Col O B C).
                    apply (col_transitivity_1 _ E); Col.
                    intro.
                    apply grid_ok.
                    subst E.
                    Col.
                  assert(Col E B C).
                    apply (col_transitivity_1 _ O); Col.
                    intro.
                    apply grid_ok.
                    subst E.
                    Col.
                  apply(col3 B C); Col.
                  intro.
                  subst C.
                  clean_trivial_hyps.
                  apply(sum_A_B_B) in HSx.
                  contradiction.
                Col.
              contradiction.
            subst C''.
            clean_trivial_hyps.
            induction H19.
              induction H18.
                assert(Par A' C' A'' C').
                  apply (par_trans _ _ O E);left; Par.
                induction H23.
                  apply False_ind.
                  apply H23.
                  exists C'.
                  split; Col.
                spliter.
                assert(A'= A'').
                  apply (l6_21 O E' C' A'); Col.
                  intro.
                  induction H16.
                    apply H16.
                    exists C'.
                    split; Col.
                  spliter.
                  apply H1.
                  apply (l6_21 O E C' O); Col.
                    intro.
                    apply grid_ok.
                    ColR.
                  intro.
                  subst C'.
                  clean_trivial_hyps.
                  apply H18.
                  exists O.
                  split; Col.
                subst A''.
                clean_trivial_hyps.
                clean_duplicated_hyps.
                induction H2.
                  induction H3.
                    assert(Par Y A' X A').
                      apply(par_trans _ _ E E'); Par.
                    induction H6.
                      apply False_ind.
                      apply H6.
                      exists A'.
                      split; Col.
                    spliter.
                    apply (l6_21 O E A' X); Col.
                    intro.
                    apply H19.
                    exists A'.
                    split; Col.
                  subst X.
                  apply False_ind.
                  apply H19.
                  exists A'.
                  split; Col.
                subst Y.
                apply False_ind.
                apply H19.
                exists A'.
                split; Col.
              contradiction.
            contradiction.
          subst C'.
          apply False_ind.
          induction H16.
            apply H16.
            exists O.
            split.
              Col.
            apply(col3 O E); Col.
            intro.
            subst E.
            apply grid_ok; Col.
          spliter.
          apply grid_ok.
          apply(colx B C); Col.
        subst C''.
        apply False_ind.
        induction H12.
          apply H12.
          exists O.
          split.
            Col.
          apply(col3 O E); Col.
          intro.
          subst E.
          apply grid_ok; Col.
        spliter.
        apply grid_ok.
        apply(colx B C); Col.
      apply False_ind.
      subst C'.
      induction H19.
        apply H16.
        exists B.
        split; Col.
      contradiction.
    subst C''.
    apply False_ind.
    induction H18.
      apply H12.
      exists B.
      split; Col.
    contradiction.
Qed.

Lemma sum_B_null : forall A B, Sum O E E' A B A -> B = O.
Proof.
    intros.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HP:= sum_A_O A H1).
    apply(sum_uniquenessB A B O A); auto.
Qed.

Lemma sum_A_null : forall A B, Sum O E E' A B B -> A = O.
Proof.
    intros.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HP:= sum_O_B B H2).
    apply(sum_uniquenessA B A O B); auto.
Qed.

Lemma sum_plg : forall A B C, Sum O E E' A B C -> (A <> O ) \/ ( B <> O) -> exists A', exists C', Plg O B C' A' /\ Plg C' A' A C.
Proof.
    intros.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    ex_and H1 A'.
    ex_and H2 C'.
    exists A'.
    exists C'.
    unfold Pj in *.
    unfold Ar2 in H.
    assert(HH:= grid_not_par).
    spliter.
    induction(eq_dec_points O B).
      subst B.
      assert(HH:=sum_A_O A H12).
      assert(HP:=sum_uniqueness A O C A HS HH).
      subst C.
      induction H4.
        induction H4.
          apply False_ind.
          apply H4.
          exists O.
          split; Col.
        spliter.
        induction H3.
          induction H3.
            apply False_ind.
            apply H3.
            exists O.
            split.
              Col.
            apply (col_transitivity_1 _ E'); Col.
          spliter.
          apply False_ind.
          apply grid_ok.
          assert(Col C' O E).
            ColR.
          ColR.
        subst C'.
        split; apply parallelogram_to_plg; apply plg_trivial1.
          auto.
        intro.
        subst A'.
        apply H.
        ColR.
      subst C'.
      apply False_ind.
      induction H5.
        apply H6.
        apply par_symmetry.
        apply (par_col_par _ _ _ A); Col; Par.
      subst A.
      induction H0; tauto.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=sum_O_B B H13 ).
      assert(HP:=sum_uniqueness O B C B HS HH).
      subst C.
      clean_trivial_hyps.
      induction H1.
        induction H1.
          apply False_ind.
          apply H1.
          exists E'.
          split; Col.
        spliter.
        apply False_ind.
        apply H.
        apply (col_transitivity_1 _ A'); Col.
      subst A'.
      clean_trivial_hyps.
      induction H5.
        induction H4.
          apply False_ind.
          apply H8.
          apply (par_trans _ _ B C'); Par.
        subst C'.
        split; apply parallelogram_to_plg; apply plg_trivial; auto.
      subst C'.
      split; apply parallelogram_to_plg; apply plg_trivial; auto.
    assert(A' <> O).
      intro.
      subst A'.
      induction H1.
        apply H6.
        apply par_symmetry.
        apply (par_col_par _ _ _ A); Col;Par.
      contradiction.
    assert(A' <> O /\ (Par_strict O E A' C' \/ B = O)).
      apply(sum_par_strict A B C A' C');auto.
      repeat split; auto.
    spliter.
    induction H19.
      assert(Par O B C' A').
        apply par_symmetry.
        apply (par_col_par _ _ _ E); finish.
      assert(Par_strict O B C' A').
        induction H20.
          auto.
        spliter.
        apply False_ind.
        apply H19.
        exists O.
        split; Col.
      (*Par O A' B C'*)
      induction H4.
        assert(Par O A' B C').
          apply par_symmetry.
          apply (par_col_par _ _ _ E'); Par; Col.
        assert(HX:= pars_par_plg O B C' A' H21 H22).
        assert(Par C' A' A C).
          apply(par_col_par _ _ _ O).
            intro.
            subst C.
            apply H15.
            apply sym_equal.
            apply(sum_A_B_A A); auto.
            apply par_right_comm.
            apply(par_col_par _ _ _ B).
              auto.
              Par.
            ColR.
          ColR.
        assert(Par_strict C' A' A C).
          induction H23.
            auto.
          spliter.
          apply False_ind.
          apply H19.
          exists C'.
          split.
            ColR.
          Col.
        induction H1.
          induction H5.
            assert(Par C' C A' A).
              apply (par_trans _ _ E E'); Par.
            assert(HY:= pars_par_plg C' A' A C H24 H25).
            split; auto.
          subst C'.
          assert_diffs;contradiction.
        split; Col.
        subst A'.
        assert_diffs.
        contradiction.
      subst C'.
      assert_diffs.
      contradiction.
    subst B.
    tauto.
Qed.

Lemma sum_cong : forall A B C, Sum O E E' A B C -> (A <> O \/ B <> O) -> Parallelogram_flat O A C B.
Proof.
    intros.
    induction(eq_dec_points A O).
      subst A.
      assert(HP:= (sum_O_B_eq B C H)).
      subst C.
      induction H0.
        tauto.
      assert(Parallelogram O O B B).
        apply plg_trivial1; auto.
      induction H1.
        apply False_ind.
        unfold Parallelogram_strict in H1.
        spliter.
        apply par_distincts in H2.
        tauto.
      assumption.
    assert(exists A' C' : Tpoint, Plg O B C' A' /\ Plg C' A' A C).
      apply(sum_plg A B C); auto.
    ex_and H2 A'.
    ex_and H3 C'.
    apply plg_to_parallelogram in H2.
    apply plg_to_parallelogram in H3.
    apply plgf_permut.
    assert(HH:=plg_pseudo_trans O B C' A' A C H2 H3).
    induction HH.
      induction H4.
        apply False_ind.
        apply H4.
        unfold Sum in H.
        spliter.
        unfold Ar2 in H.
        spliter.
        assert_diffs.
        ColR.
      apply plgf_comm2.
      auto.
    spliter.
    subst A.
    apply False_ind.
    subst C.
    tauto.
Qed.

Lemma sum_cong2 : forall A B C,
  Sum O E E' A B C ->
  (A <> O \/ B <> O) ->
  (Cong O A B C /\ Cong O B A C).
Proof.
intros.
apply sum_cong in H.
unfold Parallelogram_flat in *.
spliter;split;Cong.
assumption.
Qed.

Lemma sum_comm : forall A B C, Sum O E E' A B C -> Sum O E E' B A C.
Proof.
    intros.
    induction (eq_dec_points B O).
      subst B.
      assert(Col O E A).
        unfold Sum in H.
        spliter.
        unfold Ar2 in H.
        tauto.
      assert(C = A).
        apply (sum_uniqueness A O).
          auto.
        apply sum_A_O.
        auto.
      subst C.
      apply sum_O_B.
      auto.
    induction(eq_dec_points A O).
      subst A.
      assert(Col O E B).
        unfold Sum in H.
        spliter.
        unfold Ar2 in H.
        tauto.
      assert(B = C).
        apply (sum_uniqueness O B).
          apply sum_O_B.
          Col.
        auto.
      subst C.
      apply sum_A_O.
      Col.
    assert(A <> O \/ B <> O).
      left.
      auto.
    assert(HH:=grid_not_par).
    spliter.
    assert(HH := sum_plg A B C H H2).
    ex_and HH A'.
    ex_and H9 C'.
    assert(exists ! P' : Tpoint, Proj B P' O E' E E').
      apply(project_existence B O E' E E'); auto.
      intro.
      apply H5.
      Par.
    unfold unique in H11.
    ex_and H11 B'.
    clear H12.
    assert(HH:= parallel_existence1 O E B' H6).
    ex_and HH P'.
    assert(exists! P : Tpoint, Proj A P B' P' O E').
      apply(project_existence A B' P' O E'); auto.
      apply par_distincts in H12.
      spliter.
      auto.
      intro.
      apply H4.
      apply(par_trans _ _ B' P'); Par.
    unfold unique in H13.
    ex_and H13 D'.
    clear H14.
    assert( Ar2 O E E' A B C).
      unfold Sum in H.
      tauto.
    assert(HH:= sum_to_sump O E E' A B C H).
    unfold Sump in H13.
    apply sump_to_sum.
    unfold Sump.
    unfold Ar2 in H14.
    spliter.
    repeat split; Col.
    exists B'.
    exists D'.
    exists P'.
    split; auto.
    split; auto.
    split; auto.
    assert(Par_strict O E B' P').
      induction H12.
        auto.
      spliter.
      apply False_ind.
      assert(HA:=H11).
      unfold Proj in H11.
      spliter.
      assert(Col B' O E).
        apply (col_transitivity_1 _ P'); Col.
      assert(B' <> O).
        intro.
        subst B'.
        apply project_id in HA.
          contradiction.
        induction H24.
          induction H24.
            apply False_ind.
            apply H24.
            exists E.
            split; Col.
          spliter.
          contradiction.
        contradiction.
      apply grid_ok.
      apply (col_transitivity_1 _ B'); Col.
    assert(Par O A B' D').
      apply (par_col_par _ _ _ P').
        intro.
        subst D'.
        unfold Proj in *.
        spliter.
        induction H22.
          induction H22.
            apply H22.
            exists B'.
            split; Col.
          spliter.
          apply grid_ok.
          apply (col_transitivity_1 _ A); Col.
        subst B'.
        apply H18.
        exists A.
        split; Col.
        apply par_symmetry.
        apply (par_col_par _ _ _ E); Col; Par.
      unfold Proj in H13.
      spliter.
      Col.
    assert(Par_strict O A B' D').
      induction H19.
        auto.
      spliter.
      apply False_ind.
      apply H18.
      unfold Proj in H13.
      spliter.
      exists O.
      split.
        Col.
      apply col_permutation_2.
      apply (col_transitivity_1 _ D'); Col.
    assert(Par O B' A D').
      unfold Proj in H13.
      spliter.
      induction H24.
        apply par_symmetry.
        apply(par_col_par _ _ _ E'); Par.
          intro.
          subst B'.
          apply H20.
          exists O.
          split;Col.
        unfold Proj in H11.
        spliter.
        auto.
      subst D'.
      apply False_ind.
      apply H20.
      exists A.
      split; Col.
    assert(Plg O A D' B').
      apply(pars_par_plg O A D' B' ); Par.
    assert(HT:=sum_cong A B C H H2).
    assert(Parallelogram D' B' B C \/ D' = B' /\ O = A /\ C = B /\ D' = C).
      apply(plg_pseudo_trans D' B' O A C B).
        apply plg_to_parallelogram in H22.
        apply plg_permut in H22.
        apply plg_permut in H22.
        auto.
      right.
      auto.
    induction H23.
      repeat split; auto.
      apply plg_permut in H23.
      apply plg_par in H23.
        unfold Proj in *.
        spliter.
        induction H32.
          left.
          apply (par_trans _ _ B B'); Par.
        subst B'.
        apply par_distincts in H23.
        tauto.
        intro.
        subst B'.
        apply H20.
        exists B.
        split.
          ColR.
        Col.
      intro.
      subst C.
      assert(HN:= sum_A_null A B H).
      contradiction.
    spliter.
    subst A.
    tauto.
Qed.

Lemma cong_sum : forall A B C,
  O <> C \/ B <> A -> Ar2 O E E' A B C ->
  Cong O A B C -> Cong O B A C ->
  Sum O E E' A B C.
Proof.
    intros A B C.
    intro Hor.
    intros.
    induction (eq_dec_points A O).
      subst A.
      unfold Ar2 in H.
      spliter.
      apply cong_symmetry in H0.
      apply cong_identity in H0.
      subst C.
      apply sum_O_B; Col.
    induction (eq_dec_points B O).
      subst B.
      unfold Ar2 in H.
      spliter.
      apply cong_symmetry in H1.
      apply cong_identity in H1.
      subst C.
      apply sum_A_O; Col.
    unfold Sum.
    split; auto.
    unfold Ar2 in H.
    assert(HH:=grid_not_par).
    spliter.
    assert(exists ! P' : Tpoint, Proj A P' O E' E E').
      apply(project_existence A O E' E E'); auto.
      intro.
      apply H6.
      Par.
    ex_and H13 A'.
    unfold unique in H14.
    spliter.
    clear H14.
    unfold Proj in H13.
    spliter.
    clean_duplicated_hyps.
    assert(HH:=parallel_existence1 O E A' H7).
    ex_and HH P'.
    assert(exists ! C' : Tpoint, Proj B C' A' P' O E').
      apply(project_existence B A' P' O E'); auto.
      apply par_distincts in H.
      spliter.
      auto.
      intro.
      apply H5.
      apply(par_trans _ _ A' P'); Par.
    ex_and H13 C'.
    unfold unique in H14.
    spliter.
    clear H14.
    unfold Proj in H13.
    spliter.
    exists A'.
    exists C'.
    assert(A' <> O).
      intro.
      subst A'.
      induction H17.
        induction H17.
          apply H17.
          exists E.
          split; Col.
        spliter.
        contradiction.
      contradiction.
    assert(Par_strict O E A' P').
      unfold Par_strict.
      repeat split; auto; try apply all_coplanar.
      intro.
      ex_and H21 X.
      induction H.
        apply H.
        exists X.
        split; Col.
      spliter.
      apply grid_ok.
      ColR.
    assert(A <> A').
      intro.
      subst A'.
      apply H21.
      exists A.
      split; Col.
    repeat split; Col.
      induction H17.
        left; Par.
      right; auto.
      left.
      apply (par_col_par _ _ _ P').
        intro.
        subst C'.
        induction H19.
          induction H19.
            apply H19.
            exists A'.
            split; Col.
          spliter.
          apply grid_ok.
          ColR.
        subst A'.
        apply H21.
        exists B.
        split; Col.
        Par.
      Col.
      induction H19.
        left.
        Par.
      right.
      auto.
    assert(A' <> C').
      intro.
      subst C'.
      induction H19.
        induction H19.
          apply H19.
          exists A'.
          split; Col.
        spliter.
        apply grid_ok.
        ColR.
      subst A'.
      apply H21.
      exists B.
      split; Col.
    assert(Plg O B C' A').
      apply(pars_par_plg O B C' A').
        apply par_strict_right_comm.
        apply(par_strict_col_par_strict _ _ _ P').
          auto.
          apply par_strict_symmetry.
          apply(par_strict_col_par_strict _ _ _ E).
            auto.
            Par.
          Col.
        Col.
      induction H19.
        apply par_symmetry.
        apply(par_col_par _ _ _ E').
          auto.
          Par.
        Col.
      subst C'.
      apply False_ind.
      apply H21.
      exists B.
      split; Col.
    assert(Plg O B C A).
      apply(parallelogram_to_plg).
      right.
      unfold Parallelogram_flat.
      repeat split; try ColR.
        Cong.
        Cong.
      auto.
    apply plg_to_parallelogram in H24.
    apply plg_to_parallelogram in H25.
    assert(Parallelogram A C C' A').
      assert(Parallelogram C A A' C' \/ C = A /\ O = B /\ C' = A' /\ C = C').
        apply(plg_pseudo_trans C A O B C' A').
          apply plg_permut.
          apply plg_permut.
          assumption.
        assumption.
      induction H26.
        apply plg_comm2.
        assumption.
      spliter.
      subst C'.
      subst A'.
      tauto.
    apply plg_par in H26.
      spliter.
      induction H17.
        left.
        apply(par_trans _ _ A A'); Par.
      contradiction.
      intro.
      subst C.
      apply cong_identity in H1.
      subst B.
      tauto.
    intro.
    subst C'.
    apply plg_permut in H26.
    induction H19.
      induction H19.
        apply H19.
        exists O.
        split; Col.
        ColR.
      spliter.
      apply grid_ok.
      ColR.
    subst C.
    apply H21.
    exists B.
    split; Col.
Qed.

Lemma sum_iff_cong : forall A B C,
  Ar2 O E E' A B C -> (O <> C \/ B <> A) ->
 ((Cong O A B C /\ Cong O B A C) <-> Sum O E E' A B C).
Proof.
intros.
split.
intros.
apply cong_sum;intuition idtac.
intros.
apply sum_cong2.
assumption.
destruct H.
elim (eq_dec_points A O); intro.
subst.
right.
intro.
subst.
assert (T:= sum_O_O).
destruct H0.
apply H0.
eauto using sum_uniqueness.
intuition.
intuition.
Qed.

Lemma opp_comm : forall X Y, Opp O E E' X Y -> Opp O E E' Y X.
Proof.
    intros.
    unfold Opp in *.
    apply sum_comm.
    auto.
Qed.

Lemma opp_uniqueness :
 forall A MA1 MA2,
 Opp O E E' A MA1 ->
 Opp O E E' A MA2 ->
 MA1 = MA2.
Proof.
    intros.
    unfold Opp in *.
    apply sum_comm in H.
    apply sum_comm in H0.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=sum_uniquenessB O MA1 MA2 O H H0).
      assumption.
    apply sum_plg in H.
      apply sum_plg in H0.
        ex_and H A'.
        ex_and H2 C'.
        ex_and H0 A''.
        ex_and H3 C''.
        apply plg_to_parallelogram in H.
        apply plg_to_parallelogram in H0.
        apply plg_to_parallelogram in H2.
        apply plg_to_parallelogram in H3.
        assert(Parallelogram C' A' A'' C'' \/ C' = A' /\ A = O /\ C'' = A'' /\ C' = C'').
          apply(plg_pseudo_trans C' A' A O C'' A''); auto.
          apply plg_permut.
          apply plg_permut.
          auto.
        induction H4.
          assert(Parallelogram O MA1 C'' A'' \/ O = MA1 /\ C' = A' /\ A'' = C'' /\ O = A'').
            apply(plg_pseudo_trans O MA1 C' A' A'' C''); auto.
          induction H5.
            assert(Parallelogram O MA1 MA2 O \/ O = MA1 /\ C'' = A'' /\ O = MA2 /\ O = O).
              apply(plg_pseudo_trans O MA1 C'' A'' O MA2); auto.
              apply plg_permut.
              apply plg_permut.
              assumption.
            induction H6.
              unfold Parallelogram in H6.
              induction H6.
                unfold Parallelogram_strict in H6.
                spliter.
                unfold TS in H6.
                spliter.
                apply False_ind.
                apply H9.
                Col.
              unfold Parallelogram_flat in H6.
              spliter.
              apply cong_symmetry in H9.
              apply cong_identity in H9.
              auto.
            spliter.
            subst MA1.
            subst MA2.
            auto.
          spliter.
          subst MA1.
          subst C''.
          subst A''.
          subst C'.
          unfold Parallelogram in H0.
          induction H0.
            unfold Parallelogram_strict in H0.
            spliter.
            apply par_distincts in H5.
            tauto.
          unfold Parallelogram_flat in H0.
          spliter.
          apply cong_identity in H6.
          auto.
        spliter.
        contradiction.
      left; auto.
    left; auto.
Qed.

End Grid.

Lemma pj_uniqueness : forall O E E' A A' A'', ~Col O E E' -> Col O E A -> Col O E' A' -> Col O E' A'' -> Pj E E' A A' -> Pj E E' A A'' -> A' = A''.
Proof.
    intros.
    unfold Pj in *.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:= grid_not_par O E E' H).
      spliter.
      induction H3.
        apply False_ind.
        apply H7.
        apply par_symmetry.
        apply (par_col_par _ _ _ A'); Col.
      subst A'.
      induction H4.
        apply False_ind.
        apply H7.
        apply par_symmetry.
        apply (par_col_par _ _ _ A''); Col.
      auto.
    induction H3; induction H4.
      assert(Par A A' A A'').
        apply (par_trans _ _ E E'); Par.
      induction H6.
        apply False_ind.
        apply H6.
        exists A.
        split; Col.
      spliter.
      apply(l6_21 O E' A A'); Col.
      intro.
      apply H.
      ColR.
      auto.
      subst A''.
      apply False_ind.
      apply H.
      ColR.
      auto.
      subst A'.
      apply False_ind.
      apply H.
      ColR.
    congruence.
Qed.

Lemma pj_right_comm : forall A B C D, Pj A B C D -> Pj A B D C.
Proof.
    intros.
    unfold Pj in *.
    induction H.
      left.
      Par.
    right.
    auto.
Qed.

Lemma pj_left_comm : forall A B C D, Pj A B C D -> Pj B A C D.
Proof.
    intros.
    unfold Pj in *.
    induction H.
      left.
      Par.
    right.
    auto.
Qed.

Lemma pj_comm : forall A B C D, Pj A B C D -> Pj B A D C.
Proof.
    intros.
    apply pj_left_comm.
    apply pj_right_comm.
    auto.
Qed.

(** Lemma 14.13 *)
(** Parallel projection on the second axis preserves sums. *)

Lemma proj_preserves_sum :
 forall O E E' A B C A' B' C',
 Sum O E E' A B C ->
 Ar1 O E' A' B' C' ->
 Pj E E' A A' ->
 Pj E E' B B' ->
 Pj E E' C C' ->
 Sum O E' E A' B' C'.
Proof.
    intros.
    assert(HH:= H).
    unfold Sum in HH.
    spliter.
    ex_and H5 A0.
    ex_and H6 C0.
    unfold Ar2 in H4.
    spliter.
    assert(HH:= grid_not_par O E E' H4).
    unfold Ar1 in H0.
    spliter.
    induction(eq_dec_points A O).
      subst A.
      unfold Pj in H1.
      induction H1.
        apply False_ind.
        apply H15.
        apply par_symmetry. (* TODO ameliorier perm apply pour gerer les _ *)
        apply (par_col_par _ _ _ A');Col.
      subst A'.
      assert(B = C).
        apply (sum_O_B_eq O E E'); auto.
      subst C.
      assert(B' = C').
        apply (pj_uniqueness O E E' B); Col.
      subst C'.
      apply sum_O_B; Col.
    induction(eq_dec_points B O).
      subst B.
      unfold Pj in H2.
      induction H2.
        apply False_ind.
        apply H15.
        apply par_symmetry.
        apply (par_col_par _ _ _ B'); Col.
      subst B'.
      assert(A = C).
        apply (sum_A_O_eq O E E'); auto.
      subst C.
      assert(A' = C').
        apply (pj_uniqueness O E E' A); Col.
      subst C'.
      apply sum_A_O; Col.
    assert(A' <> O).
      intro.
      subst A'.
      unfold Pj in H1.
      induction H1.
        apply H13.
        apply par_symmetry.
        apply (par_col_par _ _ _ A);finish.
      contradiction.
    assert(B' <> O).
      intro.
      subst B'.
      unfold Pj in H2.
      induction H2.
        apply H13.
        apply par_symmetry.
        apply (par_col_par _ _ _ B); Par.
        Col.
      contradiction.
    unfold Sum.
    spliter.
    split.
      repeat split; Col.
    assert(HH:=plg_existence A O B' H22).
    ex_and HH D.
    exists A.
    exists D.
    assert(HP:= H26).
    apply plg_par in H26.
      spliter.
      repeat split; Col.
        apply pj_comm; auto.
        left.
        apply par_symmetry.
        apply(par_col_par _ _ _ B'); finish.
        left.
        apply par_symmetry.
        apply(par_col_par _ _ _ A); finish.
      assert(Parallelogram_flat O A C B).
        apply(sum_cong O E E' H4 A B C H).
        left; auto.
      assert(Parallelogram B' D C B \/ B' = D /\ A = O /\ B = C /\ B' = B).
        apply(plg_pseudo_trans B' D A O B C).
          apply plg_permut.
          apply plg_permut.
          auto.
        apply plg_comm2.
        right.
        auto.
      induction H29.
        apply plg_par in H29.
          spliter.
          induction H2.
            induction H3.
              assert(Par B B' C C').
                apply (par_trans _ _ E E'); Par.
              assert(Par C D C C').
                apply(par_trans _ _ B B'); Par.
              induction H32.
                apply False_ind.
                apply H32.
                exists C.
                split; Col.
              spliter.
              left.
              apply par_right_comm.
              apply (par_col_par _ _ _ C); Col; Par.
              intro.
              subst D.
              induction H29.
                apply H29.
                exists O.
                split; ColR.
              spliter.
              apply H25.
              apply(l6_21 O E E' O);sfinish.
            subst C'.
            left.
            apply (par_trans _ _ B B'); Par.
          subst B'.
          apply par_distincts in H30.
          tauto.
          intro.
          subst D.
          apply par_distincts in H26.
          tauto.
        intro.
        subst D.
        induction H27.
          apply H27.
          exists O.
          split; ColR.
        spliter.
        apply H4.
        apply (col_transitivity_1 _ A).
          auto.
          Col.
        apply (col_transitivity_1 _ B'); Col.
      spliter.
      contradiction.
      intro.
      subst.
      intuition.
    intuition.
Qed.

(** Lemma 14.14 *)
Lemma sum_assoc_1 : forall O E E' A B C AB BC ABC,
  Sum O E E' A B AB -> Sum O E E' B C BC -> Sum O E E' A BC ABC ->
  Sum O E E' AB C ABC.
Proof.
    intros.
    assert(HS1:=H).
    assert(HS2:=H0).
    assert(HS3:=H1).
    unfold Sum in H.
    unfold Sum in H0.
    unfold Sum in H1.
    spliter.
    assert(HA1:= H).
    assert(HA2:= H0).
    assert(HA3 := H1).
    unfold Ar2 in H.
    unfold Ar2 in H0.
    unfold Ar2 in H1.
    clear H2.
    clear H3.
    clear H4.
    spliter.
    clean_duplicated_hyps.
    induction (eq_dec_points A O).
      subst A.
      assert(HH:= sum_O_B_eq O E E' H B AB HS1).
      subst AB.
      assert(HH:= sum_O_B_eq O E E' H BC ABC HS3).
      subst BC.
      auto.
    induction (eq_dec_points B O).
      subst B.
      assert(HH:= sum_A_O_eq O E E' H A AB HS1).
      subst AB.
      assert(HH:= sum_O_B_eq O E E' H C BC HS2).
      subst BC.
      auto.
    induction (eq_dec_points C O).
      subst C.
      assert(HH:= sum_A_O_eq O E E' H B BC HS2).
      subst BC.
      assert(HH:=sum_uniqueness O E E' A B AB ABC HS1 HS3).
      subst AB.
      apply sum_A_O; Col.
    assert(HH:= grid_not_par O E E' H).
    spliter.
    apply sum_comm in HS1; auto.
    apply sum_comm in HS3; auto.
    assert(S1:=HS1).
    assert(S2:=HS2).
    assert(S3:=HS3).
    unfold Sum in HS1.
    unfold Sum in HS2.
    unfold Sum in HS3.
    spliter.
    ex_and H20 B1'.
    ex_and H21 A1.
    ex_and H18 B1''.
    ex_and H25 C1.
    ex_and H16 BC3'.
    ex_and H29 A3.
    assert(B1'=B1'').
      apply (pj_uniqueness O E E' B B1' B1''); Col.
    subst B1''.
    clean_duplicated_hyps.
    assert(HH:=sum_par_strict O E E' H B A AB B1' A1 H19 H1 H20 H21 H22 H23 H24).
    spliter.
    assert(Par_strict O E B1' A1).
      induction H25.
        auto.
      contradiction.
    clear H25.
    clear H22.
    assert(HH:=grid_not_par O E E' H).
    spliter.
    assert(exists ! P' : Tpoint, Proj AB P' O E' E E').
      apply(project_existence AB O E' E E' H37 H36).
      intro.
      apply H34.
      Par.
    ex_and H38 AB2'.
    unfold unique in H39.
    spliter.
    clear H39.
    unfold Proj in H38.
    spliter.
    clean_duplicated_hyps.
    assert(A <> AB).
      intro.
      subst AB.
      apply sum_A_B_B in S1.
        contradiction.
      auto.
    assert(ABC <> AB).
      intro.
      subst ABC.
      assert(HP := sum_uniquenessA O E E' H A BC B AB S3 S1).
      subst BC.
      apply sum_A_B_A in S2; auto.
    assert(HH:=plg_existence C O AB2' H2).
    ex_and HH C2.
    induction H42.
      assert(AB <> AB2').
        intro.
        subst AB2'.
        apply par_distincts in H35.
        tauto.
      assert(Pl:=H34).
      assert(O <> AB2').
        intro.
        subst AB2'.
        assert(HH:=plg_trivial C O H2).
        assert(HP:= plg_uniqueness C O O C C2 HH Pl).
        subst C2.
        induction H35.
          apply H35.
          exists E.
          split; Col.
        spliter.
        contradiction.
      apply plg_par in H34; auto.
      spliter.
      repeat split; Col.
      exists AB2'.
      exists C2.
      repeat split.
        left; Par.
        Col.
        left.
        apply (par_trans _ _ O C);Par.
        right.
        repeat split; Col.
        left.
        apply (par_trans _ _ O AB2'); Par.
        right.
        repeat split; Col.
      assert(Parallelogram O BC ABC A).
        right.
        apply(sum_cong O E E' H BC A ABC S3);auto.
      assert(Parallelogram O B AB A).
        right.
        apply(sum_cong O E E' H B A AB S1); auto.
      assert(Parallelogram O B BC C ).
        right.
        apply(sum_cong O E E' H B C BC); auto.
      assert( Parallelogram B AB ABC BC \/ B = AB /\ A = O /\ BC = ABC /\ B = BC).
        apply(plg_pseudo_trans B AB A O BC ABC).
          apply plg_permut.
          assumption.
        apply plg_permut.
        apply plg_permut.
        apply plg_permut.
        assumption.
      assert(Parallelogram B AB ABC BC).
        induction H43.
          assumption.
        spliter.
        contradiction.
      clear H43.
      assert(Parallelogram O C ABC AB \/ O = C /\ BC = B /\ AB = ABC /\ O = AB).
        apply(plg_pseudo_trans O C BC B AB ABC).
          apply plg_permut.
          apply plg_comm2.
          assumption.
        apply plg_permut.
        apply plg_permut.
        apply plg_permut.
        assumption.
      assert(Parallelogram O C ABC AB).
        induction H43.
          assumption.
        spliter.
        subst C.
        tauto.
      clear H43.
      assert(Parallelogram ABC AB AB2' C2 \/ ABC = AB /\ O = C /\ C2 = AB2' /\ ABC = C2).
        apply(plg_pseudo_trans ABC AB O C C2 AB2').
          apply plg_permut.
          apply plg_permut.
          assumption.
        apply plg_comm2.
        assumption.
      assert(Parallelogram ABC AB AB2' C2).
        induction H43.
          assumption.
        spliter.
        subst C.
        tauto.
      clear H43.
      apply plg_par in H46; auto.
      spliter.
      left.
      apply(par_trans _ _ AB AB2'); Par.
    subst AB2'.
    assert(AB = O).
      apply(l6_21 O E E' O); Col.
    subst AB.
    assert(HH:= plg_trivial C O H2).
    assert(Hp:= plg_uniqueness C O O C C2 HH H34).
    subst C2.
    assert(Parallelogram_flat O B BC C).
      apply(sum_cong O E E' H B C BC);auto.
    assert(Parallelogram_flat O BC ABC A).
      apply(sum_cong O E E' H BC A ABC);auto.
    assert(Parallelogram_flat O B O A).
      apply(sum_cong O E E' H B A O); auto.
    assert(Parallelogram BC C A O \/ BC = C /\ O = B /\ O = A /\ BC = O).
      apply(plg_pseudo_trans BC C O B O A).
        apply plg_permut.
        apply plg_permut.
        right; assumption.
      right; assumption.
    assert(Parallelogram BC C A O).
      induction H38.
        assumption.
      spliter.
      subst A.
      tauto.
    clear H38.
    assert(Parallelogram O BC ABC A).
      right; assumption.
    apply plg_permut in H38.
    apply plg_permut in H38.
    apply plg_permut in H38.
    apply plg_permut in H39.
    apply plg_permut in H39.
    assert(HP:=plg_uniqueness A O BC C ABC H39 H38).
    subst ABC.
    apply sum_O_B; Col.
Qed.

Lemma sum_assoc_2 : forall O E E' A B C AB BC ABC,
 Sum O E E' A B AB ->
 Sum O E E' B C BC ->
 Sum O E E' AB C ABC ->
 Sum O E E' A BC ABC.
Proof.
    intros.
    assert(HS1:=H).
    assert(HS2:=H0).
    assert(HS3:=H1).
    unfold Sum in H.
    unfold Sum in H0.
    unfold Sum in H1.
    spliter.
    unfold Ar2 in H.
    spliter.
    clean_duplicated_hyps.
    apply sum_comm; auto.
    apply(sum_assoc_1 O E E' C B A BC AB ABC ).
      apply sum_comm; auto.
      apply sum_comm; auto.
    apply sum_comm; auto.
Qed.

Lemma sum_assoc : forall O E E' A B C AB BC ABC,
  Sum O E E' A B AB ->
  Sum O E E' B C BC ->
  (Sum O E E' A BC ABC <-> Sum O E E' AB C ABC).
Proof.
    intros.
    split; intro.
      apply(sum_assoc_1 O E E' A B C AB BC ABC); auto.
    apply(sum_assoc_2 O E E' A B C AB BC ABC); auto.
Qed.

(** Lemma 14.15 *)
(** The choice of E' does not affect sum. *)
Lemma sum_y_axis_change :
 forall O E E' E'' A B C,
  Sum O E E' A B C ->
  ~ Col O E E'' ->
  Sum O E E'' A B C.
Proof.
    intros.
    assert(HS:= H).
    assert(Ar2 O E E' A B C).
      unfold Sum in H.
      tauto.
    assert(HA:=H1).
    unfold Ar2 in H1.
    spliter.
    assert(HH:=grid_not_par O E E' H1).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      apply sum_O_B_eq in H; Col.
      subst C.
      apply sum_O_B; Col.
    induction(eq_dec_points B O).
      subst B.
      apply sum_A_O_eq in H; Col.
      subst C.
      apply sum_A_O; Col.
    apply sum_plg in H; auto.
    ex_and H A'.
    ex_and H13 C'.
    assert(exists ! P' : Tpoint, Proj A P' O E'' E E'').
      apply(project_existence A O E'' E E''); intro; try (subst E''; apply H0; Col).
      induction H14.
        apply H14.
        exists E''.
        split; Col.
      spliter.
      apply H0.
      Col.
    ex_and H14 A''.
    unfold unique in H15.
    spliter.
    clear H15.
    unfold Proj in H14.
    spliter.
    assert(Par A A'' E E'').
      induction H18; auto.
      subst A''.
      apply False_ind.
      apply H0.
      ColR.
    clear H18.
    assert(HH:= plg_existence B O A'' H12).
    ex_and HH C''.
    apply plg_to_parallelogram in H.
    apply plg_to_parallelogram in H13.
    assert(A'' <> O).
      intro.
      subst A''.
      induction H19.
        apply H19.
        exists E.
        split; Col.
      spliter.
      contradiction.
    repeat split; Col.
    exists A''.
    exists C''.
    repeat split.
      left.
      Par.
      Col.
      apply plg_par in H18; auto.
      spliter.
      left.
      apply par_symmetry.
      apply (par_col_par _ _ _ B); Par; Col.
      apply plg_par in H18; auto.
      spliter.
      left.
      apply par_symmetry.
      apply (par_col_par _ _ _ A''); Par; Col.
    left.
    assert(Parallelogram_flat O A C B).
      apply(sum_cong O E E' H1 A B C HS).
      left; auto.
    assert(Parallelogram O A C B).
      right; auto.
    assert(Parallelogram C'' A'' A C \/ C'' = A'' /\ O = B /\ C = A /\ C'' = C).
      apply(plg_pseudo_trans C'' A'' O B C A).
        apply plg_comm2.
        apply plg_permut.
        apply plg_permut.
        assumption.
      apply plg_permut in H22.
      apply plg_comm2.
      apply plg_permut.
      apply plg_permut.
      assumption.
    assert(Parallelogram C'' A'' A C).
      induction H23.
        assumption.
      spliter.
      subst B.
      tauto.
    clear H23.
    assert(A <> C).
      intro.
      subst C.
      assert(Parallelogram O A A O).
        apply(plg_trivial O A); auto.
      assert(HH:=plg_uniqueness O A A O B H23 H22).
      subst B.
      tauto.
    assert(A <> A'').
      intro.
      subst A''.
      apply par_distincts in H19.
      tauto.
    assert(A'' <> C'').
      intro.
      subst C''.
      assert(Parallelogram A'' A'' A A).
        apply(plg_trivial1); auto.
      assert(HH:= plg_uniqueness A'' A'' A A C H26 H24).
      contradiction.
    apply plg_par in H24; auto.
    spliter.
    apply(par_trans _ _ A'' A); Par.
Qed.

(** Lemma 14.16 *)
(** The choice of E does not affect sum. *)
Lemma sum_x_axis_unit_change :
 forall O E E' U A B C,
 Sum O E E' A B C ->
 Col O E U ->
 U <> O ->
 Sum O U E' A B C.
Proof.
    intros.
    induction (eq_dec_points U E).
      subst U.
      assumption.
    assert(HS:= H).
    assert(Ar2 O E E' A B C).
      unfold Sum in H.
      tauto.
    assert(HA:=H3).
    unfold Ar2 in H3.
    spliter.
    assert(HH:=grid_not_par O E E' H3).
    spliter.
    assert(~Col O U E').
      intro.
      apply H3.
      ColR.
    assert(HH:=grid_not_par O U E' H13).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      apply sum_O_B_eq in H; Col.
      subst C.
      apply sum_O_B; Col.
      ColR.
    induction(eq_dec_points B O).
      subst B.
      apply sum_A_O_eq in H; Col.
      subst C.
      apply sum_A_O; Col.
      ColR.
    apply sum_plg in H; auto.
    ex_and H A'.
    ex_and H22 C'.
    apply plg_to_parallelogram in H.
    apply plg_to_parallelogram in H22.
    assert(Ar2 O U E' A B C).
      repeat split ; auto; ColR.
    assert(HB:= H23).
    unfold Ar2 in H23.
    spliter.
    clean_duplicated_hyps.
    assert(exists ! P' : Tpoint, Proj A P' O E' U E').
      apply(project_existence A O E' U E' H19 H11 ).
      intro.
      apply H16.
      Par.
    ex_and H18 A''.
    unfold unique in H23.
    spliter.
    clear H23.
    unfold Proj in H18.
    spliter.
    clean_duplicated_hyps.
    assert(Par A A'' U E').
      induction H29.
        assumption.
      subst A''.
      apply False_ind.
      apply H3.
      ColR.
    clear H29.
    assert(HH:= plg_existence B O A'' H21).
    ex_and HH C''.
    assert(O <> A'').
      intro.
      subst A''.
      assert(HH:=plg_trivial B O H21).
      assert(B = C'').
        apply (plg_uniqueness B O O B C''); auto.
      subst C''.
      induction H18.
        apply H18.
        exists U.
        split; Col.
      spliter.
      apply H3.
      ColR.
    assert(HP1:=H23).
    apply plg_par in H23; auto.
    spliter.
    repeat split; auto.
    exists A''.
    exists C''.
    repeat split.
      left.
      Par.
      Col.
      left.
      assert(Par O U B O).
        right.
        repeat split; Col.
      apply (par_trans _ _ B O); Par.
      left.
      assert(Par O E' O A'').
        right.
        repeat split; Col.
      apply(par_trans _ _ O A''); Par.
    assert(Parallelogram_flat O A C B).
      apply(sum_cong O E E' H3 A B C HS); auto.
    assert(Parallelogram O A C B).
      right.
      assumption.
    assert(Parallelogram A C C'' A'' \/ A = C /\ B = O /\ A'' = C'' /\ A = A'').
      apply(plg_pseudo_trans A C B O A'' C'').
        apply plg_permut.
        assumption.
      assumption.
    assert(Parallelogram A C C'' A'').
      induction H32.
        assumption.
      spliter.
      contradiction.
    clear H32.
    apply plg_par in H33.
      left.
      spliter.
      apply(par_trans _ _ A A''); Par.
      intro.
      subst C.
      apply sum_B_null in HS.
        contradiction.
      auto.
    intro.
    subst C''.
    induction H23.
      apply H23.
      exists C.
      split; Col.
      ColR.
    spliter.
    apply H3.
    ColR.
Qed.

Lemma change_grid_sum_0 :
 forall O E E' A B C O' A' B' C',
  Par_strict O E O' E' ->
  Ar1 O E A B C ->
  Ar1 O' E' A' B' C' ->
  Pj O O' E E' ->
  Pj O O' A A' ->
  Pj O O' B B' ->
  Pj O O' C C' ->
  Sum O E E' A B C ->
  A = O ->
  Sum O' E' E A' B' C'.
Proof.
    intros.
    assert(HS:= H6).
    induction H6.
    ex_and H8 A1.
    ex_and H9 C1.
    unfold Ar1 in *.
    unfold Ar2 in H6.
    spliter.
    subst A.
    clean_duplicated_hyps.
    assert(A' = O').
      apply(l6_21 O' E' O O');Col.
        intro.
        apply H.
        exists O.
        split; Col.
        intro.
        apply H.
        subst O'.
        exists O.
        split; Col.
      unfold Pj in H3.
      induction H3.
        induction H3.
          apply False_ind.
          apply H3.
          exists O.
          split; Col.
        spliter.
        Col.
      subst A'.
      Col.
    subst A'.
    assert(Sum O E E' O B B).
      apply sum_O_B. assumption. Col.
    unfold Sum in H7.
      assert(B = C).
        apply(sum_uniqueness O E E' O B); auto.
      subst C.
      assert(B' = C').
        apply(l6_21 O' E' B B'); Col.
          intro.
          apply H.
          exists B.
          split; Col.
          intro.
          subst B'.
          apply H.
          exists B.
          split; Col.
        induction H5.
          induction H4.
            assert(Par B C' B B').
              apply(par_trans _ _ O O'); Par.
            induction H13.
              apply False_ind.
              apply H13.
              exists B.
              split; Col.
            spliter.
            Col.
          subst B'.
          Col.
        subst C'.
        Col.
      subst C'.
      apply sum_O_B;Col.
      assert_ncols; Col.
Qed.

Lemma change_grid_sum :
 forall O E E' A B C O' A' B' C',
  Par_strict O E O' E' ->
  Ar1 O E A B C ->
  Ar1 O' E' A' B' C' ->
  Pj O O' E E' ->
  Pj O O' A A' ->
  Pj O O' B B' ->
  Pj O O' C C' ->
  Sum O E E' A B C ->
  Sum O' E' E A' B' C'.
Proof.
    intros.
    induction(eq_dec_points A O).
      subst A.
      apply(change_grid_sum_0 O E E' O B C); auto.
    assert(HS:= H6).
    induction H6.
    ex_and H8 A1.
    ex_and H9 C1.
    unfold Ar1 in *.
    unfold Ar2 in H6.
    spliter.
    assert(HG:=grid_not_par O E E' H6).
    spliter.
    assert(~Col O' E' E).
      intro.
      apply H.
      exists E.
      split; Col.
    assert(HG:=grid_not_par O' E' E H28).
    spliter.
    clean_duplicated_hyps.
    induction(eq_dec_points B O).
      subst B.
      apply sum_comm; Col.
      apply sum_comm in HS; Col.
      apply(change_grid_sum_0 O E E' O A C); auto.
        repeat split; auto.
      repeat split; auto.
    assert(A' <> O).
      intro.
      subst A'.
      induction H3.
        induction H3.
          apply H3.
          exists O.
          split; Col.
        spliter.
        apply H.
        exists O'.
        split; Col.
        ColR.
      contradiction.
    assert(~Col O A A').
      intro.
      apply H.
      exists A'.
      split; Col.
      ColR.
    assert(A' <> O').
      intro.
      subst A'.
      induction H3.
        induction H3.
          apply H3.
          exists O'.
          split; Col.
        spliter.
        contradiction.
      subst A.
      apply H15.
      Col.
    assert(Parallelogram_flat O A C B).
      apply(sum_cong O E E' H6 A B C HS).
      left.
      auto.
    unfold Parallelogram_flat in H32.
    spliter.
    assert(Proj O O' O' E' E E').
      unfold Proj.
      repeat split; Col.
        intro.
        apply H29.
        Par.
      induction H2.
        left; Par.
      subst E'.
      tauto.
    assert(Proj A A' O' E' E E').
      unfold Proj.
      repeat split; Col.
        intro.
        apply H29.
        Par.
      induction H3.
        left.
        induction H2.
          apply (par_trans _ _ O O'); Par.
        subst E'.
        tauto.
      subst A'.
      right.
      auto.
    assert(Proj C C' O' E' E E').
      unfold Proj.
      repeat split; Col.
        intro.
        apply H29.
        Par.
      induction H5.
        left.
        induction H2.
          apply (par_trans _ _ O O'); Par.
        subst E'.
        tauto.
      right.
      auto.
    assert(Proj B B' O' E' E E').
      unfold Proj.
      repeat split; Col.
        intro.
        apply H29.
        Par.
      induction H4.
        left.
        induction H2.
          apply (par_trans _ _ O O'); Par.
        subst E'.
        tauto.
      right.
      auto.
    assert(EqV O A B C).
      unfold EqV.
      left.
      right.
      apply plgf_permut.
      unfold Parallelogram_flat.
      repeat split; Col; Cong.
        ColR.
      induction H38.
        right.
        auto.
      left.
      auto.
    assert(HH:=project_preserves_eqv O A B C O' A' B' C' O' E' E E' H43 H39 H40 H42 H41).
    unfold EqV in HH.
    induction HH.
      assert(Parallelogram_flat O' A' C' B').
        induction H44.
          induction H44.
          unfold TS in H44.
          spliter.
          apply False_ind.
          apply H47.
          ColR.
        assumption.
      unfold Parallelogram_flat in H45.
      spliter.
      apply cong_sum; auto.
        induction H49.
          left; auto.
        right; auto.
        repeat split; Col.
        Cong.
      Cong.
    spliter.
    subst A'.
    tauto.
Qed.

Lemma double_null_null : forall O E E' A, Sum O E E' A A O -> A = O.
Proof.
    intros.
    induction (eq_dec_points A O).
      assumption.
    assert(HS:= H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(Parallelogram_flat O A O A).
      apply(sum_cong O E E' H A A O HS).
      left; auto.
    unfold Parallelogram_flat in H5.
    tauto.
Qed.

Lemma not_null_double_not_null : forall O E E' A C, Sum O E E' A A C -> A <> O -> C <> O.
Proof.
    intros.
    intro.
    subst C.
    apply double_null_null in H.
    contradiction.
Qed.

Lemma double_not_null_not_nul : forall O E E' A C, Sum O E E' A A C -> C <> O -> A <> O.
Proof.
    intros.
    intro.
    subst A.
    assert(HS:= H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HH:= sum_O_O O E E' H).
    apply H0.
    apply (sum_uniqueness O E E' O O); assumption.
Qed.

Lemma diff_ar2 : forall O E E' A B AMB, Diff O E E' A B AMB -> Ar2 O E E' A B AMB.
Proof.
    intros.
    unfold Diff in H.
    ex_and H MA.
    unfold Opp in H.
    unfold Sum in *.
    spliter.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma diff_null : forall O E E' A, ~Col O E E' -> Col O E A -> Diff O E E' A A O.
Proof.
    intros.
    unfold Diff.
    assert(Hop:=opp_exists O E E' H A H0).
    ex_and Hop MB.
    exists MB.
    split; auto.
    unfold Opp in H1.
    apply sum_comm; auto.
Qed.

Lemma diff_exists : forall O E E' A B, ~Col O E E' -> Col O E A -> Col O E B ->  exists D, Diff O E E' A B D.
Proof.
    intros.
    assert(Hop:=opp_exists O E E' H B H1).
    ex_and Hop MB.
    assert(Col O E MB).
      unfold Opp in H2.
      unfold Sum in H2.
      spliter.
      unfold Ar2 in H2.
      tauto.
    assert(HS:=sum_exists O E E' H A MB H0 H3).
    ex_and HS C.
    exists C.
    unfold Diff.
    exists MB.
    split; assumption.
Qed.

Lemma diff_uniqueness : forall O E E' A B D1 D2, Diff O E E' A B D1 -> Diff O E E' A B D2 -> D1 = D2.
Proof.
    intros.
    assert(Ar2 O E E' A B D1).
      apply (diff_ar2); assumption.
    unfold Ar2 in H1.
    spliter.
    unfold Diff in *.
    ex_and H MB1.
    ex_and H0 MB2.
    assert(MB1 = MB2).
      apply (opp_uniqueness O E E' H1 B); assumption.
    subst MB2.
    apply(sum_uniqueness O E E'  A MB1); assumption.
Qed.

Lemma sum_ar2 : forall O E E' A B C, Sum O E E' A B C -> Ar2 O E E' A B C.
Proof.
    intros.
    unfold Sum in H.
    tauto.
Qed.

Lemma diff_A_O : forall O E E' A, ~Col O E E' -> Col O E A ->  Diff O E E' A O A.
Proof.
    intros.
    unfold Diff.
    exists O.
    split.
      unfold Opp.
      apply sum_O_O; auto.
    apply sum_A_O;auto.
Qed.

Lemma diff_O_A : forall O E E' A mA,
  ~ Col O E E' -> Opp O E E' A mA -> Diff O E E' O A mA.
Proof.
    intros.
    assert (Col O E A) by (unfold Opp, Sum, Ar2 in *; spliter; auto).
    assert (Col O E mA) by (unfold Opp, Sum, Ar2 in *; spliter; auto).
    revert H0; revert H1; revert H2; intros.
    unfold Diff.
    exists mA.
    split.
      assumption.
    apply sum_O_B; auto.
Qed.

Lemma diff_O_A_opp : forall O E E' A mA, Diff O E E' O A mA -> Opp O E E' A mA.
Proof.
    intros.
    assert(Ar2 O E E' O A mA).
      apply diff_ar2;auto.
    unfold Diff in H.
    ex_and H A'.
    assert(Ar2 O E E' O A' mA).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(Sum O E E' O A' A').
      apply (sum_O_B); auto.
    assert(mA = A').
      apply(sum_uniqueness O E E' O A'); auto.
    subst A'.
    assumption.
Qed.

Lemma diff_uniquenessA : forall O E E' A A' B C,
  Diff O E E' A B C -> Diff O E E' A' B C -> A = A'.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply diff_ar2; auto.
    assert(Ar2 O E E' A' B C).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold Diff in *.
    ex_and H mB.
    ex_and H0 mB'.
    assert(mB = mB').
      apply(opp_uniqueness O E E' H1 B); auto.
    subst mB'.
    apply (sum_uniquenessA O E E' H1 mB A A' C); auto.
Qed.

Lemma diff_uniquenessB : forall O E E' A B B' C,
  Diff O E E' A B C -> Diff O E E' A B' C -> B = B'.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply diff_ar2; auto.
    assert(Ar2 O E E' A B' C).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold Diff in *.
    ex_and H mB.
    ex_and H0 mB'.
    assert(mB = mB').
      apply (sum_uniquenessA O E E' H1 A mB mB' C); apply sum_comm; auto.
    subst mB'.
    apply (opp_uniqueness O E E' H1 mB); apply opp_comm; auto.
Qed.

Lemma diff_null_eq : forall O E E' A B, Diff O E E' A B O -> A = B.
Proof.
    intros.
    assert(Ar2 O E E' A B O).
      apply diff_ar2; auto.
    unfold Ar2 in H0.
    spliter.
    clear H3.
    assert(Diff O E E' A A O).
      apply diff_null; Col.
    apply (diff_uniquenessB O E E' A _ _ O); auto.
Qed.

Lemma midpoint_opp: forall O E E' A B,
  Ar2 O E E' O A B -> Midpoint O A B -> Opp O E E' A B.
Proof.
    intros.
    unfold Ar2.
    unfold Ar2 in H.
    spliter.
    clear H1.
    unfold Midpoint in H0.
    spliter.
    induction (eq_dec_points A B).
      subst B.
      apply between_identity in H0.
      subst A.
      apply opp0; auto.
    unfold Opp.
    apply cong_sum; auto.
      unfold Ar2.
      repeat split; Col.
      Cong.
    Cong.
Qed.

Lemma sum_diff : forall O E E' A B S, Sum O E E' A B S -> Diff O E E' S A B.
Proof.
    intros.
    assert(Ar2 O E E' A B S).
      apply sum_ar2; auto.
    unfold Ar2 in H0.
    spliter.
    assert(HH:=opp_exists O E E' H0 A H1).
    ex_and HH mA.
    exists mA.
    split; auto.
    unfold Opp in H4.
    assert(Ar2 O E E' mA A O).
      apply sum_ar2; auto.
    unfold Ar2 in H5.
    spliter.
    clean_duplicated_hyps.
    clear H8.
    induction(eq_dec_points A O).
      subst A.
      assert(B = S).
        apply (sum_uniqueness O E E' O B); auto.
        apply sum_O_B; auto.
      subst S.
      assert(mA = O).
        apply (sum_uniqueness O E E' mA O); auto.
        apply sum_A_O; auto.
      subst mA.
      apply sum_A_O; auto.
    induction(eq_dec_points B O).
      subst B.
      assert(A = S).
        apply (sum_uniqueness O E E' A O); auto.
        apply sum_A_O; auto.
      subst S.
      apply sum_comm; auto.
    apply sum_cong in H; auto.
    apply sum_cong in H4; auto.
    assert(E <> O).
      intro.
      subst E.
      apply H0.
      Col.
    assert(Parallelogram O mA B S \/ O = mA /\ O = A /\ S = B /\ O = S).
      apply(plg_pseudo_trans O mA O A S B); auto.
        right; auto.
      right; auto.
    induction H9.
      induction H9.
        apply False_ind.
        unfold Parallelogram_strict in H9.
        spliter.
        unfold TS in H9.
        spliter.
        apply H12.
        ColR.
      unfold Parallelogram_flat in H.
      unfold Parallelogram_flat in H4.
      unfold Parallelogram_flat in H9.
      spliter.
      apply cong_sum; auto.
        repeat split; Col.
        Cong.
      Cong.
    spliter.
    subst A.
    tauto.
Qed.

Lemma diff_sum : forall O E E' A B S, Diff O E E' S A B -> Sum O E E' A B S.
Proof.
intros.
assert(Ar2 O E E' S A B).
apply diff_ar2; auto.
unfold Ar2 in H0.
spliter.
induction(eq_dec_points A O).
subst A.
assert(HH:=diff_A_O O E E' S H0 H1).
assert(S = B).
apply (diff_uniqueness O E E' S O); auto.
subst B.
apply sum_O_B; auto.
unfold Diff in H.
ex_and H mA.
assert(mA <> O).
intro.
subst mA.
assert(HH:=opp0 O E E' H0).
apply H4.
apply (opp_uniqueness O E E' H0 O); auto.
apply opp_comm; auto.
unfold Opp in H.
induction(eq_dec_points S O).
subst S.
assert(mA = B).
apply (sum_O_B_eq O E E'); auto.
subst mA.
apply sum_comm; auto.
apply sum_cong in H; auto.
apply sum_cong in H5; auto.
assert(E <> O).
intro.
subst E.
apply H0.
Col.
assert(Parallelogram O A S B \/ O = A /\ O = mA /\ B = S /\ O = B).
apply(plg_pseudo_trans O A O mA B S).
apply plg_permut.
apply plg_permut.
right.
assumption.
apply plg_comm2.
apply plg_permut.
apply plg_permut.
apply plg_permut.
right.
auto.
induction H9.
induction H9.
apply False_ind.
unfold Parallelogram_strict in H9.
spliter.
unfold TS in H9.
spliter.
apply H12.
ColR.
unfold Parallelogram_flat in H.
unfold Parallelogram_flat in H5.
unfold Parallelogram_flat in H9.
spliter.
apply cong_sum; Cong.
repeat split; Col.
spliter.
subst A.
tauto.
Qed.

Lemma diff_opp : forall O E E' A B AmB BmA,
  Diff O E E' A B AmB -> Diff O E E' B A BmA -> Opp O E E' AmB BmA.
Proof.
    intros.
    assert(Ar2 O E E' A B AmB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' B A BmA).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    apply diff_sum in H.
    apply diff_sum in H0.
    induction(eq_dec_points A O).
      subst A.
      assert(BmA = B).
        apply(sum_O_B_eq O E E'); auto.
      subst BmA.
      unfold Opp.
      assumption.
    induction(eq_dec_points B O).
      subst B.
      assert(AmB = A).
        apply(sum_O_B_eq O E E'); auto.
      subst AmB.
      unfold Opp.
      apply sum_comm; auto.
    apply sum_cong in H0; auto.
    apply sum_cong in H; auto.
    assert(Parallelogram A O BmA B).
      apply plg_comm2.
      right.
      assumption.
    apply plg_permut in H4.
    apply plg_permut in H4.
    apply plg_permut in H4.
    assert(Parallelogram AmB O BmA O \/ AmB = O /\ B = A /\ O = BmA /\ AmB = O).
      apply(plg_pseudo_trans AmB O  B A O BmA).
        apply plg_permut.
        apply plg_permut.
        apply plg_permut.
        right; assumption.
      assumption.
    assert(E <> O).
      intro.
      subst E.
      apply H1.
      Col.
    induction H9.
      induction H9.
        apply False_ind.
        unfold Parallelogram_strict in H9.
        unfold TS in H9.
        spliter.
        apply H13.
        ColR.
      unfold Parallelogram_flat in H.
      unfold Parallelogram_flat in H0.
      unfold Parallelogram_flat in H9.
      spliter.
      unfold Opp.
      apply cong_sum; Cong.
        right.
        intro.
        subst BmA.
        tauto.
      repeat split; Col.
    spliter.
    subst AmB.
    subst BmA.
    unfold Opp.
    apply sum_O_O; auto.
Qed.

Lemma sum_stable : forall O E E' A B C S1 S2 , A = B -> Sum O E E' A C S1 -> Sum O E E' B C S2 -> S1 = S2.
Proof.
    intros.
    subst B.
    apply (sum_uniqueness O E E' A C); auto.
Qed.

Lemma diff_stable : forall O E E' A B C D1 D2 , A = B -> Diff O E E' A C D1 -> Diff O E E' B C D2 -> D1 = D2.
Proof.
    intros.
    subst B.
    apply(diff_uniqueness O E E' A C); auto.
Qed.

Lemma plg_to_sum : forall O E E' A B C, Ar2 O E E' A B C ->Parallelogram_flat O A C B -> Sum O E E' A B C.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B.
      unfold Parallelogram_flat in H0.
      spliter.
      assert(O = C \/ Midpoint A O C).
        apply(l7_20 A O C H0).
        Cong.
      induction H5.
        subst C.
        tauto.
      apply cong_sum; auto.
        unfold Ar2 in H.
        tauto.
        unfold Midpoint in H5.
        tauto.
      unfold Midpoint in H5.
      tauto.
    unfold Ar2 in H.
    unfold Parallelogram_flat in H0.
    spliter.
    apply cong_sum; auto.
      repeat split; auto.
      Cong.
    Cong.
Qed.

Lemma opp_midpoint :
 forall O E E' A MA,
 Opp O E E' A MA ->
 Midpoint O A MA.
Proof.
    intros.
    unfold Opp in H.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    induction (eq_dec_points A O).
      subst A.
      assert(HH:= sum_A_O_eq O E E' H MA O HS).
      subst MA.
      unfold Midpoint.
      split; Cong.
      apply between_trivial.
    assert(Parallelogram_flat O MA O A).
      apply(sum_cong O E E' H MA A O HS).
      tauto.
    unfold Parallelogram_flat in H5.
    spliter.
    assert(A = MA \/ Midpoint O A MA).
      apply(l7_20 O A MA).
        Col.
      Cong.
    induction H10.
      subst MA.
      tauto.
    assumption.
Qed.

Lemma diff_to_plg : forall O E E' A B dBA, A <> O \/ B <> O -> Diff O E E' B A dBA -> Parallelogram_flat O A B dBA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    unfold Ar2 in H1.
    spliter.
    apply diff_sum in H0.
    induction(eq_dec_points A O).
      subst A.
      assert(dBA = B).
        apply(sum_O_B_eq O E E'); auto.
      subst dBA.
      apply plgf_permut.
      apply plgf_trivial.
      induction H; tauto.
    assert(E <> O).
      intro.
      subst E.
      apply H1.
      Col.
    induction(eq_dec_points B O).
      subst B.
      assert(Opp O E E' dBA A).
        unfold Opp.
        auto.
      apply opp_midpoint in H7.
      unfold Midpoint in H7.
      spliter.
      unfold Parallelogram_flat.
      repeat split; try ColR.
        Cong.
        Cong.
    apply sum_cong in H0; auto.
Qed.

Lemma sum3_col : forall O E E' A B C S, sum3 O E E' A B C S -> ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S.
Proof.
    intros.
    unfold sum3 in H.
    ex_and H AB.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB C S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma sum3_permut : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' C A B S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S).
      apply sum3_col; auto.
    spliter.
    unfold sum3 in H.
    ex_and H AB.
    assert(HH:= sum_exists O E E' H0 A C H1 H3).
    ex_and HH AC.
    unfold sum3.
    exists AC.
    split.
      apply sum_comm; auto.
    apply sum_comm in H5; auto.
    apply sum_comm in H6; auto.
    assert(HH:=sum_assoc O E E' C A B AC AB S H6 H).
    destruct HH.
    apply H7; auto.
Qed.

Lemma sum3_comm_1_2 : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' B A C S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S).
      apply sum3_col; auto.
    spliter.
    unfold sum3 in H.
    ex_and H AB.
    unfold sum3.
    exists AB.
    split.
      apply sum_comm; auto.
    auto.
Qed.

Lemma sum3_comm_2_3 : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' A C B S.
Proof.
    intros.
    apply sum3_permut in H.
    apply sum3_comm_1_2 in H.
    assumption.
Qed.

Lemma sum3_exists : forall O E E' A B C, Ar2 O E E' A B C -> exists S, sum3 O E E' A B C S.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=sum_exists O E E' H A B H0 H1).
    ex_and HH AB.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    unfold Ar2 in H4.
    spliter.
    clean_duplicated_hyps.
    assert(HH:=sum_exists O E E' H AB C H7 H2).
    ex_and HH ABC.
    exists ABC.
    unfold sum3.
    exists AB.
    split; auto.
Qed.

Lemma sum3_uniqueness : forall O E E' A B C S1 S2, sum3 O E E' A B C S1 -> sum3 O E E' A B C S2 -> S1 = S2.
Proof.
    intros.
    unfold sum3 in H.
    unfold sum3 in H0.
    ex_and H AB1.
    ex_and H0 AB2.
    assert(AB1 = AB2).
      apply(sum_uniqueness O E E' A B); auto.
    subst AB2.
    apply (sum_uniqueness O E E' AB1 C); auto.
Qed.

Lemma sum4_col : forall O E E' A B C D S, Sum4 O E E' A B C D S ->  ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S.
Proof.
    intros.
    unfold Sum4 in H.
    ex_and H ABC.
    assert(HH:=sum3_col O E E' A B C ABC H).
    assert(Ar2 O E E' ABC D S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma sum22_col : forall O E E' A B C D S, sum22 O E E' A B C D S ->  ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S.
Proof.
    intros.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H0 CD.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma sum_to_sum3 : forall O E E' A B AB X S, Sum O E E' A B AB -> Sum O E E' AB X S -> sum3 O E E' A B X S.
Proof.
    intros.
    unfold sum3.
    exists AB.
    split; auto.
Qed.

Lemma sum3_to_sum4 : forall O E E' A B C X ABC S , sum3 O E E' A B C ABC -> Sum O E E' ABC X S -> Sum4 O E E' A B C X S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E ABC).
      apply sum3_col; auto.
    assert(Ar2 O E E' ABC X S).
      apply sum_ar2; auto.
    unfold Ar2 in H2.
    spliter.
    clean_duplicated_hyps.
    unfold Sum4.
    exists ABC.
    split; auto.
Qed.

Lemma sum_A_exists : forall O E E' A AB, Ar2 O E E' A AB O -> exists B, Sum O E E' A B AB.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=diff_exists O E E' AB A H H1 H0).
    ex_and HH B.
    exists B.
    apply diff_sum in H3.
    assumption.
Qed.

Lemma sum_B_exists : forall O E E' B AB, Ar2 O E E' B AB O -> exists A, Sum O E E' A B AB.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=diff_exists O E E' AB B H H1 H0).
    ex_and HH A.
    exists A.
    apply diff_sum in H3.
    apply sum_comm; auto.
Qed.

Lemma sum4_equiv : forall O E E' A B C D S, Sum4 O E E' A B C D S <-> sum22 O E E' A B C D S.
Proof.
    intros.
    split.
      intro.
      assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
        apply sum4_col; auto.
      spliter.
      assert(HS1:= sum_exists O E E' H0 A B H1 H2).
      assert(HS2:= sum_exists O E E' H0 C D H3 H4).
      ex_and HS1 AB.
      ex_and HS2 CD.
      unfold sum22.
      exists AB.
      exists CD.
      assert(Ar2 O E E' A B AB).
        apply sum_ar2; auto.
      assert(Ar2 O E E' C D CD).
        apply sum_ar2; auto.
      unfold Ar2 in *.
      spliter.
      clean_duplicated_hyps.
      split; auto.
      split; auto.
      unfold Sum4 in H.
      ex_and H ABC.
      unfold sum3 in H.
      ex_and H AB'.
      assert(AB' = AB).
        apply(sum_uniqueness O E E' A B); auto.
      subst AB'.
      assert(HH:= sum_assoc O E E' AB C D ABC CD S H9 H7).
      destruct HH.
      apply H11.
      assumption.
    intro.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H0 CD.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold Sum4.
    assert(HS:=sum_exists O E E' H2 AB C H13 H8).
    ex_and HS ABC.
    exists ABC.
    split.
      unfold sum3.
      exists AB.
      split; auto.
    assert(HH:= sum_assoc O E E' AB C D ABC CD S H3 H0).
    destruct HH.
    apply H4.
    assumption.
Qed.

Lemma sum4_permut: forall O E E' A B C D S, Sum4 O E E' A B C D S -> Sum4 O E E' D A B C S.
Proof.
    intros.
    assert( ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum4_col; auto.
    spliter.
    assert(HH:=sum4_equiv O E E' A B C D S).
    destruct HH.
    assert(sum22 O E E' A B C D S).
      apply H6; auto.
    unfold sum22 in H8.
    ex_and H8 AB.
    ex_and H9 CD.
    apply sum_comm in H9; auto.
    apply sum_comm in H10; auto.
    unfold Sum4 in H.
    ex_and H ABC.
    assert(HH:= sum_assoc O E E' D C AB CD ABC S H9).
    assert(HP:=sum3_permut O E E' A B C ABC H).
    unfold sum3 in HP.
    ex_and HP AC.
    assert(HP:= sum_assoc O E E' C A B AC AB ABC H12 H8).
    destruct HP.
    assert(Sum O E E' C AB ABC).
      apply H15; auto.
    apply HH in H16.
    destruct H16.
    assert(Sum O E E' D ABC S).
      apply H17; auto.
    assert(HP:= sum_exists O E E' H0 D A H4 H1); auto.
    ex_and HP AD.
    assert(Ar2 O E E' D A AD).
      apply sum_ar2; auto.
    unfold Ar2 in H20.
    spliter.
    clean_trivial_hyps.
    assert(HP:= sum_exists O E E' H0 AD B H23 H2); auto.
    ex_and HP ABD.
    assert(HP:= sum_assoc O E E' D A B  AD AB ABD H19 H8).
    destruct HP.
    apply H26 in H24.
    unfold Sum4.
    exists ABD.
    split.
      unfold sum3.
      exists AD.
      split; auto.
    unfold sum3 in H.
    ex_and H AB'.
    assert(AB'=AB).
      apply (sum_uniqueness O E E' A B); auto.
    subst AB'.
    assert(HP:= sum_assoc O E E' D AB C ABD ABC S H24 H27).
    destruct HP.
    apply H28.
    auto.
Qed.

(* a + b + c + d = d + a + b + c *)
Lemma sum22_permut : forall O E E' A B C D S, sum22 O E E' A B C D S -> sum22 O E E' D A B C S.
Proof.
    intros.
    assert(HH:= sum4_equiv O E E' A B C D S).
    destruct HH.
    assert(Sum4 O E E' A B C D S).
      apply H1; auto.
    assert(Sum4 O E E' D A B C S).
      apply sum4_permut; auto.
    assert(HH:= sum4_equiv O E E' D A B C S).
    destruct HH.
    apply H4.
    auto.
Qed.

Lemma sum4_comm : forall O E E' A B C D S, Sum4 O E E' A B C D S -> Sum4 O E E' B A C D S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum4_col; auto.
    spliter.
    assert(HH:= sum4_equiv O E E' A B C D S).
    destruct HH.
    apply H6 in H.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H8 CD.
    apply sum_comm in H; auto.
    assert(sum22 O E E' B A C D S).
      unfold sum22.
      exists AB.
      exists CD.
      split; auto.
    assert(HH:= sum4_equiv O E E'  B A C D S).
    destruct HH.
    apply H12; auto.
Qed.

(* a + b + c + d = b + a + c + d *)
Lemma sum22_comm : forall O E E' A B C D S, sum22 O E E' A B C D S -> sum22 O E E' B A C D S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum22_col; auto.
    spliter.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H6 CD.
    unfold sum22.
    exists AB.
    exists CD.
    split; auto.
    apply sum_comm; auto.
Qed.

(* a + b + c + d = b  c + a + d *)
Lemma sum_abcd : forall O E E' A B C D AB CD BC AD S,
  Sum O E E' A B AB -> Sum O E E' C D CD -> Sum O E E' B C BC ->
  Sum O E E' A D AD -> Sum O E E' AB CD S ->
  Sum O E E' BC AD S.
Proof.
    intros.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2;auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2;auto.
    assert(Ar2 O E E' B C BC).
      apply sum_ar2;auto.
    assert(Ar2 O E E' A D AD).
      apply sum_ar2;auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2;auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(sum22 O E E' A B C D S).
      unfold sum22.
      exists AB.
      exists CD.
      split; auto.
    apply sum22_permut in H5.
    unfold sum22 in H5.
    ex_and H5 AD'.
    ex_and H6 BC'.
    assert(AD' = AD).
      apply sum_comm in H2; auto.
      apply (sum_uniqueness O E E' D A); auto.
    subst AD'.
    assert(BC' = BC).
      apply (sum_uniqueness O E E' B C); auto.
    subst BC'.
    apply sum_comm; auto.
Qed.

(* (b - a) + (c - b) = (c - a) *)
Lemma sum_diff_diff_a : forall O E E' A B C dBA dCB dCA,
  Diff O E E' B A dBA -> Diff O E E' C B dCB -> Diff O E E' C A dCA ->
  Sum O E E' dCB dBA dCA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C B dCB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C A dCA).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold Diff in H.
    ex_and H mA.
    unfold Diff in H0.
    ex_and H0 mB.
    unfold Diff in H1.
    ex_and H1 mA'.
    assert(mA' = mA).
      apply (opp_uniqueness O E E' H2 A); auto.
    subst mA'.
    assert(HH:=sum_exists O E E' H2 dBA dCB H13 H10).
    ex_and HH Sd.
    assert(sum22 O E E' B mA C mB Sd).
      unfold sum22.
      exists dBA.
      exists dCB.
      split; auto.
    apply sum22_permut in H9.
    unfold sum22 in H9.
    ex_and H9 O'.
    ex_and H14 dCA'.
    assert(O' = O).
      apply (sum_uniqueness O E E' mB B); auto.
    subst O'.
    assert(dCA'=dCA).
      apply (sum_uniqueness O E E' C mA); auto.
      apply sum_comm; auto.
    subst dCA'.
    assert(dCA=Sd).
      apply (sum_O_B_eq O E E'); auto.
    subst Sd.
    apply sum_comm; auto.
Qed.

Lemma sum_diff_diff_b : forall O E E' A B C dBA dCB dCA,
  Diff O E E' B A dBA -> Diff O E E' C B dCB -> Sum O E E' dCB dBA dCA ->
  Diff O E E' C A dCA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C B dCB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' dCB dBA dCA).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold Diff in H.
    ex_and H mA.
    unfold Diff in H0.
    ex_and H0 mB.
    assert(sum22 O E E' B mA C mB dCA).
      unfold sum22.
      exists dBA.
      exists dCB.
      split; auto.
      split; auto.
      apply sum_comm; auto.
    apply sum22_permut in H5.
    unfold sum22 in H5.
    ex_and H5 O'.
    ex_and H6 dCA'.
    assert(O'=O).
      apply (sum_uniqueness O E E' mB B); auto.
    subst O'.
    assert(dCA' = dCA).
      apply(sum_O_B_eq O E E'); auto.
    subst dCA'.
    unfold Diff.
    exists mA.
    split; auto.
    apply sum_comm; auto.
Qed.

(* (x + y) - (a + b) = (x - a) + (y - b) *)
Lemma sum_diff2_diff_sum2_a : forall O E E' A B C X Y Z dXA dYB dZC,
  Sum O E E' A B C -> Sum O E E' X Y Z -> Diff O E E' X A dXA ->
  Diff O E E' Y B dYB -> Sum O E E' dXA dYB dZC ->
  Diff O E E' Z C dZC.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    assert(Ar2 O E E' dXA dYB dZC).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    apply diff_sum in H1.
    apply diff_sum in H2.
    apply sum_diff.
    assert(HH:=sum_exists O E E' H4 C dZC H15 H9); auto.
    ex_and HH Z'.
    assert(sum22 O E E' A B dXA dYB Z').
      unfold sum22.
      exists C.
      exists dZC.
      auto.
    apply sum22_comm in H6.
    apply sum22_permut in H6.
    apply sum22_comm in H6.
    unfold sum22 in H6.
    ex_and H6 Y'.
    ex_and H16 X'.
    assert(X' = X).
      apply(sum_uniqueness O E E' A dXA); auto.
    subst X'.
    assert(Y'=Y).
      apply(sum_uniqueness O E E' B dYB); auto.
    subst Y'.
    assert( Z'= Z).
      apply(sum_uniqueness O E E' X Y); auto.
      apply sum_comm; auto.
    subst Z'.
    assumption.
Qed.

Lemma sum_diff2_diff_sum2_b : forall O E E' A B C X Y Z dXA dYB dZC,
  Sum O E E' A B C -> Sum O E E' X Y Z -> Diff O E E' X A dXA ->
  Diff O E E' Y B dYB -> Diff O E E' Z C dZC ->
  Sum O E E' dXA dYB dZC .
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X A dXA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' Y B dYB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' Z C dZC).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(HH:=sum_exists O E E' H4 dXA dYB H17 H14).
    ex_and HH dZC'.
    assert(HH:=sum_diff2_diff_sum2_a O E E' A B C X Y Z dXA dYB dZC' H H0 H1 H2 H5).
    assert( dZC' = dZC).
      apply(diff_uniqueness O E E' Z C); auto.
    subst dZC'.
    assumption.
Qed.

Lemma sum_opp : forall O E E' X MX, Sum O E E' X MX O -> Opp O E E' X MX.
Proof.
intros O E E' X MX HSum.
apply diff_O_A_opp; apply sum_diff; auto.
Qed.

Lemma sum_diff_diff : forall O E E' AX BX CX AXMBX AXMCX BXMCX,
  Diff O E E' AX BX AXMBX -> Diff O E E' AX CX AXMCX ->
  Diff O E E' BX CX BXMCX ->
  Sum O E E' AXMBX BXMCX AXMCX.
Proof.
intros O E E' AX BX CX AXMBX AXMCX BXMCX HAXMBX HAXMCX HBXMCX.
assert (HNC : ~ Col O E E')
  by (unfold Diff, Sum, Ar2 in *; destruct HAXMBX; spliter; auto).
assert (HColAX : Col O E AX)
  by (unfold Diff, Sum, Ar2 in *; destruct HAXMBX; spliter; auto).
assert (HColBX : Col O E BX)
  by (unfold Diff, Sum, Ar2 in *; destruct HBXMCX; spliter; auto).
assert (HColCX : Col O E CX)
  by (unfold Diff, Opp, Sum, Ar2 in *; destruct HBXMCX; spliter; auto).
assert (HColAXMBX : Col O E AXMBX)
  by (unfold Diff, Sum, Ar2 in *; destruct HAXMBX; spliter; auto).
assert (HColAXMCX : Col O E AXMCX)
  by (unfold Diff, Sum, Ar2 in *; destruct HAXMCX; spliter; auto).
assert (HColBXMCX : Col O E BXMCX)
  by (unfold Diff, Sum, Ar2 in *; destruct HBXMCX; spliter; auto).
destruct (opp_exists O E E' HNC BX) as [MBX HMBX]; Col.
assert (HSum1 : Sum O E E' AX MBX AXMBX).
  {
  apply diff_sum in HAXMBX; apply sum_assoc_1 with AXMBX BX O;
  apply sum_comm; auto; apply sum_O_B; Col.
  }
destruct (opp_exists O E E' HNC CX) as [MCX HMCX]; Col.
assert (HSum2 : Sum O E E' BX MCX BXMCX).
  {
  apply diff_sum in HBXMCX; apply sum_assoc_1 with BXMCX CX O;
  apply sum_comm; auto; apply sum_O_B; Col.
  }
apply sum_assoc_1 with AX MBX MCX; auto.

  {
  apply sum_assoc_2 with BX MCX O; auto; apply sum_O_B; Col.
  unfold Opp, Sum, Ar2 in *; spliter; Col.
  }

  {
  apply diff_sum in HAXMCX; apply sum_assoc_1 with AXMCX CX O;
  apply sum_comm; auto; apply sum_O_B; Col.
  }
Qed.

End T14_sum.