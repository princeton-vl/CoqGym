Require Export GeoCoq.Tarski_dev.Ch14_sum.

Section T14_prod.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma prod_to_prodp : forall O E E' A B C, Prod O E E' A B C -> Prodp O E E' A B C.
Proof.
    intros.
    unfold Prod in H.
    spliter.
    unfold Prodp.
    ex_and H0 B'.
    unfold Ar2 in H.
    spliter.
    assert(O <> E' /\ E <> E').
      split; intro; apply H; subst E'; Col.
    repeat split; try Col.
    exists B'.
    spliter.
    split.
      apply(pj_col_project B B' O E' E E'); Col.
      intro.
      induction H8.
        apply H8.
        exists E'.
        split; Col.
      apply H.
      tauto.
    apply(pj_col_project B' C O E A E'); Col.
      intro.
      subst E.
      apply H; Col.
      intro.
      subst E'.
      contradiction.
      intro.
      induction(eq_dec_points O A).
        subst A.
        induction H8.
          apply H8.
          exists O.
          split; Col.
        spliter.
        apply H.
        Col.
      induction H8.
        apply H8.
        exists A.
        split; Col.
      spliter.
      apply H.
      apply (col_transitivity_1 _ A); Col.
    unfold Pj in *.
    induction H2.
      left.
      apply par_left_comm.
      assumption.
    right; auto.
Qed.

Lemma project_pj : forall P P' A B X Y, Proj P P' A B X Y -> Pj X Y P P'.
Proof.
    intros.
    unfold Proj in H.
    spliter.
    unfold Pj.
    induction H3.
      left.
      apply par_symmetry.
      auto.
    right.
    auto.
Qed.

Lemma prodp_to_prod : forall O E E' A B C, Prodp O E E' A B C -> Prod O E E' A B C.
Proof.
    intros.
    unfold Prodp in H.
    spliter.
    ex_and H1 B'.
    unfold Prod.
    split.
      unfold Ar2.
      unfold Proj in *.
      spliter.
      repeat split; Col.
      intro.
      apply H8.
      right.
      repeat split; Col.
    exists B'.
    repeat split.
      eapply (project_pj _ _ O E'); auto.
      unfold Proj in H1.
      tauto.
    eapply (project_pj _ _ O E); auto.
    unfold Proj.
    unfold Proj in H2.
    spliter.
    repeat split; Col.
      intro.
      induction H7.
        apply H7.
        exists A.
        split; Col.
      spliter.
      apply H4.
      right.
      repeat split; Col.
    induction H6.
      left.
      apply par_right_comm.
      auto.
    right.
    auto; intro.
Qed.

Section Grid.

Variable O E E' : Tpoint.

Variable grid_ok : ~ Col O E E'.

Lemma prod_exists : forall A B,
 Col O E A -> Col O E B ->
 exists C, Prod O E E' A B C.
Proof.
    intros.
    assert(NC:=grid_ok).
    assert(exists! B' : Tpoint, Proj B B' O E' E E').
      apply(project_existence B O E' E E').
        intro.
        subst E'.
        apply NC.
        Col.
        intro.
        subst E'.
        apply NC.
        Col.
      intro.
      induction H1.
        apply H1.
        exists E'.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H1 B'.
    unfold unique in H2.
    spliter.
    assert(exists! C, Proj B' C O E E' A).
      apply(project_existence B' O E E' A).
        intro.
        subst E'.
        apply NC.
        Col.
        intro.
        subst E.
        apply NC.
        Col.
      intro.
      induction H3.
        apply H3.
        exists A.
        split; Col.
      spliter.
      apply NC.
      Col.
    ex_and H3 C.
    unfold unique in H4.
    spliter.
    exists C.
    unfold Prod.
    repeat split; Col.
      unfold Proj in H3.
      tauto.
    exists B'.
    repeat split.
      apply (project_pj B B' O E').
      auto.
      unfold Proj in H1.
      tauto.
    apply (project_pj B' C O E).
    assumption.
Qed.

Lemma prod_uniqueness : forall A B C1 C2,
 Prod O E E' A B C1 ->
 Prod O E E' A B C2 ->
 C1 = C2.
Proof.
    intros.
    apply prod_to_prodp in H.
    apply prod_to_prodp in H0.
    unfold Prodp in *.
    spliter.
    ex_and H4 B'.
    ex_and H2 B''.
    assert(B'=B'').
      eapply (project_uniqueness B B' B'' O E' E E'); auto; unfold Prod in H.
    subst B''.
    eapply (project_uniqueness B' C1 C2 O E A E'); auto.
Qed.

End Grid.


(** Lemma 14.17 *)
Lemma prod_0_l : forall O E E' A,
  ~ Col O E E' -> Col O E A -> Prod O E E' O A O.
Proof.
    intros.
    unfold Prod.
    repeat split; Col.
    assert(HH:=(grid_not_par O E E' H)).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      exists O.
      repeat split; try (apply pj_trivial).
      Col.
    assert(exists ! P' : Tpoint, Proj A P' O E' E E').
      apply(project_existence A O E' E E' H6 H5).
      intro.
      apply H3.
      Par.
    ex_and H8 B'.
    unfold unique in H9.
    spliter.
    clear H9.
    unfold Proj in H8.
    spliter.
    exists B'.
    repeat split.
      induction H12.
        left.
        Par.
      right.
      assumption.
      Col.
    left.
    right.
    repeat split; Col.
    intro.
    subst B'.
    induction H12.
      induction H12.
        apply H12.
        exists E.
        split; Col.
      spliter.
      contradiction.
    contradiction.
Qed.

Lemma prod_0_r : forall O E E' A,
  ~ Col O E E' -> Col O E A -> Prod O E E' A O O.
Proof.
    intros.
    unfold Prod.
    repeat split; Col.
    exists O.
    repeat split; try (apply pj_trivial).
    Col.
Qed.


(** Lemma 14.18 *)
Lemma prod_1_l : forall O E E' A,
  ~ Col O E E' -> Col O E A ->  Prod O E E' E A A.
Proof.
    intros.
    unfold Prod.
    repeat split; Col.
    assert(HH:=(grid_not_par O E E' H)).
    spliter.
    assert(exists ! P' : Tpoint, Proj A P' O E' E E').
      apply(project_existence A O E' E E' H6 H5).
      intro.
      apply H3.
      Par.
    ex_and H7 B'.
    unfold unique in H8.
    spliter.
    clear H8.
    unfold Proj in H7.
    spliter.
    exists B'.
    induction H11.
      repeat split.
        left; Par.
        Col.
      left; Par.
    subst B'.
    repeat split; try(apply pj_trivial).
    Col.
Qed.

Lemma prod_1_r : forall O E E' A,
  ~ Col O E E' -> Col O E A -> Prod O E E' A E A.
Proof.
    intros.
    unfold Prod.
    repeat split; Col.
    exists E'.
    assert(HH:=(grid_not_par O E E' H)).
    spliter.
    repeat split.
      left.
      right.
      repeat split; Col.
      Col.
    left.
    assert(E' <> A).
      intro.
      subst A.
      contradiction.
    right.
    repeat split; Col.
Qed.

(** Lemma 14.19 *)
Lemma inv_exists : forall O E E' A,
  ~ Col O E E' -> Col O E A -> A <> O ->
  exists IA, Prod O E E' IA A E.
Proof.
    intros.
    unfold Prod.
    repeat split; Col.
    assert(HH:=(grid_not_par O E E' H)).
    spliter.
    assert(exists ! P' : Tpoint, Proj A P' O E' E E').
      apply(project_existence A O E' E E' H7 H6).
      intro.
      apply H4.
      Par.
    ex_and H8 B'.
    unfold unique in H9.
    spliter.
    clear H9.
    unfold Proj in H8.
    spliter.
    assert(B' <> O).
      intro.
      subst B'.
      induction H12.
        induction H12.
          apply H12.
          exists E.
          split; Col.
        spliter.
        contradiction.
      contradiction.
    assert(exists ! P' : Tpoint, Proj E' P' O E B' E).
      apply(project_existence E' O E B' E); auto.
        intro.
        subst B'.
        apply H.
        Col.
      intro.
      induction H14.
        apply H14.
        exists E.
        split; Col.
      spliter.
      apply H.
      ColR.
    ex_and H14 IA.
    unfold unique in H15.
    spliter.
    clear H15.
    unfold Proj in H14.
    spliter.
    exists IA.
    repeat split; Col.
    exists B'.
    assert(Par A B' E E').
      induction H12.
        Par.
      subst B'.
      apply False_ind.
      apply H16.
      right.
      repeat split; Col.
    clear H12.
    repeat split.
      left.
      Par.
      Col.
    induction H18.
      left.
      Par.
    subst IA.
    contradiction.
Qed.

(** Lemma 14.20 *)
(** The choice of E' does not affect product *)
Lemma prod_null : forall O E E' A B, Prod O E E' A B O -> A = O \/ B = O.
Proof.
    intros.
    unfold Prod in H.
    spliter.
    ex_and H0 B'.
    induction(eq_dec_points B O).
      right.
      assumption.
    left.
    unfold Ar2 in H.
    spliter.
    unfold Pj in *.
    induction H0; induction H2.
      induction H2.
        apply False_ind.
        apply H2.
        exists E'.
        split; Col.
      spliter.
      apply(l6_21 O E B' O); Col.
      intro.
      apply H.
      ColR.
      subst B'.
      induction H0.
        apply False_ind.
        apply H0.
        exists E.
        split; Col.
      spliter.
      apply False_ind.
      apply H3.
      apply (l6_21 O E E' O); Col.
      intro.
      subst E'.
      apply H.
      Col.
      subst B'.
      induction H2.
        apply False_ind.
        apply H0.
        exists A.
        split; Col.
        apply (col3 O E); Col.
        intro.
        subst E.
        apply H; Col.
      spliter.
      apply False_ind.
      apply H2.
      apply (l6_21 O E E' O); Col.
      intro.
      subst E'.
      apply H.
      Col.
    subst B'.
    contradiction.
Qed.

Lemma prod_y_axis_change : forall O E E' E'' A B C,
  Prod O E E' A B C -> ~ Col O E E'' -> Prod O E E'' A B C.
Proof.
    intros.
    assert(HP:=H).
    unfold Prod in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(HH:=grid_not_par O E E' H ).
    spliter.
    ex_and H1 B'.
    induction(eq_dec_points B O).
      subst B.
      assert(Prod O E E' A O O).
        apply(prod_0_r); Col.
      assert(HH:= prod_uniqueness O E E' A O C O HP H13).
      subst C.
      apply prod_0_r; Col.
    induction(eq_dec_points A O).
      subst A.
      assert(Prod O E E' O B O).
        apply(prod_0_l); Col.
      assert(HH:= prod_uniqueness O E E' O B O C H14 HP).
      subst C.
      apply(prod_0_l); Col.
    assert(C <> O).
      intro.
      subst C.
      apply prod_null in HP.
      induction HP; contradiction.
    assert(exists ! P' : Tpoint, Proj B P' O E'' E E'').
      apply(project_existence B O E'' E E'').
        intro.
        subst E''.
        apply H0; Col.
        intro.
        subst E''.
        apply H0; Col.
      intro.
      induction H16.
        apply H16.
        exists E''.
        split; Col.
      spliter.
      apply H0.
      Col.
    ex_and H16 B''.
    unfold unique in H17.
    spliter.
    clear H17.
    unfold Proj in H16.
    spliter.
    assert(Par B B'' E E'').
      induction H20.
        Par.
      subst B''.
      apply False_ind.
      apply H0.
      ColR.
    clear H20.
    repeat split; auto.
    exists B''.
    repeat split.
      left; Par.
      Col.
    assert(Par E' A B' C).
      induction H12.
        assumption.
      subst B'.
      apply False_ind.
      apply H.
      ColR.
    clear H12.
    induction(eq_dec_points B E).
      subst B.
      assert(B'' = E'').
        induction H21.
          apply False_ind.
          apply H12.
          exists E.
          split; Col.
        spliter.
        apply(l6_21 O E'' E E''); Col.
      subst B''.
      assert(C = A).
        assert(Prod O E E' A E A).
          apply(prod_1_r); Col.
        eapply (prod_uniqueness O E E' A E); auto.
      subst C.
      left.
      right.
      repeat split; Col.
        intro.
        subst E''.
        apply H18.
        right.
        repeat split; Col.
      intro.
      subst E''.
      apply H18.
      right.
      repeat split; Col.
    assert(Par_strict B B'' E E'').
      induction H21.
        assumption.
      spliter.
      apply False_ind.
      apply H0.
      ColR.
    assert(Par  E E' B B').
      induction H1.
        assumption.
      subst B'.
      apply False_ind.
      apply H.
      ColR.
    clear H1.
    assert(Par_strict E E' B B').
      induction H23.
        assumption.
      spliter.
      apply False_ind.
      apply H.
      ColR.
    assert(Par_strict E' A B' C).
      induction H20.
        assumption.
      spliter.
      apply False_ind.
      assert(B' <> E').
        intro.
        subst B'.
        apply H1.
        exists E'.
        split; Col.
      apply H.
      ColR.
    induction(eq_dec_points A E).
      subst A.
      assert(Prod O E E' E B B).
        apply prod_1_l; Col.
      assert(B = C).
        apply (prod_uniqueness O E E' E B); auto.
      subst C.
      left.
      Par.
    assert(B' <> O).
      intro.
      subst B'.
      apply H5.
      apply par_symmetry.
      apply(par_col_par _ _ _ B); Par.
      Col.
    induction(eq_dec_points E' E'').
      subst E''.
      assert(Par B B' B B'').
        apply (par_trans _ _ E E'); Par.
      induction H27.
        apply False_ind.
        apply H27.
        exists B.
        split; Col.
      spliter.
      assert(B' = B'').
        apply (l6_21 B B' O E'); Col.
        intro.
        apply H.
        ColR.
      subst B''.
      left.
      Par.
    induction(col_dec E E' E'').
      assert(~Col E' E'' A).
        intro.
        apply H25.
        apply (l6_21 O E E' E''); Col.
      assert(B' <> B'').
        intro.
        subst B''.
        apply H27.
        apply(l6_21 O E' B B'); try ColR.
          intro.
          apply H.
          ColR.
        intro.
        subst B'.
        apply par_distinct in H21.
        tauto.
      assert(Par E' E'' B' B'').
        apply par_comm.
        apply (par_col_par _ _ _ B); Col.
          apply par_symmetry.
          apply (par_col_par _ _ _ E); Col.
          Par.
        assert(Par E E' E E'').
          right.
          repeat split; Col.
        assert(Par E E' B B'').
          apply (par_trans _ _ E E''); Par.
        assert(Par B B' B B'').
          apply (par_trans _ _ E E'); Par.
        induction H33.
          apply False_ind.
          apply H33.
          exists B.
          split; Col.
        spliter.
        Col.
      assert(B' <> E').
        intro.
        subst B'.
        apply H1.
        exists E'.
        split; Col.
      assert(Par_strict E' E'' B' B'').
        induction H31.
          assumption.
        spliter.
        apply False_ind.
        apply H31.
        apply(l6_21 O E' E E');Col.
        ColR.
      left.
      apply(l13_15 E' E'' A B' B'' C O H29 H33 H24); Col.
      ColR.
    assert(Par E'' E' B'' B').
      apply(l13_15 E E'' E' B B'' B' O ); Par.
      Col.
    induction(col_dec A E' E'').
      assert(Par B' C E' E'').
        apply (par_col_par _ _ _ A); Par.
        Col.
      assert(Par B' C B' B'').
        apply (par_trans _ _ E' E''); Par.
      induction H32.
        apply False_ind.
        apply H32.
        exists B'.
        split; Col.
      spliter.
      left.
      apply par_comm.
      apply(par_col_par _ _ _ B'); Par.
        intro.
        subst B''.
        apply H22.
        exists E.
        split; ColR.
      apply par_symmetry.
      apply(par_col_par _ _ _ E'); Par.
      intro.
      subst E''.
      apply H22.
      exists B.
      split; ColR.
    assert(B' <> E').
      intro.
      subst B'.
      apply H24.
      exists E'.
      split; Col.
    assert(B'' <> E'').
      intro.
      subst B''.
      apply H22.
      exists E''.
      split; Col.
    induction H29.
      left.
      apply(l13_15 E' E'' A B' B'' C O ); Par.
        intro.
        apply H30.
        Col.
      ColR.
    spliter.
    induction(col_dec O E' E'').
      left.
      apply par_comm.
      apply (l13_19 E E' A E'' B B' C B'' O); Col.
        intro.
        subst B''.
        apply H22.
        exists E.
        split; Col.
        ColR.
      left.
      Par.
    apply False_ind.
    apply H31.
    apply (l6_21 O E' E'' E'); Col.
    ColR.
Qed.


(** Lemma 14.22 *)
(** Parallel projection on the second axis preserves products. *)
Lemma proj_preserves_prod : forall O E E' A B C A' B' C',
 Prod O E E' A B C -> Ar1 O E' A' B' C' ->
 Pj E E' A A' -> Pj E E' B B' -> Pj E E' C C' ->
 Prod O E' E A' B' C'.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      unfold Prod in H.
      tauto.
    assert(AR2:= H4).
    destruct H4.
    spliter.
    unfold Ar1 in H0.
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(A' = O).
        eapply (pj_uniqueness O E E' O); Col.
        apply pj_trivial.
      subst A'.
      assert(C = O).
        assert(HH:= prod_0_l O E E' B H4 H6).
        apply(prod_uniqueness O E E' O B); auto.
      subst C.
      induction H3.
        apply False_ind.
        induction H3.
          apply H3.
          exists E'.
          spliter.
          split; Col.
        spliter.
        apply H4.
        ColR.
      subst C'.
      apply prod_0_l; Col.
    induction(eq_dec_points B O).
      subst B.
      assert(B' = O).
        apply (pj_uniqueness O E E' O); Col.
        apply pj_trivial.
      subst B'.
      assert(C = O).
        assert(HH:= prod_0_r O E E' A H4 H5).
        apply(prod_uniqueness O E E' A O); auto.
      subst C.
      induction H3.
        apply False_ind.
        induction H3.
          apply H3.
          exists E'.
          spliter.
          split; Col.
        spliter.
        apply H4.
        ColR.
      subst C'.
      apply prod_0_r; Col.
    induction(eq_dec_points C O).
      subst C.
      apply prod_null in H.
      induction H; contradiction.
    induction(eq_dec_points A' O).
      subst A'.
      apply False_ind.
      induction H1.
        induction H1.
          apply H1.
          exists E.
          split; Col.
        spliter.
        apply H4.
        ColR.
      contradiction.
    induction(eq_dec_points B' O).
      subst B'.
      apply False_ind.
      induction H2.
        induction H2.
          apply H2.
          exists E.
          split; Col.
        spliter.
        apply H4.
        ColR.
      contradiction.
    induction(eq_dec_points C' O).
      subst C'.
      apply False_ind.
      induction H3.
        induction H3.
          apply H3.
          exists E.
          split; Col.
        spliter.
        apply H4.
        ColR.
      contradiction.
    unfold Ar1 in H0.
    spliter.
    unfold Prod in *.
    spliter.
    unfold Ar2 in H.
    spliter.
    repeat split; Col.
    ex_and H17 B''.
    assert(B' = B'').
      apply(pj_uniqueness O  E E' B B' B''); Col.
    subst B''.
    exists B.
    repeat split; Col.
      apply pj_comm.
      assumption.
    left.
    apply par_comm.
    assert(HH:= grid_not_par O E E' H4).
    spliter.
    apply(l13_19 E' A A' E B' C C' B O); Col.
      intro.
      apply H4.
      ColR.
      ColR.
      ColR.
      induction H22.
        assumption.
      subst B'.
      apply False_ind.
      apply H4.
      ColR.
      induction H2.
        Par.
      subst B'.
      apply False_ind.
      apply H4.
      ColR.
    induction H1.
      induction H3.
        apply (par_trans _ _ E E'); Par.
      subst C'.
      apply False_ind.
      apply H4.
      ColR.
    subst A'.
    apply False_ind.
    apply H4.
    ColR.
Qed.

(** Lemma 14.23 *)
(** Product is associative.*)
Lemma prod_assoc1 : forall O E E' A B C AB BC ABC,
 Prod O E E' A B AB -> Prod O E E' B C BC ->
 (Prod O E E' A BC ABC -> Prod O E E' AB C ABC).
Proof.
    intros.
    assert(Ar2 O E E' A B AB).
      unfold Prod in H.
      tauto.
    assert(Ar2 O E E' B C BC).
      unfold Prod in H0.
      tauto.
    assert(Ar2 O E E' A BC ABC).
      unfold Prod in H1.
      tauto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=prod_0_l O E E' B H2 H12).
      assert(AB = O).
        apply(prod_uniqueness O E E' O B); assumption.
      subst AB.
      assert(HP:=prod_0_l O E E' BC H2 H10).
      assert(ABC=O).
        apply(prod_uniqueness O E E' O BC); assumption.
      subst ABC.
      apply prod_0_l; assumption.
    induction(eq_dec_points B  O).
      subst B.
      assert(HH:=prod_0_r O E E' A H2  H11).
      assert(AB = O).
        apply(prod_uniqueness O E E' A O); assumption.
      subst AB.
      assert(HP:=prod_0_l O E E' C H2 H9).
      assert(BC=O).
        apply(prod_uniqueness O E E' O C); assumption.
      subst BC.
      assert(ABC=O).
        apply(prod_uniqueness O E E' A O); assumption.
      subst ABC.
      apply prod_0_l; assumption.
    induction(eq_dec_points C O).
      subst C.
      assert(HH:=prod_0_r O E E' B H2  H12).
      assert(BC = O).
        apply(prod_uniqueness O E E' B O); assumption.
      subst BC.
      assert(HP:=prod_0_r O E E' A H2 H11).
      assert(ABC=O).
        apply(prod_uniqueness O E E' A O); assumption.
      subst ABC.
      apply prod_0_r; assumption.
    assert(P1:=H).
    assert(P2:= H0).
    assert(P3:=H1).
    unfold Prod in H.
    unfold Prod in H0.
    unfold Prod in H1.
    spliter.
    repeat split; auto.
    assert(HH:=grid_not_par O E E' H2).
    spliter.
    assert(exists ! P', Proj C P' O E' E E').
      apply(project_existence C O E' E E' H20 H19); Par.
    ex_and H21 C'.
    unfold unique in H22.
    spliter.
    clear H22.
    unfold Proj in H21.
    spliter.
    clean_duplicated_hyps.
    assert(Par C C' E E').
      induction H25.
        assumption.
      subst C'.
      apply False_ind.
      apply H2.
      ColR.
    clear H25.
    exists C'.
    repeat split.
      left.
      Par.
      Col.
    ex_and H14 B'.
    ex_and H8 C''.
    assert(C' = C'').
      apply(pj_uniqueness O E E' C); Col.
      left.
      Par.
    subst C''.
    ex_and H6 BC'.
    assert(B' <> O).
      intro.
      subst B'.
      induction H14.
        apply H15.
        apply par_symmetry.
        apply(par_col_par _ _ _ B); finish.
      contradiction.
    assert(BC <> O).
      intro.
      subst BC.
      assert(HH:=prod_null O E E' B C P2).
      induction HH; contradiction.
    left.
    apply(l13_19 B' B E' AB BC' BC C' ABC O); Col.
      intro.
      apply H2.
      ColR.
      intro.
      subst BC'.
      induction H6.
        apply H15.
        apply par_symmetry.
        apply (par_col_par _ _ _ BC); finish.
      contradiction.
      intro.
      subst C'.
      apply H15.
      apply par_symmetry.
      apply (par_col_par _ _ _ C); finish.
      intro.
      subst AB.
      assert(HH:=prod_null O E E' A B P1).
      induction HH; contradiction.
      intro.
      subst ABC.
      assert(HH:=prod_null O E E' A BC P3).
      induction HH; contradiction.
      ColR.
      ColR.
      ColR.
      ColR.
      ColR.
      induction H14.
        induction H6.
          apply (par_trans _ _ E E'); Par.
        subst BC'.
        apply False_ind.
        apply H2.
        ColR.
      subst B'.
      apply False_ind.
      apply H2.
      ColR.
      induction H23.
        induction H28.
          apply (par_trans _ _ E' A); Par.
        subst BC'.
        apply False_ind.
        apply H2.
        assert(ABC <> O).
          intro.
          subst ABC.
          assert(HH:=prod_null O E E' A BC P3).
          induction HH; contradiction.
        ColR.
      subst AB.
      apply False_ind.
      apply H2.
      ColR.
    induction H26.
      Par.
    subst BC.
    apply False_ind.
    apply H2.
    ColR.
Qed.

Lemma prod_assoc2 : forall O E E' A B C AB BC ABC,
 Prod O E E' A B AB -> Prod O E E' B C BC ->
 (Prod O E E' AB C ABC -> Prod O E E' A BC ABC).
Proof.
    intros.
    assert(Ar2 O E E' A B AB).
      unfold Prod in H.
      tauto.
    assert(Ar2 O E E' B C BC).
      unfold Prod in H0.
      tauto.
    assert(Ar2 O E E' AB C ABC).
      unfold Prod in H1.
      tauto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=prod_0_l O E E' B H2 H12).
      assert(AB = O).
        apply(prod_uniqueness O E E' O B); assumption.
      subst AB.
      assert(HP:=prod_0_l O E E' C H2 H9).
      assert(ABC=O).
        apply(prod_uniqueness O E E' O C); assumption.
      subst ABC.
      apply prod_0_l; assumption.
    induction(eq_dec_points B  O).
      subst B.
      assert(HH:=prod_0_l O E E' C H2  H9).
      assert(BC = O).
        apply(prod_uniqueness O E E' O C); assumption.
      subst BC.
      assert(HP:=prod_0_r O E E' A H2 H11).
      assert(AB=O).
        apply(prod_uniqueness O E E' A O); assumption.
      subst AB.
      assert(ABC=O).
        apply(prod_uniqueness O E E' O C); assumption.
      subst ABC.
      apply prod_0_r; assumption.
    induction(eq_dec_points C O).
      subst C.
      assert(HH:=prod_0_r O E E' B H2  H12).
      assert(ABC=O).
        assert(HP:=prod_0_r O E E' AB H2  H13).
        apply(prod_uniqueness O E E' AB O); assumption.
      subst ABC.
      assert(BC=O).
        apply(prod_uniqueness O E E' B O); assumption.
      subst BC.
      apply prod_0_r; assumption.
    assert(P1:=H).
    assert(P2:= H0).
    assert(P3:=H1).
    unfold Prod in H.
    unfold Prod in H0.
    unfold Prod in H1.
    spliter.
    repeat split; auto.
    assert(HH:=grid_not_par O E E' H2).
    spliter.
    assert(BC <> O).
      intro.
      subst BC.
      apply prod_null in P2.
      induction P2; contradiction.
    assert(exists ! P', Proj BC P' O E' E E').
      apply(project_existence BC O E' E E' H20 H19); Par.
    ex_and H22 BC'.
    unfold unique in H23.
    spliter.
    clear H23.
    unfold Proj in H22.
    spliter.
    clean_duplicated_hyps.
    assert(Par BC BC' E E').
      induction H26.
        assumption.
      subst BC'.
      apply False_ind.
      apply H2.
      ColR.
    clear H26.
    exists BC'.
    repeat split.
      left.
      Par.
      Col.
    ex_and H14 B'.
    ex_and H8 C'.
    ex_and H6 C''.
    assert(C' = C'').
      apply(pj_uniqueness O E E' C); Col.
    left.
    Par.
    subst C''.
    assert(B' <> O).
      intro.
      subst B'.
      induction H14.
        apply H15.
        apply par_symmetry.
        apply(par_col_par _ _ _ B); finish.
      contradiction.
    apply(par_trans _ _ B' AB).
      induction H24.
        Par.
      subst B'.
      apply False_ind.
      apply H2.
      ColR.
    apply(l13_19 E' B  B' AB C' BC BC' ABC O); auto.
      intro.
      apply H2.
      ColR.
      intro.
      subst C'.
      apply H15.
      apply par_symmetry.
      induction H6.
        apply(par_col_par _ _ _ C); Par.
        Col.
      contradiction.
      intro.
      subst BC'.
      apply H15.
      apply par_symmetry.
      apply(par_col_par _ _ _ BC); Par.
      Col.
      intro.
      subst AB.
      apply prod_null in P1.
      induction P1; contradiction.
      intro.
      subst ABC.
      apply prod_null in P3.
      induction P3.
        subst AB.
        apply prod_null in P1.
        induction P1; contradiction.
      contradiction.
      ColR.
      ColR.
      ColR.
      induction H27.
        Par.
      subst C'.
      apply False_ind.
      apply H15.
      apply par_symmetry.
      apply(par_col_par _ _ _ C); auto.
        apply par_comm.
        apply(par_col_par _ _ _ BC); auto.
          induction H6.
            Par.
          subst BC.
          apply False_ind.
          apply H2.
          ColR.
        ColR.
      Col.
      induction  H29.
        Par.
      subst C'.
      apply False_ind.
      apply H2.
      assert(ABC <> O).
        intro.
        subst ABC.
        apply H15.
        apply par_symmetry.
        apply(par_col_par _ _ _ C); auto.
          induction H6.
            Par.
          contradiction.
        ColR.
      ColR.
    induction H14.
      apply (par_trans _ _ E E'); Par.
    subst B'.
    apply False_ind.
    apply H2.
    ColR.
Qed.

Lemma prod_assoc : forall O E E' A B C AB BC ABC,
 Prod O E E' A B AB -> Prod O E E' B C BC ->
 (Prod O E E' A BC ABC <-> Prod O E E' AB C ABC).
Proof.
    intros.
    split.
      intro.
      apply (prod_assoc1 O E E' A B  _ _ BC); auto.
    intro.
    eapply (prod_assoc2 O E E' A B C AB  ); auto.
Qed.

Lemma prod_comm : forall O E E' A B C, Prod O E E' A B C -> Prod O E E' B A C.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      unfold Prod in H.
      tauto.
    unfold Ar2 in H0.
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=prod_0_l O E E' B H0 H2).
      assert(C = O).
        apply(prod_uniqueness O E E' O B); auto.
      subst C.
      eapply (prod_0_r O E E'); Col.
    induction(eq_dec_points B O).
      subst B.
      assert(HH:=prod_0_r O E E' A H0 H1).
      assert(C = O).
        apply(prod_uniqueness O E E' A O); auto.
      subst C.
      apply (prod_0_l O E E'); Col.
    induction(eq_dec_points C O).
      subst C.
      apply prod_null in H.
      induction H;  contradiction.
    unfold Prod in *.
    repeat split; auto.
    spliter.
    ex_and H7 B'.
    assert(HG:=grid_not_par O E E' H0).
    spliter.
    assert(exists ! P' : Tpoint, Proj A P' O E' E E').
      apply(project_existence A O E' E E'); Col.
      intro.
      apply H12.
      Par.
    ex_and H16 A'.
    unfold unique in H17.
    spliter.
    clear H17.
    unfold Proj in H16.
    spliter.
    clean_duplicated_hyps.
    assert(Par A A' E E').
      induction H20.
        Par.
      subst A'.
      apply False_ind.
      apply H0.
      ColR.
    clear H20.
    exists A'.
    repeat split.
      left.
      Par.
      Col.
    left.
    apply par_comm.
    apply par_symmetry.
    apply (l13_11 C B A E' A' B' O); Col.
      intro.
      apply H0.
      ColR.
      ColR.
      ColR.
      intro.
      subst A'.
      apply H10.
      apply par_symmetry.
      apply(par_col_par _ _ _ A); finish.
      induction H7.
        intro.
        subst B'.
        apply H10.
        apply par_symmetry.
        apply(par_col_par _ _ _ B); finish.
      subst B'.
      intro.
      contradiction.
      ColR.
      induction H7.
        apply(par_trans _ _ E E'); Par.
      subst B'.
      apply False_ind.
      apply H0.
      ColR.
    induction H9.
      Par.
    subst B'.
    apply False_ind.
    apply H0.
    ColR.
Qed.

(** Lemma 14.24 *)
(** Left distributivity of product over sum.*)
Lemma prod_O_l_eq : forall O E E' B C, Prod O E E' O B C -> C = O.
Proof.
    intros.
    assert(HH:=H).
    unfold Prod in HH.
    spliter.
    unfold Ar2 in H0.
    spliter.
    assert(HH:=prod_0_l O E E' B H0 H3).
    apply (prod_uniqueness O E E' O B); auto.
Qed.

Lemma prod_O_r_eq : forall O E E' A C, Prod O E E' A O C -> C = O.
Proof.
    intros.
    assert(HH:=H).
    unfold Prod in HH.
    spliter.
    unfold Ar2 in H0.
    spliter.
    assert(HH:=prod_0_r O E E' A H0 H2).
    apply (prod_uniqueness O E E' A O); auto.
Qed.

Lemma prod_uniquenessA : forall O E E' A A' B C,
  B <> O -> Prod O E E' A B C -> Prod O E E' A' B C -> A = A'.
Proof.
    intros.
    assert(HP1:= H0).
    assert(HP2:= H1).
    unfold Prod in H0.
    unfold Prod in H1.
    spliter.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    induction(eq_dec_points A' O).
      subst A'.
      assert(C = O).
        assert(HH:= prod_0_l O E E' B H0 H8).
        apply(prod_uniqueness O E E' O B); auto.
      subst C.
      apply prod_null in HP1.
      induction HP1.
        assumption.
      contradiction.
    ex_and H3 B'.
    ex_and H2 B''.
    assert(B' = B'').
      induction H3; induction H2.
        assert(Par B B' B B'').
          apply (par_trans _ _ E E'); Par.
        induction H12.
          apply False_ind.
          apply H12.
          exists B.
          split; Col.
        spliter.
        apply(l6_21 O E' B B'); Col.
        intro.
        apply H0.
        ColR.
        subst B''.
        apply False_ind.
        apply H0.
        ColR.
        subst B'.
        apply False_ind.
        apply H0.
        ColR.
      subst B.
      assumption.
    subst B''.
    assert(HH:= grid_not_par O E E' H0).
    spliter.
    induction H6; induction H11.
      assert(Par E' A' E' A).
        apply(par_trans _ _ B' C); Par.
      induction H18.
        apply False_ind.
        apply H18.
        exists E'.
        split; Col.
      spliter.
      apply(l6_21 O E E' A); Col.
      subst B'.
      apply par_distincts in H6.
      tauto.
      subst B'.
      apply par_distincts in H11.
      tauto.
    subst B'.
    induction(eq_dec_points C O).
      subst C.
      apply prod_null in HP1.
      apply prod_null in HP2.
      induction HP1; induction HP2; try contradiction.
    apply False_ind.
    apply H0.
    ColR.
Qed.

Lemma prod_uniquenessB : forall O E E' A B B' C,
  A <> O -> Prod O E E' A B C -> Prod O E E' A B' C -> B = B'.
Proof.
    intros.
    apply prod_comm in H0.
    apply prod_comm in H1.
    apply (prod_uniquenessA O E E' B B' A C); auto.
Qed.

(** Lemma 14.25 *)
(** Left distributivity of product over sum.*)
Lemma distr_l : forall O E E' A B C D AB AC AD,
 Sum O E E' B C D -> Prod O E E' A B AB -> Prod O E E' A C AC ->
 (Prod O E E' A D AD -> Sum O E E' AB AC AD).
Proof.
    intros.
    assert(HS:=H).
    unfold Sum in H.
    spliter.
    ex_and H3 B'.
    ex_and H4 C1.
    assert(HP1:=H0).
    assert(HP2:=H1).
    assert(HPS:=H2).
    unfold Prod in H0.
    spliter.
    ex_and H8 B''.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D).
      unfold Ar2 in *.
      spliter.
      repeat split; Col.
    spliter.
    assert(HH:=grid_not_par O E E' H11).
    spliter.
    assert(B' = B'').
      apply(pj_uniqueness O E E' B); Col.
    subst B''.
    unfold Prod in H1.
    spliter.
    ex_and H22 C'.
    unfold Prod in H2.
    spliter.
    ex_and H25 D'.
    assert(Sum O E' E B' C' D').
      apply(proj_preserves_sum O E E' B C D B' C' D'); auto.
      repeat split; Col.
    (* case A = O) *)
    induction(eq_dec_points A O).
      subst A.
      assert(HH1:= prod_0_l O E E' B H11 H13).
      assert( AB = O).
        apply (prod_uniqueness O E E' O B); auto.
      subst AB.
      assert(HH2:= prod_0_l O E E' C H11 H14).
      assert( AC = O).
        apply (prod_uniqueness O E E' O C); auto.
      subst AC.
      assert(HH3:= prod_0_l O E E' D H11 H15).
      assert( AD = O).
        apply (prod_uniqueness O E E' O D); auto.
      subst AD.
      apply sum_O_O; Col.
    assert(Sum O E' A B' C' D').
      apply(sum_y_axis_change O E' E A B' C' D'); auto.
      intro.
      apply H11.
      ColR.
    assert(Sum O A E' AB AC AD).
      unfold Ar2 in *.
      spliter.
      apply(proj_preserves_sum O E' A B' C' D' AB AC AD); auto.
      repeat split; auto.
        ColR.
        ColR.
      ColR.
    apply(sum_x_axis_unit_change O A E' E AB AC AD); Col.
Qed.

(** Lemma 14.24 *)
(** Right distributivity of product over sum.*)
Lemma distr_r : forall O E E' A B C D AC BC DC,
 Sum O E E' A B D -> Prod O E E' A C AC -> Prod O E E' B C BC ->
 (Prod O E E' D C DC -> Sum O E E' AC BC DC).
Proof.
    intros.
    apply prod_comm in H0.
    apply prod_comm in H1.
    apply prod_comm in H2.
    apply(distr_l O E E' C A B  D AC BC DC); auto.
Qed.

(** We omit lemma 14.26 which states that we have a division ring. *)

(** Lemma 14.27. *)
(** Sum and product are preserved by parallel projection on a different x-axis.*)
(** This lemma is used to prove that there is an isomorphism between number lines.*)
Lemma prod_1_l_eq : forall O E E' A B, Prod O E E' A B B -> A = E \/ B = O.
Proof.
    intros.
    assert(HP:=H).
    unfold Prod in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    clear H0.
    assert(HH:= prod_1_l O E E' B H H2).
    induction(eq_dec_points B O).
      right; assumption.
    left.
    apply (prod_uniquenessA O E E' A E B B H0); assumption.
Qed.

Lemma prod_1_r_eq : forall O E E' A B, Prod O E E' A B A -> B = E \/ A = O.
Proof.
    intros.
    apply prod_comm in H.
    apply (prod_1_l_eq O E E').
    assumption.
Qed.

Lemma change_grid_prod_l_O : forall O E E' B C O' A' B' C',
  Par_strict O E O' E' -> Ar1 O E O B C -> Ar1 O' E' A' B' C' ->
  Pj O O' E E' -> Pj O O' O A' -> Pj O O' B B' -> Pj O O' C C' ->
  Prod O E E' O B C ->
  Prod O' E' E A' B' C'.
Proof.
    intros.
    assert(HP:= H6).
    unfold Prod in H6.
    spliter.
    unfold Ar2 in H6.
    clear H7.
    spliter.
    assert(C = O).
      apply prod_O_l_eq in HP.
      assumption.
    subst C.
    assert(Par O O' O A').
      induction H3.
        Par.
      subst A'.
      unfold Ar1 in H1.
      spliter.
      apply False_ind.
      apply H.
      exists O.
      split; Col.
    induction H10.
      apply False_ind.
      apply H10.
      exists O.
      split; Col.
    spliter.
    assert(A' = O').
      apply (l6_21 O O' E' O'); Col.
        intro.
        apply H.
        exists O.
        split; Col.
        unfold Ar1 in H1.
        spliter.
        auto.
      unfold Ar1 in H1.
      spliter.
      Col.
    subst A'.
    clean_trivial_hyps.
    assert(Par O O' O C').
      induction H5.
        Par.
      subst C'.
      apply False_ind.
      unfold Ar1 in H1.
      spliter.
      apply H.
      exists O.
      split; Col.
    induction H7.
      apply False_ind.
      apply H7.
      exists O.
      split; Col.
    spliter.
    assert(C' = O').
      apply (l6_21 O O' E' O'); Col.
        intro.
        apply H.
        exists O.
        split; Col.
        unfold Ar1 in H1.
        spliter.
        auto.
      unfold Ar1 in H1.
      spliter.
      Col.
    subst C'.
    apply(prod_0_l).
      intro.
      apply H.
      exists E.
      split; Col.
    unfold Ar1 in H1.
    spliter.
    Col.
Qed.

Lemma change_grid_prod1 : forall O E E' B C O' A' B' C',
  Par_strict O E O' E' -> Ar1 O E E B C -> Ar1 O' E' A' B' C' ->
  Pj O O' E E' -> Pj O O' E A' -> Pj O O' B B' -> Pj O O' C C' ->
  Prod O E E' E B C ->
  Prod O' E' E A' B' C'.
Proof.
    intros.
    induction (eq_dec_points B O).
      subst B.
      apply prod_comm.
      unfold Ar1 in *.
      spliter.
      apply(change_grid_prod_l_O O E E' E C O' B' A' C'); auto.
        repeat split; Col.
        repeat split; Col.
      apply prod_comm.
      assumption.
    induction(eq_dec_points C O).
      subst C.
      apply prod_null in H6.
      induction H6.
        subst E.
        apply par_strict_distinct in H.
        tauto.
      subst B.
      tauto.
    assert(HP:= H6).
    unfold Prod in H6.
    spliter.
    unfold Ar2 in H6.
    spliter.
    clear H9.
    unfold Ar1 in H1.
    spliter.
    assert(HH:=prod_1_l O E E' B H6 H11).
    assert(B = C).
      apply (prod_uniqueness O E E' E B); auto.
    subst C.
    assert(A' = E').
      apply(l6_21 E E' O' E'); Col.
        intro.
        apply H.
        exists E.
        split; Col.
      induction H2; induction H3.
        assert(Par E A' E E').
          apply(par_trans _ _ O O'); Par.
        induction H15.
          apply False_ind.
          apply H15.
          exists E.
          split; Col.
        spliter.
        Col.
        subst A'.
        Col.
        subst E'.
        Col.
      subst A'.
      Col.
    subst A'.
    assert(C' = B').
      apply(l6_21 B' B O' E'); Col.
        intro.
        apply H.
        exists B.
        split; Col.
        assert(B' <> O').
          intro.
          subst B'.
          induction H4.
            induction H4.
              apply H4.
              exists O'.
              split; Col.
            spliter.
            apply H.
            exists O'.
            split; Col.
            ColR.
          subst B.
          apply H.
          exists O'.
          split; Col.
        ColR.
      induction H4; induction H5.
        assert(Par B C' B B').
          apply(par_trans _ _ O O'); Par.
        induction H15.
          apply False_ind.
          apply H15.
          exists B.
          split; Col.
        spliter.
        Col.
        subst C'.
        Col.
        subst B'.
        Col.
      subst C'.
      Col.
    subst C'.
    apply (prod_1_l O' E' E); Col.
    intro.
    apply H.
    exists E.
    split; Col.
Qed.

Lemma change_grid_prod : forall O E E' A B C O' A' B' C',
  Par_strict O E O' E' -> Ar1 O E A B C -> Ar1 O' E' A' B' C' ->
  Pj O O' E E' -> Pj O O' A A' -> Pj O O' B B' -> Pj O O' C C' ->
  Prod O E E' A B C ->
  Prod O' E' E A' B' C'.
Proof.
    intros.
    induction (eq_dec_points A O).
      subst A.
      apply(change_grid_prod_l_O O E E' B C O' A' B' C'); auto.
    induction (eq_dec_points B O).
      subst B.
      apply prod_comm.
      unfold Ar1 in *.
      spliter.
      apply(change_grid_prod_l_O O E E' A C O' B' A' C'); auto.
        repeat split; Col.
        repeat split; Col.
      apply prod_comm.
      assumption.
    induction(eq_dec_points C O).
      subst C.
      apply prod_null in H6.
      induction H6;contradiction.
    induction(eq_dec_points A E).
      subst A.
      apply (change_grid_prod1 O E E' B C); auto.
    rename H10 into ANE.
    assert(HP:=H6).
    unfold Prod in H6.
    spliter.
    clear H10.
    unfold Ar1 in *.
    unfold Ar2 in H6.
    spliter.
    clean_duplicated_hyps.
    prolong O O' E'' O O'.
    assert(E''<> O).
      intro.
      subst E''.
      apply between_identity in H10.
      subst O'.
      apply H.
      exists O.
      split; Col.
    assert(~Col O E E'').
      intro.
      apply H.
      exists O'.
      apply bet_col in H10.
      split; Col.
      ColR.
    assert(HH:= prod_y_axis_change O E E' E'' A B C  HP H19).
    assert(HP1:= HH).
    unfold Prod in HH.
    spliter.
    ex_and H21 B''.
    assert(~Col O E'' E).
      intro.
      apply H19.
      Col.
    assert(exists C : Tpoint, Sum O E'' E E'' O' C).
      apply(sum_exists O E'' E H24 E'' O'); Col.
    ex_and H25 C2.
    assert(~ Col O E'' A).
      intro.
      apply H24.
      ColR.
    assert(HH:= sum_y_axis_change O E'' E A  E'' O' C2 H26 H25).
    assert(HS1:= HH).
    unfold Sum in HH.
    spliter.
    unfold Ar2 in H27.
    spliter.
    clear H27.
    ex_and H28 A0.
    ex_and H27 A0'.
    assert(A = A0).
      apply(l6_21 O E E'' A); Col.
        intro.
        subst A.
        apply H25.
        Col.
        ColR.
        induction H27.
          induction H27.
            apply False_ind.
            apply H27.
            exists E''.
            split; Col.
          spliter.
          Col.
        subst A0.
        Col.
    subst A0.
    assert(Par O O' E E').
      induction H2.
        Par.
      subst E'.
      apply False_ind.
      apply H6.
      Col.
    assert(Par O O' A A').
      induction H3.
        Par.
      subst A'.
      apply False_ind.
      apply H.
      exists A.
      split; Col.
    assert(Par O O' B B').
      induction H4.
        Par.
      subst B'.
      apply False_ind.
      apply H.
      exists B.
      split; Col.
    assert(Par O O' C C').
      induction H5.
        Par.
      subst C'.
      apply False_ind.
      apply H.
      exists C.
      split; Col.
    assert(O <> O').
      intro.
      subst O'.
      apply par_distinct in H35.
      tauto.
    clear H2 H3 H4 H5.
    assert(A0'=A').
      apply (l6_21 O' E' A A'); Col.
        intro.
        apply H.
        exists A.
        split; Col.
        intro.
        subst A'.
        apply par_distinct in H36.
        tauto.
        induction H33.
          assert(Par O' E' O' A0').
            apply(par_trans _ _ O A); Par.
            apply(par_col_par _ _ _ E); Col.
            left.
            Par.
          induction H3.
            apply False_ind.
            apply H3.
            exists O'.
            split; Col.
          spliter.
          Col.
        subst A0'.
        Col.
        induction H32.
          assert(Par A A' A A0').
            apply(par_trans _ _ O O'); Par.
            apply par_symmetry.
            apply(par_col_par _ _ _ E''); Col.
            Par.
          induction H3.
            apply False_ind.
            apply H3.
            exists A.
            split; Col.
          spliter.
          Col.
        subst A0'.
        Col.
    subst A0'.
    assert(Par O E'' A A').
      induction H32.
        Par.
      subst A'.
      apply par_distinct in H36.
      tauto.
    assert(Par O A O' A').
      induction H33.
        Par.
      subst A'.
      apply False_ind.
      induction H2.
        apply H2.
        exists O'.
        split; Col.
      spliter.
      apply H.
      exists O'.
      split; Col.
      ColR.
    assert(Par A E'' A' C2).
      induction H34.
        Par.
      subst C2.
      apply False_ind.
      induction H2.
        apply H2.
        exists A'.
        split; Col.
      spliter.
      apply H.
      exists A'.
      split; Col.
      ColR.
    clear H33 H34 H32.
    assert(HS0:= H26).
    induction H26.
    unfold Ar2 in H5.
    spliter.
    clean_duplicated_hyps.
    ex_and H26 E0.
    ex_and H5 E0'.
    assert(E0 = E).
      apply (l6_21 E'' E O E); Col.
      induction H5.
        induction H5.
          apply False_ind.
          apply H5.
          exists E''.
          split; Col.
        spliter.
        Col.
      subst E0.
      Col.
    subst E0.
    assert(E0' = E').
      apply(l6_21 O' E' E E'); Col.
        intro.
        apply H.
        exists E.
        split; Col.
        intro.
        subst E'.
        apply H6.
        Col.
        induction H30.
          assert(Par O' E' O' E0').
            apply(par_trans _ _ O E); Par.
          induction H40.
            apply False_ind.
            apply H40.
            exists O'.
            split; Col.
          spliter.
          Col.
        subst E0'.
        Col.
        induction H29.
          assert(Par E E' E E0').
            apply(par_trans _ _ O E''); Par.
            apply (par_col_par _ _ _ O'); Col.
            Par.
          induction H40.
            apply False_ind.
            apply H40.
            exists E.
            split; Col.
          spliter.
          Col.
        subst E0'.
        Col.
    subst E0'.
    clean_trivial_hyps.
    clean_duplicated_hyps.
    assert(Par E E'' E' C2).
      induction H31.
        Par.
      subst C2.
      apply False_ind.
      assert(Col O O' E').
        ColR.
      apply H.
      exists O.
      split; Col.
    clear H31.
    clear H5.
    clear H30.
    clear H29.
    assert(Par E E'' B B'').
      induction H21.
        Par.
      subst B''.
      apply False_ind.
      apply H19.
      ColR.
    clear H21.
    assert(exists C : Tpoint, Sum O E'' E B'' O' C).
      apply(sum_exists O E'' E H24 B'' O'); Col.
    ex_and H21 C3.
    assert(HS2:= H28).
    induction H28.
    ex_and H28 B0.
    ex_and H29 B0'.
    assert(B'' <> O).
      intro.
      subst B''.
      induction H5.
        apply H5.
        exists E.
        split; Col.
      spliter.
      apply H19.
      ColR.
    assert(B0 = B).
      apply (l6_21 O E B'' B); Col.
        intro.
        apply H24.
        ColR.
        intro.
        subst B''.
        apply par_distinct in H5.
        tauto.
        induction H28.
          assert(Par B'' B0 B B'').
            apply(par_trans _ _ E E''); Par.
          induction H41.
            apply False_ind.
            apply H41.
            exists B''.
            split; Col.
          spliter.
          Col.
        subst B0.
        Col.
    subst B0.
    assert(B0' = B').
      apply (l6_21 O' E' B B'); Col.
        intro.
        apply H.
        exists B.
        split; Col.
        intro.
        subst B'.
        apply par_distinct in H37.
        tauto.
        induction H31.
          assert(Par O' E' O' B0').
            apply(par_trans _ _ O E); Par.
          induction H41.
            apply False_ind.
            apply H41.
            exists O'.
            split; Col.
          spliter.
          Col.
        subst B0'.
        Col.
        induction H30.
          assert(Par B B' B B0').
            apply(par_trans _ _ O E''); Par.
            apply (par_col_par _ _ _ O'); Col.
            Par.
          induction H41.
            apply False_ind.
            apply H41.
            exists B.
            split; Col.
          spliter.
          Col.
        subst B0'.
        Col.

    subst B0'.
    unfold Ar2 in H21.
    spliter.
    clean_duplicated_hyps.
    assert(E'' <> O).
      intro.
      subst E''.
      apply H25.
      Col.
    assert(B' <> O').
      intro.
      subst B'.
      induction H37.
        apply H29.
        exists O'.
        split; Col.
      spliter.
      apply H.
      exists O'.
      split; Col.
      ColR.
    assert(Par E E'' B' C3).
      induction H32.
        Par.
      subst C3.
      apply False_ind.
      assert(Col O O' B').
        ColR.
      apply H.
      exists O.
      split; Col.
      ColR.
    clear H32.
    assert(Par E'' E B'' B).
      induction H28.
        Par.
      subst B''.
      apply par_distinct in H5.
      tauto.
    clear H28.
    assert(HH:= sum_y_axis_change O E'' E A  B'' O' C3 HS2 H25).
    assert(HS3 := HH).
    unfold Sum in HH.
    spliter.
    unfold Ar2 in H28.
    spliter.
    clean_duplicated_hyps.
    ex_and H42 C0.
    ex_and H21 C0'.
    assert(Par E'' A B'' C).
      induction H23.
        Par.
      subst B''.
      apply False_ind.
      induction H32.
        apply H23.
        exists E.
        split; Col.
        ColR.
      spliter.
      apply H19.
      ColR.
    clear H23.
    assert(C0 = C).
      apply (l6_21 O E B'' C); Col.
        intro.
        apply H19.
        ColR.
        intro.
        subst B''.
        apply par_distinct in H46.
        tauto.
        ColR.
        induction H21.
          assert(Par B'' C B'' C0).
            apply(par_trans _ _ E'' A); Par.
          induction H23.
            apply False_ind.
            apply H23.
            exists B''.
            split; Col.
          spliter.
          Col.
        subst C0.
        Col.
    subst C0.
    assert(C0' = C').
      apply (l6_21 O' E' C C'); Col.
        intro.
        apply H.
        exists C.
        split; Col.
        intro.
        subst C'.
        apply par_distincts in H38.
        tauto.
        induction H44.
          assert(Par O' C' O' C0').
            apply(par_trans _ _ O E); Par.
              apply par_symmetry.
              apply(par_col_par _ _ _ E'); Col.
                intro.
                subst C'.
                induction H38.
                  apply H38.
                  exists O'.
                  split; Col.
                spliter.
                apply H.
                exists O'.
                split; Col.
                ColR.
              left.
              Par.
            apply par_symmetry.
            apply(par_col_par _ _ _ A); Col.
            Par.
          induction H44.
            apply False_ind.
            apply H44.
            exists O'.
            split; Col.
          spliter.
          Col.
          ColR.
        subst C0'.
        Col.
        induction H42.
          assert(Par C C' C C0').
            apply(par_trans _ _ O O'); Par.
            apply par_symmetry.
            apply (par_col_par _ _ _ E''); Col.
            Par.
          induction H42.
            apply False_ind.
            apply H42.
            exists C.
            split; Col.
          spliter.
          Col.
        subst C0'.
        induction H44.
          induction H23.
            apply False_ind.
            apply H23.
            exists C.
            split;Col.
          spliter.
          apply False_ind.
          apply H.
          exists O'.
          split; Col.
          ColR.
        Col.
    subst C0'.
    assert(Par B B'' B' C3).
      apply(par_trans _ _ E E''); Par.
    assert(Par C B'' C' C3).
      apply(par_trans _ _ A E''); Par.
      induction H45.
        Par.
      subst C3.
      assert(Par E E'' O E).
        apply(par_trans _ _ O' E'); Par.
          apply(par_col_par _ _ _ C'); Col.
          apply par_comm.
          apply(par_col_par _ _ _ B'); Col.
            intro.
            subst C'.
            induction H38.
              apply H38.
              exists O'.
              split; Col.
            spliter.
            apply H.
            exists O'.
            split; Col.
            ColR.
            Par.
          ColR.
      apply False_ind.
      induction H45.
        apply H45.
        exists E.
        split; Col.
      spliter.
      apply H24.
      Col.
    (*  *)
    assert(Prod O' E' C2 A' B' C').
      repeat split; Col.
        intro.
        assert(C2 <> O').
          intro.
          subst C2.
          assert(Par O E E E'').
            apply(par_trans _ _ O' E'); Par.
          induction H49.
            apply H49.
            exists E.
            split; Col.
          spliter.
          contradiction.
        assert(Col O O' C2).
          ColR.
        assert(Col O O' E').
          ColR.
        apply H.
        exists O.
        split; Col.
      exists C3.
      split.
        left.
        apply (par_trans _ _ B B''); Par.
        apply (par_trans _ _  E E''); Par.
      split.
        ColR.
      left.
      apply(par_trans _ _ C B''); Par.
      apply(par_trans _ _ A E''); Par.
    apply(prod_y_axis_change O' E' C2 E A' B' C' H48).
    intro.
    apply H.
    exists E.
    split; Col.
Qed.


(** Lemma
 14.28 is something like
  exists f,
  prod O E X A B C ->
  prod O' E' f(X) f(A') f(B') f(C') ?
*)


(** Lemma 14.29 *)
(** From Pappus-Pascal we can derive that the product is symmetric, hence we have a field. *)

(* already done : prod_comm *)

Lemma prod_sym : forall O E E' A B C,
  Prod O E E' A B C -> Prod O E E' B A C.
Proof.
    intros.
    apply (prod_comm O E E').
    assumption.
Qed.

(** Lemma 14.31 *)
Lemma l14_31_1 : forall O E E' A B C D,
  Ar2_4 O E E' A B C D -> C <> O ->
  (exists X, Prod O E E' A B X /\ Prod O E E' C D X) -> Prod O C E' A B D.
Proof.
    intros.
    ex_and H1 X.
    spliter.
    unfold Ar2_4 in H.
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:= prod_0_l O E E' B H H4).
      assert(X=O).
        apply (prod_O_l_eq O E E' B); assumption.
      subst X.
      apply (prod_null)in H2.
      induction H2.
        contradiction.
      subst D.
      apply(prod_0_l O C E' B).
        intro.
        apply H.
        ColR.
      assert(HG:=grid_not_par O E E' H).
      spliter.
      ColR.
    induction(eq_dec_points B O).
      subst B.
      assert(HH:= prod_0_r O E E' A H H3).
      assert(X=O).
        apply (prod_O_r_eq O E E' A); assumption.
      subst X.
      apply (prod_null)in H2.
      induction H2.
        contradiction.
      subst D.
      apply(prod_0_r O C E' A).
        intro.
        apply H.
        ColR.
      assert(HG:=grid_not_par O E E' H).
      spliter.
      ColR.
    induction(eq_dec_points D O).
      subst D.
      assert(HH:= prod_0_r O E E' C H H5).
      assert(X=O).
        apply (prod_O_r_eq O E E' C); assumption.
      subst X.
      apply (prod_null)in H1.
      induction H1.
        contradiction.
      contradiction.
    assert(HG:=grid_not_par O E E' H).
    spliter.
    assert(exists ! P' : Tpoint, Proj B P' O E' E' C).
      apply(project_existence B O E' E' C).
        intro.
        subst C.
        contradiction.
        auto.
      intro.
      induction H16.
        apply H16.
        exists E'.
        split; Col.
      spliter.
      apply H.
      ColR.
    ex_and H16 B''.
    unfold unique in H17.
    spliter.
    clear H17.
    unfold Proj in H16.
    spliter.
    assert(Par B B'' E' C).
      induction H20.
        Par.
      subst B''.
      apply False_ind.
      apply H.
      ColR.
    clear H20.
    unfold Prod.
    repeat split; try ColR.
      intro.
      apply H.
      ColR.
    exists B''.
    split.
      left.
      Par.
    split.
      Col.
    assert(HP1:=H1).
    assert(HP2:=H2).
    unfold Prod in H1.
    unfold Prod in H2.
    spliter.
    ex_and H22 B'.
    ex_and H20 D'.
    assert(B' <> O).
      intro.
      subst B'.
      induction H22.
        induction H22.
          apply H22.
          exists E.
          split; Col.
        spliter.
        apply H.
        ColR.
      contradiction.
    assert(Par E B'' C B').
      apply(l13_11 E C B  B'  B'' E' O); Col.
        intro.
        apply H.
        ColR.
        ColR.
        intro.
        subst B''.
        induction H21.
          apply H21.
          exists C.
          split; Col.
          ColR.
        spliter.
        apply H.
        ColR.
        ColR.
        Par.
      induction H22.
        Par.
      subst B'.
      apply False_ind.
      apply H.
      ColR.
    assert(X <> O).
      intro.
      subst X.
      apply prod_null in HP1.
      induction HP1; contradiction.
    assert(Par A D' C B').
      apply(l13_11 A C X  B'  D' E' O); Col.
        intro.
        apply H.
        ColR.
        ColR.
        unfold Ar2 in *.
        spliter.
        ColR.
        intro.
        subst D'.
        induction H20.
          induction H20.
            apply H20.
            exists E.
            split; Col.
          spliter.
          apply H.
          ColR.
        contradiction.
        ColR.
        induction H26.
          Par.
        subst D'.
        apply False_ind.
        apply H.
        unfold Ar2 in *.
        spliter.
        ColR.
      induction H24.
        Par.
      subst B'.
      apply False_ind.
      unfold Ar2 in *.
      spliter.
      apply H.
      ColR.
    left.
    apply par_symmetry.
    apply par_comm.
    unfold Ar2 in *.
    spliter.
    apply(l13_11 D A E E' B'' D' O); Col.
      intro.
      apply H.
      ColR.
      ColR.
      intro.
      subst B''.
      induction H28.
        apply H28.
        exists C.
        split; Col.
      spliter.
      apply H.
      ColR.
      intro.
      subst D'.
      induction H30.
        apply H30.
        exists C.
        split; Col.
        ColR.
      spliter.
      apply H.
      ColR.
      ColR.
      apply (par_trans _ _ C B'); Par.
    induction H20.
      Par.
    subst D'.
    apply False_ind.
    apply H.
    ColR.
Qed.

Lemma l14_31_2 : forall O E E' A B C D ,
  Ar2_4 O E E' A B C D -> C <> O -> Prod O C E' A B D ->
  (exists X, Prod O E E' A B X /\ Prod O E E' C D X).
Proof.
    intros.
    unfold Ar2_4 in H.
    spliter.
    assert(HG:= grid_not_par O E E' H).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(D = O).
        apply(prod_O_l_eq O C E' B); auto.
      subst D.
      exists O.
      split.
        apply(prod_0_l O E E' B); Col.
      apply(prod_0_r O E E' C); Col.
    induction(eq_dec_points B O).
      subst B.
      assert(D = O).
        apply(prod_O_r_eq O C E' A); auto.
      subst D.
      exists O.
      split.
        apply(prod_0_r O E E' A); Col.
      apply(prod_0_r O E E' C); Col.
    induction(eq_dec_points D O).
      subst D.
      exists O.
      apply prod_null in H1.
      induction H1.
        subst A.
        split.
          apply(prod_0_l O E E' B); Col.
        apply(prod_0_r O E E' C); Col.
      subst B.
      split.
        apply(prod_0_r O E E' A); Col.
      apply(prod_0_r O E E' C); Col.
    assert(exists ! P' : Tpoint, Proj B P' O E' E E').
      apply(project_existence B O E' E E'); auto.
      intro.
      apply H8.
      Par.
    ex_and H15 B'.
    unfold unique in H16.
    spliter.
    clear H16.
    unfold Proj in H15.
    spliter.
    assert(Par B B' E E').
      induction H19.
        Par.
      subst B'.
      apply False_ind.
      apply H.
      ColR.
    clear H19.
    assert(exists ! P' : Tpoint, Proj B' P' O E E' A).
      apply(project_existence B' O E E' A); auto.
        intro.
        subst A.
        contradiction.
      intro.
      induction H19.
        apply H19.
        exists A.
        split; Col.
      spliter.
      apply H.
      Col.
    ex_and H19 X.
    unfold unique in H21.
    spliter.
    clear H21.
    unfold Proj in H19.
    spliter.
    clean_duplicated_hyps.
    assert(X <> O).
      intro.
      subst X.
      induction H24.
        induction H15.
          apply H15.
          exists E'.
          split; Col.
        spliter.
        apply H.
        ColR.
      subst B'.
      induction H20.
        apply H15.
        exists E.
        split; Col.
      spliter.
      contradiction.
    assert(Par B' X E' A).
      induction H24.
        Par.
      subst B'.
      apply False_ind.
      apply H.
      ColR.
    clear H24.
    exists X.
    unfold Prod in *.
    spliter.
    ex_and H17 B''.
    repeat split; Col.
      exists B'.
      split.
        left.
        Par.
      split.
        Col.
      induction H24.
        left.
        Par.
      subst B''.
      apply False_ind.
      apply H.
      ColR.
    assert(exists ! P' : Tpoint, Proj D P' O E' E E').
      apply(project_existence D O E' E E'); Col.
      intro.
      apply H8.
      Par.
    ex_and H25 D'.
    unfold unique in H26.
    spliter.
    clear H26.
    unfold Proj in H25.
    spliter.
    clean_duplicated_hyps.
    assert(Par D D' E E').
      induction H29.
        Par.
      subst D'.
      apply False_ind.
      apply H.
      ColR.
    clear H29.
    exists D'.
    split.
      left.
      Par.
    split.
      Col.
    left.
    assert(Par X D' B B'').
      apply(l13_11 X B D B'' D' B' O); auto.
        intro.
        assert(B''<>O).
          intro.
          subst B''.
          induction H17.
            induction H17.
              apply H17.
              exists C.
              split; Col.
              ColR.
            spliter.
            apply H.
            ColR.
          contradiction.
        apply H.
        ColR.
        ColR.
        ColR.
        intro.
        subst D'.
        induction H25.
          apply H25.
          exists E.
          split; Col.
        spliter.
        contradiction.
        intro.
        subst B'.
        induction H20.
          apply H20.
          exists E.
          split; Col.
        spliter.
        contradiction.
        ColR.
        ColR.
        Par.
        apply(par_trans _ _ E E'); Par.
      induction H24.
        apply(par_trans _ _ E' A); Par.
      subst B''.
      apply False_ind.
      apply H.
      ColR.
    induction H17.
      apply (par_trans _ _ B B''); Par.
    subst B''.
    apply par_distincts in H26.
    tauto.
Qed.

Lemma prod_x_axis_unit_change : forall O E E' A B C D U,
  Ar2_4 O E E' A B C D -> Col O E U -> U <> O ->
  ( exists X, Prod O E E' A B X /\ Prod O E E' C D X) ->
  ( exists Y, Prod O U E' A B Y /\ Prod O U E' C D Y).
Proof.
    intros.
    ex_and H2 X.
    unfold Ar2_4 in H.
    spliter.
    assert(HG:= grid_not_par O E E' H).
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(X = O).
        apply(prod_O_l_eq O E E' B); assumption.
      subst X.
      apply prod_null in H3.
      induction H3.
        subst C.
        exists O.
        split.
          apply(prod_0_l).
            intro.
            apply H.
            ColR.
          ColR.
        apply(prod_0_l).
          intro.
          apply H.
          ColR.
        ColR.
      subst D.
      exists O.
      split.
        apply(prod_0_l).
          intro.
          apply H.
          ColR.
        ColR.
      apply(prod_0_r).
        intro.
        apply H.
        ColR.
      ColR.
    induction(eq_dec_points B O).
      subst B.
      assert(X = O).
        apply(prod_O_r_eq O E E' A); assumption.
      subst X.
      apply prod_null in H3.
      induction H3.
        subst C.
        exists O.
        split.
          apply(prod_0_r).
            intro.
            apply H.
            ColR.
          ColR.
        apply(prod_0_l).
          intro.
          apply H.
          ColR.
        ColR.
      subst D.
      exists O.
      split.
        apply(prod_0_r).
          intro.
          apply H.
          ColR.
        ColR.
      apply(prod_0_r).
        intro.
        apply H.
        ColR.
      ColR.
    induction(eq_dec_points C O).
      subst C.
      assert(X = O).
        apply(prod_O_l_eq O E E' D); assumption.
      subst X.
      apply prod_null in H2.
      induction H2.
        subst A.
        exists O.
        split.
          apply(prod_0_l).
            intro.
            apply H.
            ColR.
          ColR.
        apply(prod_0_l).
          intro.
          apply H.
          ColR.
        ColR.
      subst B.
      exists O.
      split.
        apply(prod_0_r).
          intro.
          apply H.
          ColR.
        ColR.
      apply(prod_0_l).
        intro.
        apply H.
        ColR.
      ColR.
    induction(eq_dec_points D O).
      subst D.
      assert(X = O).
        apply(prod_O_r_eq O E E' C); assumption.
      subst X.
      apply prod_null in H2.
      induction H2.
        subst A.
        exists O.
        split.
          apply(prod_0_l).
            intro.
            apply H.
            ColR.
          ColR.
        apply(prod_0_r).
          intro.
          apply H.
          ColR.
        ColR.
      subst B.
      exists O.
      split.
        apply(prod_0_r).
          intro.
          apply H.
          ColR.
        ColR.
      apply(prod_0_r).
        intro.
        apply H.
        ColR.
      ColR.
    assert(exists ! P' : Tpoint, Proj B P' O E' U E').
      apply(project_existence B O E' U E').
        intro.
        subst U.
        contradiction.
        auto.
      intro.
      induction H18.
        apply H18.
        exists E'.
        split;Col.
      spliter.
      apply H.
      ColR.
    ex_and H18 Bu.
    unfold unique in H19.
    spliter.
    clear H19.
    unfold Proj in H18.
    spliter.
    assert(Par B Bu U E').
      induction H22.
        Par.
      subst Bu.
      apply False_ind.
      apply H.
      ColR.
    clear H22.
    assert(exists ! P' : Tpoint, Proj Bu P' O E A E').
      apply(project_existence Bu O E A E').
        intro.
        subst A.
        contradiction.
        auto.
      intro.
      induction H22.
        apply H22.
        exists A.
        split; Col.
      spliter.
      apply H.
      Col.
    ex_and H22 Xu.
    unfold unique in H24.
    spliter.
    clear H24.
    unfold Proj in H22.
    spliter.
    assert(Par Bu Xu A E').
      induction H27.
        Par.
      subst Bu.
      apply False_ind.
      induction H23.
        apply H23.
        exists U.
        split; Col.
        ColR.
      spliter.
      apply H.
      ColR.
    clear H27.
    exists Xu.
    split.
      unfold Prod.
      repeat split; try ColR.
        intro.
        apply H.
        ColR.
      exists Bu.
      split.
        left.
        Par.
      split.
        ColR.
      left.
      Par.
    assert(exists ! P' : Tpoint, Proj D P' O E' U E').
      apply(project_existence D O E' U E').
        intro.
        subst U.
        apply H.
        ColR.
        auto.
      intro.
      induction H27.
        apply H27.
        exists E'.
        split; Col.
      spliter.
      apply H.
      ColR.
    ex_and H27 Du.
    unfold unique in H29.
    spliter.
    clear H29.
    unfold Proj in H27.
    spliter.
    assert(Par D Du U E').
      induction H32.
        Par.
      subst Du.
      apply False_ind.
      apply H.
      ColR.
    clear H32.
    unfold Prod.
    repeat split; try ColR.
      intro.
      apply H.
      ColR.
    exists Du.
    split.
      left.
      Par.
    split.
      Col.
    assert(Prod O C E' A B D).
      apply(l14_31_1 O E E' A B C D).
        repeat split; Col.
        auto.
      exists X.
      split; Col.
    unfold Prod in H2.
    spliter.
    ex_and H34 B'.
    unfold Prod in H3.
    spliter.
    ex_and H37 D'.
    unfold Prod in H32.
    spliter.
    ex_and H40 D''.
    assert(Xu <> O).
      intro.
      subst Xu.
      induction H28.
        apply H28.
        exists E'.
        split; Col.
      spliter.
      apply H.
      ColR.
    assert(D'' <> O).
      intro.
      subst D''.
      induction H42.
        induction H42.
          apply H42.
          exists A.
          split; Col.
          ColR.
        spliter.
        apply H.
        ColR.
      subst D.
      tauto.
    assert(Par Xu Du B D'').
      apply(l13_11 Xu B D D'' Du Bu O); auto.
        intro.
        apply H.
        ColR.
        ColR.
        ColR.
        intro.
        subst Du.
        induction H33.
          apply H33.
          exists U.
          split; Col.
          ColR.
        spliter.
        apply H.
        ColR.
        intro.
        subst Bu.
        induction H28.
          apply H28.
          exists A.
          split; Col.
          ColR.
        spliter.
        apply H.
        ColR.
        ColR.
        ColR.
        apply(par_trans _ _ U E'); Par.
      induction H42.
        apply (par_trans _ _ E' A); Par.
      subst D''.
      apply False_ind.
      apply H.
      ColR.
    left.
    apply (par_trans _ _ B D''); Par.
    induction H40.
      Par.
    subst D''.
    apply False_ind.
    apply par_distincts in H45.
    tauto.
Qed.

Lemma opp_prod : forall O E E' ME X MX,
  Opp O E E' E ME -> Opp O E E' X MX -> Prod O E E' X ME MX.
Proof.
intros O E E' ME X MX HOpp1 HOpp2.
assert (HNC : ~ Col O E E')
  by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HCol1 : Col O E ME)
  by (unfold Opp, Sum, Ar2 in *; spliter; Col).
assert (HCol2 : Col O E X)
  by (unfold Opp, Sum, Ar2 in *; spliter; Col).
destruct (sum_exists O E E' HNC E ME) as [EPME HEPME]; Col.
assert (O = EPME)
  by (apply sum_uniqueness with O E E' E ME; auto; apply diff_sum; apply diff_O_A; Col).
treat_equalities; destruct (prod_exists O E E' HNC X E) as [X' HX]; Col.
assert (X = X') by (apply prod_uniqueness with O E E' X E; auto; apply prod_1_r; Col).
treat_equalities; destruct (prod_exists O E E' HNC X O) as [O' HProd]; Col.
assert (O = O') by (apply prod_uniqueness with O E E' X O; auto; apply prod_0_r; Col).
treat_equalities; destruct (prod_exists O E E' HNC X ME) as [MX' HMX]; Col.
assert (HOpp3 : Sum O E E' X MX' O) by (apply distr_l with X E ME O; auto).
apply sum_opp in HOpp3; assert (MX = MX') by (apply opp_uniqueness with O E E' X; Col).
treat_equalities; auto.
Qed.

Lemma distr_l_diff : forall O E E' A B C BMC AB AC ABMC,
  Diff O E E' B C BMC -> Prod O E E' A B AB ->
  Prod O E E' A C AC -> Prod O E E' A BMC ABMC ->
  Diff O E E' AB AC ABMC.
Proof.
intros O E E' A B C BMC AB AC ABMC HBMC HAB HAC HABMC.
apply diff_sum in HBMC; apply sum_diff.
apply distr_l with A C BMC B; auto.
Qed.

Lemma diff_of_squares : forall O E E' A B A2 B2 A2MB2 APB AMB F,
  Prod O E E' A A A2 -> Prod O E E' B B B2 -> Diff O E E' A2 B2 A2MB2 ->
  Sum O E E' A B APB -> Diff O E E' A B AMB -> Prod O E E' APB AMB F ->
  A2MB2 = F.
Proof.
intros O E E' A B A2 B2 A2MB2 APB AMB F HA2 HB2 HA2MB2 HAPB HAMB HF.
assert (HNC : ~ Col O E E')
  by (apply diff_ar2 in HA2MB2; unfold Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColAMB : Col O E AMB) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (prod_exists O E E' HNC A AMB) as [F1 HF1]; Col.
assert (HColF1 : Col O E F1) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (prod_exists O E E' HNC B AMB) as [F2 HF2]; Col.
assert (HColF2 : Col O E F2) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (sum_exists O E E' HNC F1 F2) as [F' HF']; Col.
assert (F = F').
  {
  apply sum_uniqueness with O E E' F1 F2; auto.
  apply distr_r with A B AMB APB; auto.
  }
treat_equalities; destruct (prod_exists O E E' HNC A B) as [AB HAB]; Col.
assert (HColA2 : Col O E A2) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColAB : Col O E AB) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' A2 AB) as [A2MAB HA2MAB]; Col.
assert (A2MAB = F1).
  {
  apply diff_uniqueness with O E E' A2 AB; auto.
  apply distr_l_diff with A A B AMB; auto.
  }
destruct (prod_exists O E E' HNC B A) as [BA HBA]; Col.
assert (HColB2 : Col O E B2) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColBA : Col O E BA) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' BA B2) as [BAMB2 HBAMB2]; Col.
assert (BAMB2 = F2).
  {
  apply diff_uniqueness with O E E' BA B2; auto.
  apply distr_l_diff with B A B AMB; auto.
  }
assert (AB = BA).
  {
  apply prod_uniqueness with O E E' A B; auto.
  apply prod_comm; auto.
  }
treat_equalities; apply diff_uniqueness with O E E' A2 B2; auto.
apply sum_diff_diff_b with AB BAMB2 A2MAB; auto.
Qed.

Lemma eq_squares_eq_or_opp : forall O E E' A B A2,
  Prod O E E' A A A2 -> Prod O E E' B B A2 -> A = B \/ Opp O E E' A B.
Proof.
intros O E E' A B A2 HA2 HB2.
assert (HNC : ~ Col O E E')
  by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA : Col O E A) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColA2 : Col O E A2) by (unfold Prod, Ar2 in *; spliter; Col).
assert (HColB : Col O E B) by (unfold Prod, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' A2 A2) as [O' HA2MA2]; Col.
assert (O = O')
  by (apply diff_uniqueness with O E E' A2 A2; auto; apply diff_null; Col).
destruct (sum_exists O E E' HNC A B) as [APB HAPB]; Col.
assert (HColAPB : Col O E APB) by (unfold Sum, Ar2 in *; spliter; Col).
destruct (diff_exists O E E' A B) as [AMB HAMB]; Col; treat_equalities.
assert (HColAMB : Col O E AMB)
  by (apply diff_sum in HAMB; unfold Sum, Ar2 in *; spliter; Col).
destruct (prod_exists O E E' HNC APB AMB) as [O' H]; Col.
assert (O = O')
  by (apply diff_of_squares with O E E' A B A2 A2 APB AMB; auto).
treat_equalities; apply prod_null in H; induction H; treat_equalities;
[right; apply sum_opp|left; apply diff_null_eq with AMB E E']; auto.
Qed.

Lemma diff_2_prod : forall O E E' A B AMB BMA ME,
  Opp O E E' E ME -> Diff O E E' A B AMB -> Diff O E E' B A BMA ->
  Prod O E E' AMB ME BMA.
Proof.
intros O E E' A B AMB BMA ME HOpp HAMB HBMA.
apply opp_prod; auto; apply diff_opp with A B; auto.
Qed.

End T14_prod.
