Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section T12_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma par_reflexivity : forall A B, A<>B -> Par A B A B.
Proof.
    intros.
    unfold Par.
    unfold Par_strict.
    right.
    repeat split.
      assumption.
      assumption.
      apply col_trivial_1.
    apply col_trivial_3.
Qed.

Lemma par_strict_irreflexivity : forall A B,
 ~ Par_strict A B A B.
Proof.
    intros.
    intro.
    unfold Par_strict in H.
    spliter.
    apply H2.
    exists A.
    split; apply col_trivial_1.
Qed.

Lemma not_par_strict_id : forall A B C,
 ~ Par_strict A B A C.
Proof.
    intros.
    intro.
    unfold Par_strict in H.
    spliter.
    apply H2.
    exists A.
    split; Col.
Qed.

Lemma par_id : forall A B C,
 Par A B A C -> Col A B C.
Proof.
    intros.
    unfold Par in H.
    induction H.
      unfold Par_strict in H.
      spliter.
      apply False_ind.
      apply H2.
      exists A.
      Col.
    spliter;Col.
Qed.

Lemma par_strict_not_col_1 : forall A B C D,
 Par_strict A B C D  -> ~ Col A B C.
Proof.
    intros.
    unfold Par_strict in *.
    spliter.
    intro.
    apply H2.
    exists C.
    split;Col.
Qed.

Lemma par_strict_not_col_2 : forall A B C D,
 Par_strict A B C D  -> ~ Col B C D.
Proof.
    intros.
    unfold Par_strict in *.
    spliter.
    intro.
    apply H2.
    exists B.
    split;Col.
Qed.

Lemma par_strict_not_col_3 : forall A B C D,
 Par_strict A B C D  -> ~ Col C D A.
Proof.
    intros.
    unfold Par_strict in *.
    spliter.
    intro.
    apply H2.
    exists A.
    split;Col.
Qed.

Lemma par_strict_not_col_4 : forall A B C D,
 Par_strict A B C D  -> ~ Col A B D.
Proof.
    intros.
    unfold Par_strict in *.
    spliter.
    intro.
    apply H2.
    exists D.
    split;Col.
Qed.

Lemma par_strict_not_cols : forall A B C D,
 Par_strict A B C D -> ~ Col A B C /\ ~ Col B C D /\ ~ Col C D A /\ ~ Col A B D.
Proof.
    intros.
    repeat split.
    apply par_strict_not_col_1 with D, H.
    apply (par_strict_not_col_2 A), H.
    apply par_strict_not_col_3 with B, H.
    apply par_strict_not_col_4 with C, H.
Qed.

Lemma par_id_1 : forall A B C,
 Par A B A C -> Col B A C.
Proof.
    intros.
    assert (H1 := par_id A B C H).
    Col.
Qed.

Lemma par_id_2 : forall A B C,
 Par A B A C -> Col B C A.
Proof.
    intros.
    assert (H1 := par_id A B C H).
    Col.
Qed.

Lemma par_id_3 : forall A B C,
 Par A B A C -> Col A C B.
Proof.
    intros.
    assert (H1 := par_id A B C H).
    Col.
Qed.

Lemma par_id_4 : forall A B C,
 Par A B A C -> Col C B A.
Proof.
    intros.
    assert (H1 := par_id A B C H).
    Col.
Qed.


Lemma par_id_5 : forall A B C,
 Par A B A C -> Col C A B.
Proof.
    intros.
    assert (H1 := par_id A B C H).
    Col.
Qed.

Lemma par_strict_symmetry :forall A B C D,
 Par_strict A B C D -> Par_strict C D A B.
Proof.
    unfold Par_strict.
    intros.
    spliter.
    repeat split.
      assumption.
      assumption.
      apply coplanar_perm_16;assumption.
    intro.
    apply H2.
    ex_and H3 X.
    exists X.
    split; assumption.
Qed.

Lemma par_symmetry :forall A B C D,
 Par A B C D -> Par C D A B.
Proof.
    unfold Par.
    intros.
    induction H.
      left.
      apply par_strict_symmetry.
      assumption.
    spliter.
    right.
    repeat split;try assumption.
      eapply (col_transitivity_1 _ D);Col.
    eapply (col_transitivity_1 _ C);Col.
Qed.

Lemma par_left_comm : forall A B C D,
 Par A B C D -> Par B A C D.
Proof.
    unfold Par.
    intros.
    induction H.
      left.
      unfold Par_strict in *.
      spliter.
      repeat split.
        auto.
        assumption.
        apply coplanar_perm_6;assumption.
      intro.
      apply H2.
      ex_and H3 X.
      exists X.
      Col5.
    right.
    spliter.
    Col5.
Qed.

Lemma par_right_comm : forall A B C D,
 Par A B C D -> Par A B D C.
Proof.
    intros.
    apply par_symmetry in H.
    apply par_symmetry.
    apply par_left_comm.
    assumption.
Qed.

Lemma par_comm : forall A B C D,
 Par A B C D -> Par B A D C.
Proof.
    intros.
    apply par_left_comm.
    apply par_right_comm.
    assumption.
Qed.

Lemma par_strict_left_comm : forall A B C D,
 Par_strict A B C D -> Par_strict B A C D.
Proof.
    unfold Par_strict.
    intros.
    decompose [and] H;clear H.
    repeat split.
      intuition.
      assumption.
      apply coplanar_perm_6;assumption.
    intro.
    apply H4.
    destruct H as [X [HCol1 HCol2]].
    exists X; Col.
Qed.

Lemma par_strict_right_comm : forall A B C D,
 Par_strict A B C D -> Par_strict A B D C.
Proof.
    unfold Par_strict.
    intros.
    decompose [and] H;clear H.
    repeat split.
      assumption.
      intuition.
      apply coplanar_perm_1;assumption.
    intro.
    apply H4.
    destruct H as [X [HCol1 HCol2]].
    exists X; Col.
Qed.

Lemma par_strict_comm : forall A B C D,
 Par_strict A B C D -> Par_strict B A D C.
Proof.
    intros.
    apply par_strict_left_comm in H.
    apply par_strict_right_comm.
    assumption.
Qed.

Lemma par_strict_neq1 : forall A B C D, Par_strict A B C D -> A <> B.
Proof. unfold Par_strict; intros; spliter; auto. Qed.

Lemma par_strict_neq2 : forall A B C D, Par_strict A B C D -> C <> D.
Proof. unfold Par_strict; intros; spliter; auto. Qed.

Lemma par_neq1 : forall A B C D, Par A B C D -> A <> B.
Proof. unfold Par, Par_strict; intros; induction H; spliter; auto. Qed.

Lemma par_neq2 : forall A B C D, Par A B C D -> C <> D.
Proof. unfold Par, Par_strict; intros; induction H; spliter; auto. Qed.

End T12_1.

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:(~Bet ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp2 X1 X2 X2 X3;
      assert (h := not_bet_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq12__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq21__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?B <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq23__neq A B C H H2);clean_reap_hyps
      | H:Bet ?A ?B ?C, H2 : ?C <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= bet_neq32__neq A B C H H2);clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:Le ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D H2 H);clean_reap_hyps
      | H:Le ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= le_diff A B C D (swap_diff B A H2) H);clean_reap_hyps
      | H:Lt ?A ?B ?C ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= lt_diff A B C D H);clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Per ?A ?B ?C, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct A B C H (swap_diff B A H2)); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?B<>?C |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H H2); clean_reap_hyps
      | H:Per ?A ?B ?C, H2 : ?C<>?B |- _ =>
      let T:= fresh in (not_exist_hyp_comm A C);
        assert (T:= per_distinct_1 A B C H (swap_diff C B H2)); clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_at ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:TS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ts_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:OS ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp5 A B A C A D B C B D;
      assert (h := os_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps
      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp6 A B A C A D B C B D C D;
      assert (h := ncop_distincts A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= conga_diff1 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= conga_diff2 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= conga_diff45 A B C A' B' C' H);clean_reap_hyps
      | H:CongA ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= conga_diff56 A B C A' B' C' H);clean_reap_hyps

      | H:(InAngle ?P ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B C B P B;
      assert (h := inangle_distincts A B C P H);decompose [and] h;clear h;clean_reap_hyps
      | H:LeA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lea_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:LtA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lta_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Acute ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := acute_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Obtuse ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp2 A B B C;
      assert (h := obtuse_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:SuppA ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := suppa_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps

      | H:(Orth_at ?X ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_at_distincts A B C U V X H);decompose [and] h;clear h;clean_reap_hyps
      | H:(Orth ?A ?B ?C ?U ?V) |- _ =>
      let h := fresh in
      not_exist_hyp4 A B A C B C U V;
      assert (h := orth_distincts A B C U V H);decompose [and] h;clear h;clean_reap_hyps

      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= par_neq1 A B C D H);clean_reap_hyps
      | H:Par ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= par_neq2 A B C D H);clean_reap_hyps
      | H:Par_strict ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= par_strict_neq1 A B C D H);clean_reap_hyps
      | H:Par_strict ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= par_strict_neq2 A B C D H);clean_reap_hyps
 end.

Ltac assert_ncols :=
repeat
  match goal with
      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(one_side_not_col123 A B X Y);finish)

      | H:OS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(one_side_not_col124 A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B X;assert (~ Col A B X) by (apply(two_sides_not_col A B X Y);finish)

      | H:TS ?A ?B ?X ?Y |- _ =>
     not_exist_hyp_perm_ncol A B Y;assert (~ Col A B Y) by (apply(two_sides_not_col A B Y X);finish)

      | H:~ Coplanar ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := ncop__ncols A B C D H);decompose [and] h;clear h;clean_reap_hyps

      | H:Par_strict ?A ?B ?C ?D |- _ =>
      let h := fresh in
      not_exist_hyp_perm4 A B C D;
      assert (h := par_strict_not_cols A B C D H);decompose [and] h;clear h;clean_reap_hyps
  end.


Hint Resolve
 par_reflexivity par_strict_irreflexivity
 par_strict_symmetry par_strict_comm par_strict_right_comm par_strict_left_comm
 par_symmetry par_comm par_right_comm par_left_comm : par.

Hint Resolve par_strict_not_col_1 par_strict_not_col_2
             par_strict_not_col_3 par_strict_not_col_4 : col.

Ltac Par := eauto with par.

Section T12_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma Par_cases :
  forall A B C D,
  Par A B C D \/ Par B A C D \/ Par A B D C \/ Par B A D C \/
  Par C D A B \/ Par C D B A \/ Par D C A B \/ Par D C B A ->
  Par A B C D.
Proof.
    intros.
    decompose [or]  H;Par.
Qed.

Lemma Par_perm :
  forall A B C D,
  Par A B C D ->
  Par A B C D /\ Par B A C D /\ Par A B D C /\ Par B A D C /\
  Par C D A B /\ Par C D B A /\ Par D C A B /\ Par D C B A.
Proof.
    intros.
    do 7 (split; Par).
Qed.

Lemma Par_strict_cases :
  forall A B C D,
  Par_strict A B C D \/ Par_strict B A C D \/ Par_strict A B D C \/ Par_strict B A D C \/
  Par_strict C D A B \/ Par_strict C D B A \/ Par_strict D C A B \/ Par_strict D C B A ->
  Par_strict A B C D.
Proof.
    intros.
    decompose [or]  H; eauto with par.
Qed.

Lemma Par_strict_perm :
  forall A B C D,
  Par_strict A B C D ->
  Par_strict A B C D /\ Par_strict B A C D /\ Par_strict A B D C /\ Par_strict B A D C /\
  Par_strict C D A B /\ Par_strict C D B A /\ Par_strict D C A B /\ Par_strict D C B A.
Proof.
    intros.
    do 7 (split; Par).
Qed.

End T12_2.

Section T12_2'.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma l12_6 : forall A B C D,
 Par_strict A B C D -> OS A B C D.
Proof.
    intros.
    unfold Par_strict in H.
    spliter.
    assert(HH:= cop__not_two_sides_one_side A B C D).
    apply HH.
      assumption.
      intro.
      apply H2.
      exists C;Col.
      intro.
      apply H2.
      exists D;Col.
    intro.
    apply H2.
    unfold TS in H3.
    spliter.
    ex_and H5 T.
    exists T.
    eauto using bet_col with col.
Qed.

Lemma pars__os3412 : forall A B C D,
 Par_strict A B C D -> OS C D A B.
Proof.
    intros.
    apply l12_6.
    apply par_strict_symmetry.
    assumption.
Qed.

Lemma perp_dec : forall A B C D, Perp A B C D \/ ~ Perp A B C D.
Proof.
    intros.
    induction (col_dec A B C).
      induction (perp_in_dec C A B C D).
        left.
        apply l8_14_2_1a with C;auto.
      right.
      intro.
      apply H0. clear H0.
      apply perp_in_right_comm.
      apply (l8_15_1 A B D C).
        apply perp_distinct in H1.
        intuition.
      apply perp_right_comm;assumption.
    elim (l8_18_existence A B C H); intros P HP.
    spliter.
    induction (eq_dec_points C D).
      subst.
      right.
      intro.
      assert (A <> B /\ D <> D) by (apply perp_distinct;assumption).
      intuition.
    induction (col_dec P C D).
      left.
      assert (A <> B /\ C <> P) by (apply perp_distinct;assumption).
      spliter.
      apply perp_col1 with P;Col.
    right.
    intro.
    apply H3.
    apply col_permutation_2, cop_perp2__col with A B; [Cop|apply perp_sym;assumption..].
Qed.

Lemma col_cop2_perp2__col : forall X1 X2 Y1 Y2 A B,
 Perp X1 X2 A B -> Perp Y1 Y2 A B -> Col X1 Y1 Y2 ->
 Coplanar A B X2 Y1 -> Coplanar A B X2 Y2 -> Col X2 Y1 Y2.
Proof.
    intros.
    induction(eq_dec_points X1 Y2).
      subst Y2.
      assert(Perp Y1 X1 A B).
        eapply perp_col.
          intro.
          treat_equalities.
          apply perp_distinct in H0.
          intuition.
          apply H0.
        Col.
      apply col_permutation_1.
      apply cop_perp2__col with A B.
        assumption.
        apply H.
      apply perp_left_comm.
      assumption.
    assert(Perp Y2 X1 A B).
      eapply perp_col.
        auto.
        apply perp_left_comm.
        apply H0.
      Col.
    assert(Perp X1 Y2 A B).
      eapply perp_left_comm.
      assumption.
    induction(eq_dec_points X1 Y1).
      subst Y1.
      apply col_permutation_2.
      apply cop_perp2__col with A B; Cop.
    assert(Perp X1 Y1 A B).
      eauto using perp_left_comm, perp_col with col.
    assert (Col X1 X2 Y1).
      apply cop_perp2__col with A B; Perp; Cop.
    ColR.
Qed.

Lemma col_perp2_ncol__col : forall X1 X2 Y1 Y2 A B,
 Perp X1 X2 A B -> Perp Y1 Y2 A B ->
 Col X1 Y1 Y2 -> ~ Col X1 A B ->
 Col X2 Y1 Y2.
Proof.
    intros.
    assert (Coplanar A B X2 Y1).
      induction (eq_dec_points X1 Y1).
        subst; Cop.
      apply coplanar_trans_1 with X1; [Cop..|].
      assert (Perp Y1 X1 A B) by (apply perp_col with Y2; Col); Cop.
    assert (Coplanar A B X2 Y2).
      induction (eq_dec_points X1 Y2).
        subst; Cop.
      apply coplanar_trans_1 with X1; [Cop..|].
      assert (Perp Y2 X1 A B) by (apply perp_col with Y1; Perp; Col); Cop.
    apply col_cop2_perp2__col with X1 A B; assumption.
Qed.

Lemma l12_9 : forall A1 A2 B1 B2 C1 C2,
 Coplanar C1 C2 A1 B1 -> Coplanar C1 C2 A1 B2 ->
 Coplanar C1 C2 A2 B1 -> Coplanar C1 C2 A2 B2 ->
 Perp A1 A2 C1 C2 -> Perp B1 B2 C1 C2 ->
 Par A1 A2 B1 B2.
Proof.
    intros A1 A2 B1 B2 C1 C2.
    intros.
    unfold Par.
    unfold Par_strict.
    assert(A1 <> A2 /\ C1 <> C2) by (apply perp_distinct;assumption).
    assert(B1 <> B2 /\ C1 <> C2) by (apply perp_distinct;assumption).
    spliter.
    induction(col_dec A1 B1 B2).
      right.
      repeat split; auto.
      apply col_cop2_perp2__col with A1 C1 C2; auto.
    (***********************************)
    left.
    repeat split.
      assumption.
      assumption.
      induction (perp_not_col2 C1 C2 A1 A2); Perp.
        apply coplanar_pseudo_trans with C1 C2 A1; Cop.
        apply coplanar_pseudo_trans with C1 C2 A2; Cop.
    intro.
    ex_and H10 AB.
    apply H9.
    induction(eq_dec_points AB A1).
      subst AB.
      assumption.
    assert(Perp A1 AB C1 C2) by (eauto using perp_col with col).
    apply col_cop2_perp2__col with AB C1 C2; Perp.
Qed.

(** We show here that from the axioms of neutral geometry we can deduce the existence of a parallel line. 
This is important because it shows that axioms of neutral geometry are inconsistent with those of elliptic geometry as 
elliptic geometry assumes that no parallel lines exist. *)
(** This corresponds to l12_10 in Tarski's book. *)

Lemma parallel_existence : forall A B P, A <> B ->
 exists C, exists D, C<>D /\ Par A B C D /\ Col P C D.
Proof.
    intros.
    induction(col_dec A B P).
      exists A.
      exists B.
      repeat split.
        assumption.
        Par.
      Col.
    assert(exists P', Col A B P' /\ Perp A B P P').
      eapply l8_18_existence.
      assumption.
    ex_and H1 P'.
    assert(P <> P').
      intro.
      subst P'.
      contradiction.
    induction(eq_dec_points P' A).
      subst P'.
      assert(exists Q, Per Q P A /\ Cong Q P A B /\ OS A P Q B).
        eapply ex_per_cong.
          auto.
          assumption.
          apply col_trivial_2.
        intro.
        apply H0.
        Col.
      ex_and H4 Q.
      exists P.
      exists Q.
      assert(P <> Q).
        intro.
        treat_equalities.
        intuition.
      repeat split.
        assumption.
        apply l12_9 with P A; Cop.
        apply per_perp_in in H4.
          apply perp_in_perp_bis in H4.
          induction H4.
            apply perp_distinct in H4.
            spliter.
            absurde.
          apply perp_left_comm.
          assumption.
          auto.
        assumption.
      Col.
    assert(exists Q, Per Q P P' /\ Cong Q P A B /\ OS P' P Q A).
      eapply ex_per_cong.
        auto.
        assumption.
        Col.
      intro.
      apply H0.
      eapply (col_transitivity_1 _ P').
        auto.
        Col.
      Col.
    ex_and H5 Q.
    exists P.
    exists Q.
    assert(P <> Q).
      intro.
      treat_equalities.
      intuition.
    repeat split.
      assumption.
      apply l12_9 with P P'.
        exists P; left; split; Col.
        Cop.
        exists P; left; split; Col.
        apply coplanar_perm_3, col_cop__cop with A; Col; Cop.
        apply H2.
      apply per_perp_in in H5.
        apply perp_in_perp_bis in H5.
        induction H5.
          apply perp_distinct in H5.
          spliter.
          absurde.
        apply perp_left_comm.
        assumption.
        auto.
      assumption.
    Col.
Qed.

Lemma par_col_par : forall A B C D D',
 C <> D' -> Par A B C D -> Col C D D' -> Par A B C D'.
Proof.
    intros.
    unfold Par in *.
    induction H0.
      left.
      unfold Par_strict in *.
      spliter.
      repeat split.
        assumption.
        assumption.
        apply col_cop__cop with D; auto.
      intro.
      apply H4.
      ex_and H5 P.
      exists P.
      split.
        assumption.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H.
        Col.
      Col.
    right.
    spliter.
    repeat split.
      assumption.
      assumption.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H2.
        assumption.
      Col.
    apply col_permutation_2.
    eapply col_transitivity_1.
      apply H2.
      assumption.
    Col.
Qed.

Lemma parallel_existence1 : forall A B P, A <> B -> exists Q, Par A B P Q.
Proof.
    intros.
    assert (T:= parallel_existence A B P H).
    decompose [and ex] T;clear T.
    elim (eq_dec_points x P);intro.
      subst.
      exists x0.
      intuition.
    exists x.
    apply par_right_comm.
    apply par_col_par with x0; Par.
    Col.
Qed.

Lemma par_not_col : forall A B C D X, Par_strict A B C D -> Col X A B -> ~Col X C D.
Proof.
    intros.
    unfold Par_strict in H.
    intro.
    spliter.
    apply H4.
    exists X; Col.
Qed.

Lemma not_strict_par1 : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B C.
Proof.
    intros.
    unfold Par in H.
    induction H.
      unfold Par_strict in H.
      spliter.
      assert(exists X, Col X A B /\ Col X C D).
        exists X.
        split; Col.
      contradiction.
    spliter.
    apply col_permutation_1.
    eapply col_transitivity_1.
      apply H2.
      Col.
    Col.
Qed.

Lemma not_strict_par2 : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B D.
Proof.
    intros.
    eapply not_strict_par1.
      apply par_right_comm.
      apply H.
      apply H0.
    Col.
Qed.

Lemma not_strict_par : forall A B C D X, Par A B C D -> Col A B X -> Col C D X -> Col A B C /\ Col A B D.
Proof.
    intros.
    split.
      eapply not_strict_par1.
        apply H.
        apply H0.
      assumption.
    eapply not_strict_par2.
      apply H.
      apply H0.
    assumption.
Qed.

Lemma not_par_not_col : forall A B C, A <> B -> A <> C -> ~Par A B A C -> ~Col A B C.
Proof.
    intros.
    intro.
    apply H1.
    unfold Par.
    right.
    repeat split.
      assumption.
      assumption.
      apply col_trivial_1.
    Col.
Qed.

Lemma not_par_inter_uniqueness : forall A B C D X Y,
  A <> B -> C <> D -> ~Par A B C D -> Col A B X -> Col C D X -> Col A B Y -> Col C D Y ->
  X = Y.
Proof.
    intros.
    induction(eq_dec_points C Y).
      subst Y.
      induction (eq_dec_points C X).
        subst X.
        reflexivity.
      eapply l6_21.
        2: apply H.
        2: apply H3.
        intro.
        apply H1.
        unfold Par.
        right.
        repeat split; assumption || ColR.
        assumption.
        assumption.
        assumption.
    eapply l6_21.
      2: apply H0.
      2: apply H2.
      intro.
      apply H1.
      unfold Par.
      right.
      repeat split; ColR || assumption.
      assumption.
      assumption.
      assumption.
Qed.

Lemma inter_uniqueness_not_par : forall A B C D P,
  ~Col A B C -> Col A B P -> Col C D P -> ~Par A B C D.
Proof.
    intros.
    intro.
    unfold Par in H2.
    induction H2.
      unfold Par_strict in H2.
      spliter.
      apply H5.
      exists P.
      Col5.
    spliter.
    apply H.
    ColR.
Qed.

Lemma col_not_col_not_par :
 forall A B C D,
 (exists P, Col A B P /\ Col C D P) ->
 (exists Q, Col C D Q /\ ~Col A B Q) -> ~Par A B C D.
Proof.
    intros.
    ex_and H P.
    ex_and H0 Q.
    intro.
    unfold Par in H3.
    induction H3.
      unfold Par_strict in H3.
      spliter.
      apply H6.
      exists P.
      Col5.
    spliter.
    apply H2.
    eapply col3.
      apply H4.
      Col.
      Col.
    Col.
Qed.

Lemma par_distincts : forall A B C D,
 Par A B C D -> (Par A B C D /\ A <> B /\ C <> D).
Proof.
    intros.
    split.
      assumption.
    unfold Par in H.
    induction H.
      unfold Par_strict in H.
      spliter.
      split; assumption.
    spliter.
    split; assumption.
Qed.

Lemma par_not_col_strict : forall A B C D P,
 Par A B C D -> Col C D P -> ~Col A B P -> Par_strict A B C D.
Proof.
    intros.
    apply par_symmetry in H.
    unfold Par in H.
    induction H.
      apply par_strict_symmetry.
      assumption.
    spliter.
    unfold Par_strict.
    repeat split; auto.
      exists C; left; split; Col.
    intro.
    ex_and H5 X.
    apply H1.
    assert(Col A C D).
      eapply (col_transitivity_1 _ B).
        assumption.
        Col.
      Col.
    assert(Col B C D).
      eapply (col_transitivity_1 _ A).
        auto.
        Col.
      Col.
    eapply col3.
      apply H.
      Col.
      Col.
    Col.
Qed.

Lemma all_one_side_par_strict : forall A B C D,
 C <> D -> (forall P, Col C D P -> OS A B C P) ->
 Par_strict A B C D.
Proof.
    intros.
    unfold Par_strict.
    repeat split.
      assert(HH:=H0 D (col_trivial_2 _ _)).
      unfold OS in HH.
      ex_and HH C0.
      unfold TS in H1.
      spliter.
        intro.
        subst B.
        Col.
      assumption.
      apply os__coplanar, H0; Col.
    intro.
    ex_and H1 X.
    assert(HH:= H0 X (col_permutation_1 _ _ _ H2) ).
    unfold OS in HH.
    ex_and HH M.
    unfold TS in H4.
    spliter.
    contradiction.
Qed.

Lemma par_col_par_2 : forall A B C D P,
 A <> P -> Col A B P -> Par A B C D -> Par A P C D.
Proof.
    intros.
    unfold Par in *.
    induction H1.
      left.
      unfold Par_strict in *.
      spliter.
      repeat split; auto.
      apply coplanar_perm_16, col_cop__cop with B; Cop.
      intro.
      ex_and H5 X.
      apply H4.
      exists X.
      split.
        ColR.
      Col.
    right.
    spliter.
    repeat split;auto.
    assert(Col A B D).
      ColR.
    assert(Col A B C).
      ColR.
    eapply col3.
      apply H1.
      Col.
      Col.
    Col.
Qed.


Lemma par_col2_par : forall A B C D E F,
 E <> F -> Par A B C D -> Col C D E -> Col C D F -> Par A B E F.
Proof.
    intros.
    induction (eq_dec_points C E).
      subst E.
      eapply par_col_par.
        assumption.
        apply H0.
      assumption.
    eapply par_col_par.
      assumption.
      apply par_right_comm.
      eapply par_col_par.
        apply H3.
        apply H0.
      assumption.
    apply col_permutation_2.
    eapply col_transitivity_1.
      apply par_distincts in H0.
      spliter.
      apply H5.
      assumption.
    assumption.
Qed.

Lemma par_col2_par_bis : forall A B C D E F,
 E <> F -> Par A B C D -> Col E F C -> Col E F D -> Par A B E F.
Proof.
intros.
apply par_col2_par with C D; Col; ColR.
Qed.

Lemma par_strict_col_par_strict : forall A B C D E,
 C <> E -> Par_strict A B C D -> Col C D E ->
 Par_strict A B C E.
Proof.
    intros.
    assert(Par C E A B).
      eapply par_col_par_2.
        auto.
        apply H1.
      apply par_symmetry.
      left.
      assumption.
    induction H2.
      apply par_strict_symmetry.
      assumption.
    unfold Par_strict in H0.
    spliter.
    apply False_ind.
    apply H8.
    exists C.
    split; Col.
Qed.

Lemma par_strict_col2_par_strict : forall A B C D E F,
 E <> F -> Par_strict A B C D -> Col C D E -> Col C D F ->
 Par_strict A B E F.
Proof.
    intros.
    unfold Par_strict in *.
    spliter.
    repeat split.
      assumption.
      assumption.
      apply col2_cop__cop with C D; assumption.
    intro.
    apply H5.
    ex_and H6 X.
    exists X.
    split.
      assumption.
    assert(Col C E F).
      eapply col_transitivity_1.
        apply H3.
        assumption.
      assumption.
    assert(Col D E F).
      eapply (col_transitivity_1 _ C).
        auto.
        Col.
      Col.
    eapply col3.
      apply H.
      Col.
      Col.
    Col.
Qed.

Lemma line_dec : forall B1 B2 C1 C2, (Col C1 B1 B2 /\ Col C2 B1 B2) \/ ~ (Col C1 B1 B2 /\ Col C2 B1 B2).
Proof.
    intros.
    induction (col_dec C1 B1 B2); induction (col_dec C2 B1 B2);tauto.
Qed.

Lemma par_distinct : forall A B C D, Par A B C D -> A <> B /\ C <> D.
Proof.
    intros.
    induction H.
      unfold Par_strict in H; intuition.
    intuition.
Qed.

Lemma par_col4__par : forall A B C D E F G H, E <> F -> G <> H -> Par A B C D ->
 Col A B E -> Col A B F -> Col C D G -> Col C D H -> Par E F G H.
Proof.
    intros A B C D E F G H.
    intros.
    apply (par_col2_par _ _ C D); auto.
    apply par_symmetry.
    apply (par_col2_par _ _ A B); auto.
    apply par_symmetry; auto.
Qed.

Lemma par_strict_col4__par_strict : forall A B C D E F G H, E <> F -> G <> H ->
 Par_strict A B C D -> Col A B E -> Col A B F -> Col C D G -> Col C D H ->
 Par_strict E F G H.
Proof.
    intros A B C D E F G H.
    intros.
    apply (par_strict_col2_par_strict _ _ C D); auto.
    apply par_strict_symmetry.
    apply (par_strict_col2_par_strict _ _ A B); auto.
    apply par_strict_symmetry; auto.
Qed.

Lemma par_strict_one_side : forall A B C D P,
 Par_strict A B C D -> Col C D P -> OS A B C P.
Proof.
  intros A B C D P HPar HCol.
  destruct (eq_dec_points C P).
    subst P; apply par_strict_not_col_1 in HPar; apply one_side_reflexivity; Col.
  apply l12_6, par_strict_col_par_strict with D; trivial.
Qed.

Lemma par_strict_all_one_side : forall A B C D,
 Par_strict A B C D -> (forall P, Col C D P -> OS A B C P).
Proof.
    intros.
    eapply par_strict_one_side.
      apply H.
    assumption.
Qed.

Lemma inter_distincts : forall A B C D X, Inter A B C D X -> A <> B /\ C <> D.
Proof.
    intros.
    destruct H as [HAB [[P []] _]].
    assert_diffs.
    split; auto.
Qed.

Lemma inter_trivial : forall A B X, ~ Col A B X -> Inter A X B X X.
Proof.
    intros.
    assert_diffs.
    unfold Inter.
    repeat split; Col.
      exists B.
      split.
        Col.
      intro.
      apply H.
      Col.
Qed.

Lemma inter_sym : forall A B C D X, Inter A B C D X -> Inter C D A B X.
Proof.
    intros.
    unfold Inter in *.
    spliter.
    ex_and H0 P.
    assert(A <> B).
      intro.
      subst B.
      apply H3.
      Col.
    split.
      assumption.
    split.
      induction(eq_dec_points A X).
        treat_equalities.
        exists B.
        split.
          Col.
        intro.
        apply H3.
        eapply col3.
          apply H.
          Col.
          Col.
        Col.
      exists A.
      split.
        Col.
      intro.
      apply H3.
      assert(Col A P X).
        eapply col3.
          apply H.
          Col.
          Col.
        Col.
      ColR.
    split; Col.
Qed.

Lemma inter_left_comm : forall A B C D X, Inter A B C D X -> Inter B A C D X.
Proof.
    intros.
    unfold Inter in *.
    spliter.
    ex_and H0 P.
    split.
      assumption.
    split.
      exists P.
      split.
        assumption.
      intro.
      apply H3.
      Col.
    split; Col.
Qed.

Lemma inter_right_comm : forall A B C D X, Inter A B C D X -> Inter A B D C X.
Proof.
    intros.
    unfold Inter in *.
    spliter.
    ex_and H0 P.
    split.
      auto.
    split.
      exists P.
      split.
        Col.
      assumption.
    split; Col.
Qed.

Lemma inter_comm : forall A B C D X, Inter A B C D X -> Inter B A D C X.
Proof.
    intros.
    apply inter_left_comm.
    apply inter_right_comm.
    assumption.
Qed.

(** In the proof given by Tarski on page 125 the distinction of cases is explicit.
This is a good example on the significance of decidability. *)
Lemma l12_17 : forall A B C D P,
 A <> B -> Midpoint P A C -> Midpoint P B D -> Par A B C D.
Proof.
    intros.
    induction(col_dec A B P).
      unfold Par.
      right.
      induction(eq_dec_points A P).
        subst P.
        apply is_midpoint_id in H0.
        subst C.
        repeat split.
          assumption.
          intro.
          treat_equalities.
          apply l7_2 in H1.
          apply is_midpoint_id in H1.
          contradiction.
          apply col_trivial_1.
        unfold Midpoint in H1.
        spliter.
        apply bet_col.
        assumption.
      induction(eq_dec_points B P).
        subst P.
        apply is_midpoint_id in H1.
        subst D.
        repeat split.
          assumption.
          intro.
          subst C.
          apply l7_2 in H0.
          apply is_midpoint_id in H0.
          auto.
          unfold Midpoint in H0.
          spliter.
          apply bet_col in H0 .
          Col.
        apply col_trivial_3.
      assert(HH0 := H0).
      assert(HH1:= H1).
      unfold Midpoint in H0.
      unfold Midpoint in H1.
      spliter.
      apply bet_col in H1.
      apply bet_col in H0.
      assert(Col B C P).
        eapply col_permutation_1.
        eapply (col_transitivity_1 _ A).
          auto.
          Col.
        Col.
      assert(Col B C D).
        eapply (col_transitivity_1 _ P).
          assumption.
          Col.
        Col.
      repeat split.
        assumption.
        intro.
        treat_equalities.
        intuition.
        induction(eq_dec_points A D).
          subst D.
          apply col_trivial_3.
        assert(Col C D P).
          eapply (col_transitivity_1 _ B).
            intro.
            subst C.
            assert(A = D).
              eapply symmetric_point_uniqueness.
                eapply l7_2.
                apply HH0.
              assumption.
            contradiction.
            Col.
          Col.
        induction(eq_dec_points C P).
          treat_equalities.
          intuition.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ P).
          assumption.
          Col.
        Col.
      assumption.
    (* cas non degenere *)
    assert(exists E, Col A B E /\ Perp A B P E).
      eapply l8_18_existence.
      assumption.
    ex_and H3 E.
    assert(A <> P).
      intro.
      treat_equalities.
      apply H2.
      apply col_trivial_3.
    induction(eq_dec_points A E).
      treat_equalities.
      assert(Per P A B).
        eapply perp_in_per.
        apply perp_in_comm.
        eapply perp_perp_in.
        apply perp_sym.
        apply perp_comm.
        assumption.
      prolong B A B' B A.
      prolong B' P D' B' P.
      assert(Midpoint C D D').
        eapply symmetry_preserves_midpoint.
          apply H1.
          apply H0.
          split.
            apply H8.
          Cong.
        split.
          assumption.
        Cong.
      assert(Per P A B').
        eapply per_col.
          apply H.
          assumption.
        apply bet_col in H6.
        Col.
      ex_and H3 B''.
      assert(B' = B'').
        eapply symmetric_point_uniqueness.
          split.
            apply H6.
          Cong.
        assumption.
      subst B''.
      assert(Cong P D P D').
        apply  (cong_transitivity _ _ B P).
          unfold Midpoint in H1.
          spliter.
          Cong.
        apply  (cong_transitivity _ _ B' P).
          Cong.
        Cong.
      assert(Per P C D).
        unfold Per.
        exists D'.
        split; assumption.
      apply per_perp_in in H14.
        apply perp_in_perp_bis in H14.
        induction H14.
          apply perp_distinct in H14.
          intuition.
        eapply l12_9 with P A; Cop.
        apply perp_sym.
        eapply perp_col.
          auto.
          apply H14.
        unfold Midpoint in H0.
        spliter.
        apply bet_col in H0.
        Col.
        intro.
        treat_equalities.
        apply l7_2 in H0.
        eapply is_midpoint_id in H0.
        auto.
      intro.
      subst D.
      assert(C = D').
        apply is_midpoint_id.
        assumption.
      subst D'.
      assert(A = B).
        eapply symmetric_point_uniqueness.
          apply l7_2.
          apply H0.
        apply l7_2.
        assumption.
      auto.
    prolong E P F E P.
    assert(Col C D F).
      eapply mid_preserves_col.
        2: apply H0.
        2:apply H1.
        apply H3.
      split.
        assumption.
      Cong.
    prolong A E A' A E.
    prolong A' P C' A' P.
    assert(Midpoint F C C').
      eapply symmetry_preserves_midpoint.
        apply H0.
        split.
          apply H7.
        Cong.
        split.
          apply H12.
        Cong.
      split.
        assumption.
      Cong.
    assert(Per P E A).
      eapply perp_in_per.
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      eapply perp_col.
        assumption.
        apply perp_right_comm.
        apply H4.
      Col.
    assert(Cong P C P C').
      eapply (cong_transitivity _ _ P A).
        unfold Midpoint in H0.
        spliter.
        Cong.
      eapply (cong_transitivity _ _ P A').
        unfold Per in H15.
        ex_and H15 A''.
        assert( A' = A'').
          eapply symmetric_point_uniqueness.
            split.
              apply H10.
            Cong.
          assumption.
        subst A''.
        assumption.
      Cong.
    assert(Per P F C).
      unfold Per.
      exists C'.
      split.
        assumption.
      assumption.
    apply per_perp_in in H17.
      apply perp_in_comm in H17.
      apply perp_in_perp_bis in H17.
      induction H17.
        apply l12_9 with P E.
          exists P; left; split; Col.
          exists B; right; right; split; Col.
          exists A; right; right; split; Col.
          exists P; left; split; Col.
          apply H4.
        eapply perp_col.
          intro.
          subst D.
          assert (A = B).
            eapply symmetric_point_uniqueness.
              apply l7_2.
              apply H0.
            apply l7_2.
            assumption.
          auto.
          apply perp_sym.
          eapply perp_col.
            intro.
            treat_equalities.
            apply perp_distinct in H17.
            spliter.
            auto.
            apply perp_left_comm.
            apply H17.
          apply bet_col in H7.
          Col.
        Col.
      apply perp_distinct in H17.
      spliter.
      tauto.
      intro.
      treat_equalities.
      apply perp_distinct in H4.
      spliter.
      tauto.
    intro.
    subst C.
    assert(F = C').
      apply is_midpoint_id .
      assumption.
    treat_equalities.
    assert(A = E).
      eapply symmetric_point_uniqueness.
        apply l7_2.
        apply H0.
      split.
        apply between_symmetry.
        assumption.
      Cong.
    tauto.
Qed.

Lemma l12_18_a :
  forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par A B C D.
Proof.
    intros.
    assert(Midpoint P A C /\ Midpoint P B D) by (apply l7_21; assumption).
    spliter.
    eapply l12_17.
      intro.
      subst B.
      apply H1.
      apply col_trivial_1.
      apply H5.
    apply H6.
Qed.

Lemma l12_18_b :
  forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par B C D A.
Proof.
    intros.
    assert(Midpoint P A C /\ Midpoint P B D) by (apply l7_21; assumption).
    eapply l12_18_a.
      assumption.
      Cong.
      intro.
      apply H1.
      assert(Col B C P).
        eapply col_transitivity_1.
          apply H2.
          Col.
        Col.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ P).
        intro.
        subst P.
        spliter.
        apply l7_2 in H5.
        apply is_midpoint_id in H5.
        subst C.
        apply H1.
        apply col_trivial_3.
        Col.
      Col.
      intro.
      subst C.
      apply H1.
      apply col_trivial_3.
      apply H4.
    Col.
Qed.

Lemma l12_18_c :
 forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  TS B D A C.
Proof.
    intros.
    assert(Midpoint P A C /\ Midpoint P B D) by (apply l7_21; assumption).
    unfold TS.
    repeat split.
      intro.
      apply H1.
      assert(Col A B P).
        apply col_permutation_2.
        eapply (col_transitivity_1 _ D).
          assumption.
          Col.
        Col.
      eapply (col_transitivity_1 _ P).
        intro.
        subst P.
        spliter.
        apply is_midpoint_id in H5.
        subst C.
        apply H1.
        apply col_trivial_3.
        Col.
      Col.
      intro.
      apply H1.
      assert(Col B P C).
        eapply (col_transitivity_1 _ D).
          assumption.
          Col.
        Col.
      apply col_permutation_1.
      eapply (col_transitivity_1 _ P).
        intro.
        subst P.
        spliter.
        apply l7_2 in H5.
        apply is_midpoint_id in H5.
        subst C.
        apply H1.
        apply col_trivial_3.
        Col.
      Col.
    exists P.
    split.
      Col.
    spliter.
    unfold Midpoint in H5.
    tauto.
Qed.

Lemma l12_18_d :
 forall A B C D P,
 Cong A B C D -> Cong B C D A -> ~Col A B C ->
 B <> D -> Col A P C -> Col B P D ->
 TS A C B D.
Proof.
    intros.
    assert(Midpoint P A C /\ Midpoint P B D) by (apply l7_21; assumption).
    eapply (l12_18_c _ _ _ _ P).
      Cong.
      Cong.
      intro.
      apply H1.
      assert(Col A B P).
        eapply col_permutation_2.
        eapply col_transitivity_1.
          apply H2.
          Col.
        Col.
      eapply (col_transitivity_1 _ P).
        intro.
        subst P.
        spliter.
        apply is_midpoint_id in H5.
        subst C.
        contradiction.
        Col.
      Col.
      intro.
      subst C.
      apply H1.
      apply col_trivial_3.
      Col.
    Col.
Qed.

Lemma l12_18 :
 forall A B C D P,
  Cong A B C D -> Cong B C D A -> ~Col A B C ->
  B <> D -> Col A P C -> Col B P D ->
  Par A B C D /\ Par B C D A /\ TS B D A C /\ TS A C B D.
Proof.
    intros.
    split.
      apply (l12_18_a _ _ _ _ P); assumption.
    split.
      apply (l12_18_b _ _ _ _ P); assumption.
    split.
      apply (l12_18_c _ _ _ _ P); assumption.
    apply (l12_18_d _ _ _ _ P); assumption.
Qed.

Lemma par_two_sides_two_sides :
  forall A B C D,
  Par A B C D -> TS B D A C ->
  TS A C B D.
Proof.
    intros.
    apply par_distincts in H.
    spliter.
    unfold Par in H.
    induction H.
      assert(A <> C).
        intro.
        subst C.
        unfold Par_strict in H.
        spliter.
        apply H5.
        exists A.
        split; apply col_trivial_1.
      unfold TS in *.
      assert (~ Col A B D).
        spliter.
        assumption.
      spliter.
      ex_and H6 T.
      repeat split.
        intro.
        assert(Col T B C).
          apply col_permutation_1.
          eapply (col_transitivity_1 _ A).
            auto.
            apply bet_col in H7.
            Col.
          Col.
        apply H5.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ T).
          intro.
          treat_equalities.
          unfold Par_strict in H.
          spliter.
          apply H9.
          exists C.
          split.
            Col.
          apply col_trivial_1.
          Col.
        Col.
        intro.
        assert(Col T C D).
          apply col_permutation_2.
          apply (col_transitivity_1 _ A).
            auto.
            Col.
          apply bet_col in H7.
          Col.
        apply H5.
        apply col_permutation_1.
        apply (col_transitivity_1 _ T).
          intro.
          treat_equalities.
          unfold Par_strict in H.
          spliter.
          apply H9.
          exists A.
          split.
            apply col_trivial_1.
          Col.
          Col.
        Col.
      exists T.
      split.
        apply bet_col in H7.
        Col.
      unfold Col in H6.
      induction H6.
        assert(HH:= outer_pasch C D T A B (between_symmetry _ _ _ H7) (between_symmetry _ _ _ H6)).
        ex_and HH X.
        unfold Par_strict in H.
        spliter.
        apply False_ind.
        apply H12.
        exists X.
        apply bet_col in H8.
        apply bet_col in H9.
        split; Col.
      induction H6.
        assert(HH:= outer_pasch A B T C D H7 H6).
        ex_and HH X.
        apply False_ind.
        unfold Par_strict in H.
        spliter.
        apply H12.
        exists X.
        apply bet_col in H8.
        apply bet_col in H9.
        split; Col.
      apply between_symmetry.
      assumption.
    unfold TS in H0.
    spliter.
    apply False_ind.
    apply H3.
    apply col_permutation_1.
    eapply (col_transitivity_1 _ C).
      auto.
      Col.
    Col.
Qed.

Lemma par_one_or_two_sides :
 forall A B C D,
  Par_strict A B C D ->
 TS A C B D /\ TS B D A C \/ OS A C B D /\ OS B D A C.
Proof.
    intros.
    induction(two_sides_dec A C B D).
      left.
      split.
        assumption.
      apply par_two_sides_two_sides.
        apply par_comm.
        unfold Par.
        left.
        assumption.
      assumption.
    right.
    assert(HH:=H).
    unfold Par_strict in H.
    spliter.
    assert(A <> C).
      intro.
      subst C.
      apply H3.
      exists A.
      split; Col.
    assert(B <> D).
      intro.
      subst D.
      apply H3.
      exists B.
      split; Col.
    split.
      apply cop__not_two_sides_one_side; Cop.
        intro.
        apply H3.
        exists C.
        split; Col.
        intro.
        apply H3.
        exists A.
        split; Col.
    apply cop__not_two_sides_one_side; Cop.
      intro.
      apply H3.
      exists D.
      split; Col.
      intro.
      apply H3.
      exists B.
      split; Col.
    intro.
    apply H0.
    apply par_two_sides_two_sides.
      left.
      assumption.
    assumption.
Qed.

Lemma l12_21_b : forall A B C D,
 TS A C B D ->
 CongA B A C D C A -> Par A B C D.
Proof.
    intros.
    apply conga_distinct in H0.
    spliter.
    assert(~Col A B C).
      intro.
      unfold TS in H.
      spliter.
      apply col_permutation_4 in H5.
      assert(Col D C A).
        eapply col_conga_col.
          apply H5.
        assumption.
      contradiction.
    assert(A <> B /\ C <> D).
      auto.
    spliter.
    assert(HH:=segment_construction_3 C D A B H7 H6).
    ex_and HH D'.
    assert(CongA B A C D' C A).
      eapply l11_10.
        apply H0.
        apply out_trivial.
        assumption.
        apply out_trivial.
        assumption.
        apply l6_6.
        assumption.
      apply out_trivial.
      assumption.
    assert(Cong D' A B C).
      eapply cong2_conga_cong.
        apply conga_sym.
        apply H10.
        Cong.
      Cong.
    assert(TS A C D' B).
      eapply l9_5.
        apply l9_2.
        apply H.
        apply col_trivial_3.
      assumption.
    unfold TS in H12.
    spliter.
    ex_and H14 M.
    assert(B <> D').
      intro.
      treat_equalities.
      contradiction.
    assert(Midpoint M A C /\ Midpoint M B D').
      apply l7_21.
        assumption.
        assumption.
        Cong.
        Cong.
        Col.
      apply bet_col in H15.
      Col.
    spliter.
    assert(Par A B C D').
      eapply l12_17.
        assumption.
        apply H17.
      assumption.
    eapply par_col_par.
      auto.
      apply H19.
    apply out_col in H8.
    Col.
Qed.

Lemma l12_22_aux :
 forall A B C D P,
  P <> A -> A <> C -> Bet P A C -> OS P A B D ->
  CongA B A P D C P ->
  Par A B C D.
Proof.
    intros.
    assert (P<>C) by (intro; Between).
    prolong B A B' B A .
    spliter.
    assert(CongA P A B C A B').
      apply l11_14.
        assumption.
        assumption.
        auto.
        assumption.
        unfold CongA in H3.
        spliter.
        auto.
        intro.
        treat_equalities.
        unfold CongA in H3.
        tauto.
    assert(CongA D C A D C P).
      eapply l11_10.
        apply conga_refl.
          3: apply out_trivial.
          unfold CongA in H3.
          tauto.
        5:apply out_trivial.
        auto.
        unfold CongA in H3.
        tauto.
        apply between_symmetry in H1.
        apply bet_out in H1.
          assumption.
          auto.
          auto.
        apply out_trivial.
        unfold CongA in H3.
        tauto.
      auto.
    assert(Par A B' C D).
      eapply l12_21_b.
        assert(~Col B P A).
          unfold OS in H2.
          ex_and H2 T.
          unfold TS in H2.
          tauto.
        assert(TS P A B B').
          unfold TS.
          repeat split.
            assumption.
            intro.
            apply H9.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ B').
              intro.
              treat_equalities.
              unfold CongA in H3.
              tauto.
              apply bet_col in H1.
              Col.
            Col.
          exists A.
          split.
            Col.
          assumption.
        apply l9_2.
        eapply l9_8_2.
          eapply col_two_sides.
            3:apply invert_two_sides.
            3: apply H10.
            apply bet_col in H1.
            Col.
          assumption.
        eapply col_one_side.
          3: apply invert_one_side.
          3: apply H2.
          apply bet_col in H1.
          Col.
        assumption.
      eapply conga_trans.
        apply conga_sym.
        apply conga_comm.
        apply H7.
      eapply conga_trans.
        apply H3.
      apply conga_sym.
      assumption.
    apply par_symmetry.
    eapply par_col_par.
      2: apply par_symmetry.
      2:apply H9.
      unfold CongA in H3.
      spliter.
      auto.
    apply bet_col in H1.
    Col.
Qed.


Lemma l12_22_b :
 forall A B C D P,
  Out P A C -> OS P A B D -> CongA B A P D C P ->
  Par A B C D.
Proof.
    intros.
    induction(eq_dec_points A C).
      subst C.
      unfold Par.
      right.
      repeat split.
        unfold CongA in H1.
        spliter.
        auto.
        unfold CongA in H1.
        spliter.
        auto.
        Col.
      apply conga_comm in H1.
      apply conga_cop__or_out_ts in H1; Cop.
      induction H1.
        apply out_col in H1.
        Col.
      apply l9_9 in H1.
      contradiction.
    unfold Out in H.
    spliter.
    induction H4.
      eapply l12_22_aux.
        3:apply H4.
        auto.
        assumption.
        assumption.
      assumption.
    apply par_symmetry.
    eapply l12_22_aux.
      3:apply H4.
      auto.
      auto.
      eapply (col_one_side _ A).
        apply bet_col in H4.
        Col.
        auto.
      apply one_side_symmetry.
      assumption.
    apply conga_sym.
    assumption.
Qed.

Lemma par_strict_par : forall A B C D,
 Par_strict A B C D -> Par A B C D.
Proof.
    intros.
    unfold Par.
    tauto.
Qed.


Lemma par_strict_distinct : forall A B C D,
 Par_strict A B C D ->
  A<>B /\ A<>C /\ A<>D /\ B<>C /\ B<>D /\ C<>D.
Proof.
    unfold Par_strict.
    intros; spliter.
    repeat split; auto;
    intro; apply H2; [exists A..|exists B|exists B]; subst; split; Col.
Qed.

Lemma col_par : forall A B C,
 A <> B -> B <> C ->
 Col A B C -> Par A B B C.
Proof.
    intros.
    unfold Par.
    right.
    intuition Col.
Qed.

Lemma acute_col_perp__out : forall A B C A',
  Acute A B C -> Col B C A' -> Perp B C A A' -> Out B A' C.
Proof.
  intros A B C A' HacuteB HBCA' HPerp.
  assert(HUn := perp_not_col2 B C A A' HPerp).
  destruct HUn as [HNCol1|]; [|contradiction].
  assert(HB' := l10_15 B C B A).
  destruct HB' as [B' []]; Col.
  assert_diffs.
  assert(HNCol2 : ~ Col B' B C ) by (apply per_not_col; Perp).
  assert(HNCol3 : ~ Col B B' A).
  { intro.
    apply (nlta A B C).
    apply acute_per__lta; auto.
    apply (l8_3 B'); Col; Perp.
  }
  assert(HPars : Par_strict B B' A A').
    apply (par_not_col_strict _ _ _ _ A); Col; apply (l12_9 _ _ _ _ B C); Perp; Cop.
  assert(HNCol4 := par_strict_not_col_4 B B' A A' HPars).
  apply (col_one_side_out _ B'); Col.
  apply (one_side_transitivity _ _ _ A).
    apply l12_6; Par.
  apply invert_one_side.
  apply in_angle_one_side; Col.
  apply l11_24.
  apply lea_in_angle; Side.
  apply lta_comm.
  apply acute_per__lta; Perp.
Qed.

Lemma acute_col_perp__out_1 : forall A B C A',
  Acute A B C -> Col B C A' -> Perp B A A A' -> Out B A' C.
Proof.
  intros A B C A' HAcute HCol HPerp.
  destruct (segment_construction A B A B) as [A0 [HA1 HA2]].
  destruct (segment_construction C B C B) as [C0 [HC1 HC2]].
  assert_diffs.
  assert (HNCol : ~ Col B A A') by (apply per_not_col; Perp).
  assert_diffs.
  apply l6_2 with C0; auto.
  apply not_out_bet.
    ColR.
  intro.
  apply (not_bet_and_out A B A0); split; trivial.
  apply acute_col_perp__out with A'; Col.
    apply acute_sym, (acute_conga__acute A B C); auto.
    apply l11_14; auto.
    apply between_symmetry, l6_2 with C0; Between.
    apply l6_6; assumption.
  apply perp_col with A; Col; Perp.
Qed.

Lemma conga_cop_inangle_per2__inangle : forall A B C P T,
  Per A B C -> InAngle T A B C -> CongA P B A P B C -> Per B P T -> Coplanar A B C P ->
  InAngle P A B C.
Proof.
  intros A B C P T HPer HInangle HConga HPerP HCop.
  destruct (eq_dec_points P T).
    subst; apply HInangle.
  assert_diffs.
  destruct (angle_bisector A B C) as [P' [HInangle' HConga']]; auto.
  assert_diffs.
  assert (HAcute : Acute P' B A).
    apply acute_sym, conga_inangle_per__acute with C; trivial.
  apply l11_25 with P' A C; try (apply out_trivial); auto.
  assert (HNCol1 : ~ Col A B C) by (apply per_not_col; auto).
  assert (HCol : Col B P P').
    apply conga2_cop2__col with A C; trivial.
    intro; apply HNCol1; Col.
    apply coplanar_trans_1 with C; Cop; Col.
    apply coplanar_trans_1 with A; Cop.
  apply (acute_col_perp__out T); Col.
  { apply acute_lea_acute with P' B A; trivial.
    assert (HNCol2 : ~ Col P' B A).
      intro.
      assert (Col P' B C) by (apply (col_conga_col P' B A); assumption).
      apply HNCol1; ColR.
    assert (Coplanar A B T P') by (apply coplanar_trans_1 with C; Cop; Col).
    destruct (col_dec T B P'); [|assert_diffs; destruct (cop__one_or_two_sides B P' A T); Col; Cop].
    - apply l11_31_1; auto.
      apply col_one_side_out with A; Col.
      apply invert_one_side, inangle_one_side with C; Col.
      assert (~ Col B P T) by (apply per_not_col; auto).
      intro; assert_diffs; apply HNCol2; ColR.
    - apply (l11_30 P' B T P' B C); CongA.
      exists T; split; CongA.
      apply l11_24 in HInangle; apply l11_24 in HInangle'.
      destruct (col_dec B C T).
        apply out341__inangle; auto.
        apply col_in_angle_out with A; Col.
        intro; apply HNCol1; Col.
      assert (HNCol3 : ~ Col P' B C) by (apply (ncol_conga_ncol P' B A); assumption).
      apply os2__inangle.
        exists A; split; Side.
        apply invert_two_sides, in_angle_two_sides; Col.
      apply invert_one_side, inangle_one_side with A; Col.
    - exists T; split; CongA.
      destruct (col_dec B A T).
        apply out341__inangle; auto.
        apply col_in_angle_out with C; Col.
        intro; apply HNCol1; Col.
      apply os2__inangle; trivial.
      apply invert_one_side, inangle_one_side with C; Col.
  }
  apply perp_col with P; Col.
  apply perp_right_comm, per_perp; auto.
Qed.

End T12_2'.

Hint Resolve col_par par_strict_par : par.

Hint Resolve l12_6 pars__os3412 : side.

(*
Ltac finish := repeat match goal with
 | |- Bet ?A ?B ?C => Between
 | |- Col ?A ?B ?C => Col
 | |- ~ Col ?A ?B ?C => Col
 | |- Par ?A ?B ?C ?D => Par
 | |- Par_strict ?A ?B ?C ?D => Par
 | |- Perp ?A ?B ?C ?D => Perp
 | |- Perp_at ?A ?B ?C ?D ?E => Perp
 | |- Per ?A ?B ?C => Perp
 | |- Cong ?A ?B ?C ?D => Cong
 | |- Midpoint ?A ?B ?C => Midpoint
 | |- ?A<>?B => apply swap_diff;assumption
 | |- _ => try assumption
end.
*)

Section T12_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_not_par : forall A B X Y, Perp A B X Y -> ~ Par A B X Y.
Proof.
    intros.
    assert(HH:=H).
    unfold Perp in HH.
    ex_and HH P.
    intro.
    induction H1.
      apply H1.
      exists P.
      apply perp_in_col in H0.
      spliter.
      split; Col.
    spliter.
    induction(eq_dec_points A Y).
      subst Y.
      assert(P = A).
        eapply (l8_14_2_1b P A B X A); Col.
      subst P.
      apply perp_in_comm in H0.
      apply perp_in_per in H0.
      assert(~ Col B A X).
        eapply(per_not_col).
          auto.
          auto.
        assumption.
      apply H5.
      Col.
    apply(l8_16_1 A B X A Y); Col.
      ColR.
    ColR.
Qed.

Lemma cong_conga_perp : forall A B C P, TS B P A C -> Cong A B C B -> CongA A B P C B P -> Perp A C B P.
Proof.
    intros.
    assert(HH:=H).
    unfold TS in HH.
    assert (~ Col A B P).
      spliter.
      assumption.
    spliter.
    ex_and H5 T.
    assert(B <> P).
      intro.
      subst P.
      apply H3.
      Col.
    assert(A <> B).
      intro.
      subst B.
      apply H3.
      Col.
    assert(C <> B).
      intro.
      subst C.
      apply H4.
      Col.
    assert(A <> C).
      intro.
      subst C.
      assert(OS B P A A).
        apply one_side_reflexivity.
        assumption.
      apply l9_9 in H.
      contradiction.
    induction (bet_dec A B C).
      assert(Per P B A).
        apply(l11_18_2 P B A C); auto.
        apply conga_comm.
        assumption.
      eapply (col_per_perp _ _ _ C) in H12; auto.
        apply perp_right_comm.
        assumption.
      apply bet_col in H11.
      Col.
    assert(B <> T).
      intro.
      subst T.
      contradiction.
    assert(CongA T B A T B C).
      induction H5.
        eapply (l11_13 P _ _ P); Between.
        apply conga_comm.
        apply H1.
      assert(Out B P T).
        repeat split; auto.
        induction H5.
          left.
          Between.
        right.
        Between.
      apply conga_comm.
      eapply (out_conga A _ P C _ P); auto.
        apply out_trivial.
        auto.
      apply out_trivial.
      auto.
    assert(Cong T A T C).
      apply (cong2_conga_cong T B A T B C); Cong.
    assert(Midpoint T A C).
      split; Cong.
    assert(Per B T A).
      unfold Per.
      exists C.
      split; Cong.
    eapply (col_per_perp _ _ _ C) in H16; auto.
      apply perp_sym.
      apply (perp_col _ T); Col.
      Perp.
      intro.
      subst T.
      apply is_midpoint_id in H15.
      contradiction.
      intro.
      subst T.
      apply l7_2 in H15.
      apply is_midpoint_id in H15.
      apply H10.
      auto.
    apply bet_col in H6.
    Col.
Qed.

Lemma perp_inter_exists : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P.
Proof.
    intros A B C D HPerp.
    destruct HPerp as [P [_ [_ [HCol1 [HCol2]]]]].
    exists P; split; Col.
Qed.

Lemma perp_inter_perp_in : forall A B C D, Perp A B C D -> exists P, Col A B P /\ Col C D P /\ Perp_at P A B C D.
Proof.
    intros.
    assert(HH:=perp_inter_exists A B C D H).
    ex_and HH P.
    exists P.
    split.
      Col.
    split.
      Col.
    apply l8_14_2_1b_bis; Col.
Qed.

End T12_3.

Section T12_2D.

Context `{T2D:Tarski_2D}.

Lemma col_perp2__col : forall X1 X2 Y1 Y2 A B,
  Perp X1 X2 A B -> Perp Y1 Y2 A B -> Col X1 Y1 Y2 -> Col X2 Y1 Y2.
Proof.
  intros.
  apply col_cop2_perp2__col with X1 A B; trivial; apply all_coplanar.
Qed.

Lemma l12_9_2D : forall A1 A2 B1 B2 C1 C2,
  Perp A1 A2 C1 C2 -> Perp B1 B2 C1 C2 -> Par A1 A2 B1 B2.
Proof.
  intros A1 A2 B1 B2 C1 C2.
  apply l12_9; apply all_coplanar.
Qed.

Lemma conga_inangle_per2__inangle : forall A B C P T,
  Per A B C -> InAngle T A B C -> CongA P B A P B C -> Per B P T ->
  InAngle P A B C.
Proof.
  intros.
  assert (HCop := all_coplanar A B C P).
  apply conga_cop_inangle_per2__inangle with T; assumption.
Qed.

End T12_2D.