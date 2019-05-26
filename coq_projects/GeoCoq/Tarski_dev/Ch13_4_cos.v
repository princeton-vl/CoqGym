(* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_3_angles.

Ltac anga_instance_o a A B P C :=
        assert(tempo_anga:= anga_const_o a A B P);
        match goal with
           |H: Q_CongA_Acute a |-  _ => assert(tempo_H:= H); apply tempo_anga in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_anga.

Section Cosinus.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(************************************* cos *****************************)

Lemma l13_6 : forall a lc ld l, Lcos lc l a -> Lcos ld l a -> EqL lc ld.
Proof.
    intros.
    unfold Lcos in *.
    spliter.
    ex_and H6 X1.
    ex_and H7 Y1.
    ex_and H6 Z1.
    ex_and H3 X2.
    ex_and H10 Y2.
    ex_and H3 Z2.
    clean_duplicated_hyps.
    assert(Len X1 Z1 l).
      split; auto.
    assert(Len X2 Z2 l).
      split; auto.
    assert(Cong X1 Z1 X2 Z2).
      eapply (is_len_cong _ _ _ _ l); auto.
    assert(Ang_Acute Y1 X1 Z1 a).
      split; auto.
    assert(Ang_Acute Y2 X2 Z2 a).
      split; auto.
    assert(CongA Y1 X1 Z1 Y2 X2 Z2).
      apply (is_anga_conga _ _ _ _ _ _ a); split; auto.
    assert(Len X1 Y1 lc).
      split; auto.
    assert(Len X2 Y2 ld).
      split; auto.
    induction(eq_dec_points Z1 Y1).
      subst Z1.
      assert(Out X2 Y2 Z2).
        apply (eq_conga_out Y1 X1); auto.
      assert(Y2 = Z2).
        assert(Z2 = Y2 \/ X2 = Y2).
          apply l8_9.
            auto.
          apply out_col in H19.
          Col.
        induction H20.
          auto.
        unfold Out in H19.
        spliter.
        subst Y2.
        tauto.
      subst Z2.
      assert(EqL l lc).
        apply ex_eql.
        exists X1.
        exists Y1.
        split; auto.
      assert(EqL l ld).
        apply ex_eql.
        exists X2.
        exists Y2.
        split; auto.
     transitivity l;auto.
     symmetry; auto.
    assert(Z2 <> Y2).
      intro.
      subst Z2.
      assert(Out X1 Y1 Z1).
        apply (eq_conga_out Y2 X2).
        apply conga_sym.
        auto.
      assert(Y1 = Z1).
        assert(Z1 = Y1 \/ X1 = Y1).
          apply l8_9.
            auto.
          apply out_col in H20.
          Col.
        induction H21.
          auto.
        subst Y1.
        unfold Out in H20.
        spliter.
        tauto.
      subst Z1.
      tauto.
    apply conga_distinct in H16.
    spliter.
    assert(CongA X1 Y1 Z1 X2 Y2 Z2).
      apply l11_16; Perp; auto.
    assert(~Col Z1 X1 Y1).
      intro.
      assert(X1 = Y1 \/ Z1 = Y1).
        apply l8_9.
          Perp.
        Col.
      induction H27.
        subst Y1.
        tauto.
      contradiction.
    apply conga_comm in H16.
    apply cong_commutativity in H13.
    assert(HH:=l11_50_2 Z1 X1 Y1 Z2 X2 Y2 H26 H25 H16 H13).
    spliter.
    apply ex_eql.
    exists X1.
    exists Y1.
    split.
      auto.
    eapply is_len_cong_is_len.
      apply H18.
    Cong.
Qed.

Lemma null_lcos_eql : forall lp l a, Lcos lp l a -> Q_CongA_Null_Acute a -> EqL l lp.
Proof.
    intros.
    unfold Lcos in H.
    spliter.
    ex_and H3 A.
    ex_and H4 B.
    ex_and H3 C.
    unfold Q_CongA_Null_Acute in H0.
    spliter.
    assert(HH:= H7 B A C H6).
    assert(Col A B C) by (apply out_col;auto).
    assert(Col C B A) by Col.
    assert(HQ:= l8_9 C B A H3 H9).
    induction HQ.
      subst C.
      apply (all_eql A B).
        split; auto.
      split; auto.
    subst B.
    exfalso.
    unfold Out in HH.
    tauto.
Qed.

Lemma eql_lcos_null : forall l lp a, Lcos l lp a -> EqL l lp -> Q_CongA_Null_Acute a.
Proof.
    intros.
    unfold Lcos in H.
    spliter.
    ex_and H3 B.
    ex_and H4 A.
    ex_and H3 C.
    assert(forall A0 B0 : Tpoint, l A0 B0 <-> lp A0 B0).
      apply H0; auto.
    assert(HP:= (H7 B A)).
    assert(HQ:= (H7 B C)).
    destruct HP.
    destruct HQ.
    assert(l B C).
      apply H11.
      auto.
    assert(lp B A).
      apply H8.
      auto.
    clear H7 H8 H9 H10 H11.
    assert(Cong B A B C).
      apply (lg_cong l); auto.
    unfold Per in H3.
    ex_and H3 B'.
    assert(HH:= anga_distinct a A B C H2 H6).
    spliter.
    assert(A = C).
      eapply (l4_18 B B').
        intro.
        subst B'.
        apply l7_3 in H3.
        contradiction.
        unfold Midpoint in H3; assert(HH:= midpoint_col).
        spliter.
        apply bet_col in H3.
        Col.
        auto.
      unfold Midpoint in H3.
      spliter.
      eapply cong_transitivity.
        apply cong_symmetry.
        apply cong_commutativity.
        apply H11.
      eapply cong_transitivity.
        apply cong_commutativity.
        apply H7.
      Cong.
    subst C.
    unfold Q_CongA_Null_Acute.
    split.
      auto.
    intros A0 B0 C0 HP.
    apply (eq_conga_out A B).
    apply (anga_conga a); auto.
Qed.

Lemma lcos_lg_not_null: forall l lp a, Lcos l lp a -> ~ Q_Cong_Null l /\ ~ Q_Cong_Null lp.
Proof.
    intros.
    unfold Lcos in H.
    spliter.
    ex_and H2 A.
    ex_and H3 B.
    ex_and H2 C.
    assert(HH:= anga_distinct a B A C H1 H5).
    spliter.
    unfold Q_Cong_Null.
    split; intro; spliter; ex_and H9 X.
      assert (Cong A B X X) by (apply (lg_cong l); auto).
      treat_equalities;intuition.
    assert(Cong A C X X) by (apply (lg_cong lp); auto).
    treat_equalities;intuition.
Qed.

Lemma perp_acute_out : forall A B C C', Acute A B C -> Perp A B C C' -> Col A B C' -> Out B A C'.
Proof.
    intros.
    apply l6_6.
    apply acute_col_perp__out with C.
      apply acute_sym.
      assumption.
      Col.
      Perp.
Qed.

End Cosinus.

Require Import Morphisms.

Section Cosinus2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma perp_out__acute : forall A B C C', Perp A B C C' -> Col A B C' -> (Acute A B C <-> Out B A C').
Proof.
    intros.
    split.
      intro.
      apply (perp_acute_out _ _ C); auto.
    intro.
    apply (perp_out_acute _ _ C C'); auto.
Qed.

Lemma obtuse_not_acute : forall A B C, Obtuse A B C -> ~ Acute A B C.
Proof.
    intros.
    intro.
    unfold Obtuse in H.
    unfold Acute in H0.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    ex_and H0 A1.
    ex_and H2 B1.
    ex_and H0 C1.
    assert(A0 <> B0 /\ C0 <> B0 /\ A1 <> B1 /\ C1 <> B1 /\ A <> B /\ C <> B).
      unfold GtA in H1.
      unfold LtA in *.
      unfold LeA in *.
      spliter.
      ex_and H1 P0.
      ex_and H2 P.
      unfold InAngle in H2.
      unfold CongA in H5 .
      unfold CongA in H6 .
      spliter.
      repeat split; auto.
    spliter.
    assert(CongA A0 B0 C0 A1 B1 C1).
      apply l11_16; auto.
    assert(GtA A B C A1 B1 C1).
      apply (conga_preserves_gta A B C A0 B0 C0).
        apply conga_refl; auto.
        auto.
      assumption.
    assert(HH:=not_lta_and_gta A B C A1 B1 C1).
    apply HH.
    split; auto.
Qed.

Lemma acute_not_obtuse : forall A B C, Acute A B C -> ~ Obtuse A B C.
Proof.
    intros.
    intro.
    apply obtuse_not_acute in H0.
    contradiction.
Qed.

Lemma perp_obtuse_bet : forall A B C C', Perp A B C C' -> Col A B C' -> Obtuse A B C -> Bet A B C'.
Proof.
    intros.
    assert(HH:= H1).
    unfold Obtuse in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    assert(A0 <> B0 /\ C0 <> B0 /\ A <> B /\ C <> B).
      unfold GtA in H3.
      unfold LtA in H3.
      spliter.
      unfold LeA in H3.
      ex_and H3 P.
      unfold CongA in H5.
      spliter.
      repeat split; auto.
      intro.
      subst C.
      apply perp_comm in H.
      apply perp_not_col in H.
      apply H.
      Col.
    spliter.
    assert(B <> C').
      intro.
      subst C'.
      assert(Per A B C).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        Perp.
      assert(CongA A0 B0 C0 A B C).
        apply l11_16; auto.
      unfold GtA in H3.
      unfold LtA in H3.
      spliter.
      unfold LeA in H3.
      contradiction.
    induction H0.
      auto.
    assert(Out B A C').
      unfold Out.
      repeat split; auto.
      induction H0.
        right.
        auto.
      left.
      Between.
    eapply (perp_out_acute _ _ C) in H9.
      apply obtuse_not_acute in H1.
      contradiction.
      auto.
Qed.

Lemma lcos_const0 : forall l lp a, Lcos lp l a -> Q_CongA_Null_Acute a ->
 exists A, exists B, exists C, l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    ex_and H4 A.
    ex_and H5 B.
    ex_and H4 C.
    exists C.
    exists A.
    exists B.
    repeat split.
      apply lg_sym; auto.
      auto.
    apply anga_sym; auto.
Qed.

Lemma lcos_const1 : forall l lp a P, Lcos lp l a -> ~ Q_CongA_Null_Acute a ->
 exists A, exists B, exists C, ~Col A B P /\ OS A B C P /\ l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    assert(HH:= (lcos_lg_not_null lp l a H)).
    spliter.
    lg_instance_not_col l P A B.
    exists A.
    exists B.
    assert(HH:=anga_const_o a A B P H8 H0 H3).
    ex_and HH C'.
    assert(A <> B /\ B <> C').
      assert(HP:= anga_distinct a A B C' H3 H9).
      spliter.
      auto.
    spliter.
    assert(HH:=ex_point_lg_out lp B C' H12 H1 H5).
    ex_and HH C.
    exists C.
    repeat split; auto.
      assert(~ Col A B C').
        unfold OS in H10.
        ex_and H10 D.
        unfold TS in H10.
        spliter.
        intro.
        apply H10.
        Col.
      assert(HP:=out_one_side_1 A B C' C B H15).
      eapply (one_side_transitivity _ _ _ C').
        apply one_side_symmetry.
        apply HP.
          Col.
        apply l6_6.
        auto.
      auto.
    apply (anga_out_anga a A B C'); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.

Lemma lcos_const : forall lp l a, Lcos lp l a ->
 exists A, exists B, exists C, lp A B /\ l B C /\ a A B C.
Proof.
    intros.
    unfold Lcos in H.
    spliter.
    ex_and H2 A.
    ex_and H3 B.
    ex_and H2 C.
    exists B.
    exists A.
    exists C.
    repeat split; auto.
    apply lg_sym; auto.
Qed.

Lemma lcos_lg_distincts : forall lp l a A B C, Lcos lp l a -> l A B -> lp B C -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    unfold Q_Cong_Null in *.
    split.
      intro.
      subst B.
      apply H4.
      unfold Lcos in H.
      split.
        tauto.
      exists A.
      auto.
    intro.
    subst C.
    apply H3.
    unfold Lcos in H.
    split.
      tauto.
    exists B.
    auto.
Qed.


Lemma lcos_const_a : forall lp l a B, Lcos lp l a -> exists A, exists C, l A B /\ lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    clear H3.
    assert(HH:= ex_point_lg l B H1).
    ex_and HH A.
    assert(l A B).
      apply lg_sym; auto.
    exists A.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(A <> B).
      intro.
      subst A.
      apply H6.
      unfold Q_Cong_Null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a A B H2 H7).
    ex_and HH C'.
    assert(HH:= anga_distincts a A B C' H2 H8).
    spliter.
    assert(B <> C'); auto.
    assert(HH:= ex_point_lg_out lp B C' H11 H0 H5).
    ex_and HH C.
    exists C.
    repeat split; auto.
    apply (anga_out_anga a A B C' A C); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.


Lemma lcos_const_ab : forall lp l a B A, Lcos lp l a -> l A B -> exists C, lp B C /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    clear H4.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(A <> B).
      intro.
      subst A.
      apply H5.
      unfold Q_Cong_Null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a A B H3 H6).
    ex_and HH C'.
    assert(HH:= anga_distincts a A B C' H3 H7).
    spliter.
    assert(B <> C'); auto.
    assert(HH:= ex_point_lg_out lp B C' H10 H1 H4).
    ex_and HH C.
    exists C.
    repeat split; auto.
    apply (anga_out_anga a A B C' A C); auto.
      apply out_trivial.
      auto.
    apply l6_6.
    auto.
Qed.

Lemma lcos_const_cb : forall lp l a B C, Lcos lp l a -> lp B C -> exists A, l A B /\ a A B C.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    clear H4.
    assert(HH:= lcos_lg_not_null lp l a H).
    spliter.
    assert(C <> B).
      intro.
      subst C.
      apply H4.
      unfold Q_Cong_Null.
      split.
        auto.
      exists B.
      auto.
    assert(HH:= anga_const a C B H3 H6).
    ex_and HH A'.
    assert(HH:= anga_distincts a C B A' H3 H7).
    spliter.
    assert(B <> A'); auto.
    assert(HH:= ex_point_lg_out l B A' H10 H2 H5).
    ex_and HH A.
    exists A.
    split.
      apply lg_sym; auto.
    apply(anga_out_anga a A' B C); auto.
      apply anga_sym; auto.
      apply l6_6.
      auto.
    apply out_trivial.
    auto.
Qed.

Lemma lcos_lg_anga : forall l lp a, Lcos lp l a -> Lcos lp l a /\ Q_Cong l /\ Q_Cong lp /\ Q_CongA_Acute a.
Proof.
    intros.
    split.
      auto.
    unfold Lcos in H.
    tauto.
Qed.

Lemma lcos_eql_lcos : forall lp1 l1 lp2 l2 a, EqL lp1 lp2 -> EqL l1 l2 -> Lcos lp1 l1 a -> Lcos lp2 l2 a.
Proof.
    intros.
    unfold Lcos in *.
    spliter.
    ex_and H4 A.
    ex_and H5 B.
    ex_and H4 C.

    assert(HH:=lg_eql_lg l1 l2 H2 H0).
    assert(HP:=lg_eql_lg lp1 lp2 H1 H).
    repeat split; auto.
    exists A.
    exists B.
    exists C.
    unfold EqL in *.
    spliter.
    repeat split; auto.
      apply H.
      auto.
    apply H0; auto.
Qed.

Global Instance lcos_morphism :
 Proper (EqL ==> EqL ==> eq ==> iff) Lcos.
Proof.
unfold Proper.
split.
 - rewrite H1.
   intro.
   eauto using lcos_eql_lcos.
 - intro.
   rewrite H1.
   eapply lcos_eql_lcos with y y0;
   try symmetry;assumption.
Qed.


Lemma lcos_not_lg_null : forall lp l a, Lcos lp l a -> ~ Q_Cong_Null lp.
Proof.
    intros.
    intro.
    unfold Q_Cong_Null in H0.
    spliter.
    unfold Lcos in H.
    spliter.
    ex_and H4 B.
    ex_and H5 A.
    ex_and H4 C.
    ex_and H1 P.
    unfold Q_Cong in H0.
    ex_and H0 X.
    ex_and H1 Y.
    assert(HH:= (H0 B A)).
    destruct HH.
    assert(HH:= (H0 P P)).
    destruct HH.
    apply H11 in H8.
    apply H9 in H5.
    assert(Cong B A P P).
      apply (cong_transitivity _ _ X Y); Cong.
    assert(A = B).
      eapply (cong_identity _ _ P).
      Cong.
    assert(HH:=anga_distincts a A B C H3 H7).
    spliter.
    contradiction.
Qed.

Lemma lcos_const_o : forall lp l a A B P, ~ Col A B P -> ~ Q_CongA_Null_Acute a -> Q_Cong l -> Q_Cong lp ->
  Q_CongA_Acute a -> l A B -> Lcos lp l a ->
  exists C, OS A B C P /\ a A B C /\ lp B C.
Proof.
    intros.
    assert(HH:= anga_const_o a A B P H H0 H3).
    ex_and HH C'.
    assert(A <> B /\ C' <> B).
      apply (anga_distincts a); auto.
    spliter.
    assert(HH:= lcos_not_lg_null lp l a H5).
    assert (B <> C').
      intro.
      apply H9.
      auto.
    assert(HP:=lg_exists C' B).
    ex_and HP lc'.
    assert(HQ:=anga_not_lg_null a l lc' A B C' H1 H11 H3 H4 H12 H6).
    spliter.
    assert(HR:= ex_point_lg_out lp B C' H10 H2 HH).
    ex_and HR C.
    exists C.
    split.
      apply invert_one_side.
      apply one_side_symmetry.
      apply (out_out_one_side _ _ _ C').
        apply invert_one_side.
        apply one_side_symmetry.
        auto.
      apply l6_6.
      auto.
    split.
      eapply (anga_out_anga a A B C'); auto.
        apply out_trivial.
        auto.
      apply l6_6.
      auto.
    auto.
Qed.

Lemma flat_not_acute : forall A B C, Bet A B C -> ~ Acute A B C.
Proof.
    intros.
    intro.
    unfold Acute in H0.
    ex_and H0 A'.
    ex_and H1 B'.
    ex_and H0 C'.
    unfold LtA in H1.
    spliter.
    unfold LeA in H1.
    ex_and H1 P'.
    unfold InAngle in H1.
    spliter.
    ex_and H6 X.
    apply conga_distinct in H3.
    spliter.
    assert(A <> C).
      intro.
      subst C.
      apply between_identity in H.
      contradiction.
    induction H7.
      subst X.
      apply H2.
      apply conga_line; auto.
    assert(CongA A B C A' B' X).
      apply (out_conga A B C A' B' P').
        auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      apply l6_6.
      auto.
    apply H2.
    assert(Bet A' B' X).
      apply (bet_conga__bet A B C); auto.
    apply conga_line; auto.
    apply (between_exchange4 _ _ X); auto.
Qed.

Lemma acute_comp_not_acute : forall A B C D, Bet A B C -> Acute A B D -> ~ Acute C B D.
Proof.
    intros.
    intro.
    induction(col_dec A C D).
      induction H2.
        assert(Bet A B D).
          eBetween.
        assert(HH:= flat_not_acute A B D H3).
        contradiction.
      induction H2.
        assert(Bet A B D \/ Bet A D B).
          apply (l5_3 A B D C).
            auto.
          Between.
        induction H3.
          assert(HH:= flat_not_acute A B D H3).
          contradiction.
        assert(Bet C B D).
          eBetween.
        assert(HH:= flat_not_acute C B D H4).
        contradiction.
      assert(Bet C B D).
        eBetween.
      assert(HH:= flat_not_acute C B D H3).
      contradiction.
    unfold Acute in *.
    ex_and H0 A0.
    ex_and H3 B0.
    ex_and H0 C0.
    ex_and H1 A1.
    ex_and H4 B1.
    ex_and H1 C1.
    assert (Hd := H3).
    assert (Hd' := H4).
    apply lta_distincts in Hd.
    apply lta_distincts in Hd'.
    spliter.
    assert(HH:=l11_16 A0 B0 C0 A1 B1 C1 H0 H12 H13 H1 H7 H8).
    assert(LtA C B D A0 B0 C0).
      eapply(conga_preserves_lta C B D A1 B1 C1).
        apply conga_refl; auto.
        apply conga_sym.
        auto.
      auto.
    clear H4.
    assert(A <> C).
      intro.
      subst C.
      apply between_identity in H.
      contradiction.
    assert(Col A C B).
      apply bet_col in H.
      Col.
    assert(HP:= l10_15 A C B D H16 H2).
    ex_and HP P.
    assert(HP:= perp_col A C P B B H10 H17 H16).
    apply perp_left_comm in HP.
    apply perp_perp_in in HP.
    assert(Per A B P).
      apply perp_in_per.
      apply perp_in_comm.
      auto.
    assert(HR:= perp_not_eq_2 A C P B H17).
    assert(HQ:=l11_16 A B P A0 B0 C0 H19 H10 HR H0 H12 H13).
    assert(LtA A B D A B P).
      apply (conga_preserves_lta A B D A0 B0 C0); auto.
        apply conga_refl; auto.
      apply conga_sym.
      auto.
    assert(LtA C B D A B P).
      apply (conga_preserves_lta C B D A0 B0 C0); auto.
        apply conga_refl; auto.
      apply conga_sym.
      auto.
    clear HQ H15 HH H3 H0 H1.
    unfold LtA in *.
    spliter.
    assert((LeA A B D A B P <-> LeA C B P C B D)).
      apply (l11_36 A B D A B P C C); auto.
    destruct H20.
    assert(LeA C B P C B D).
      apply H20.
      auto.
    assert(CongA A B P C B P).
      apply l11_16; auto.
      apply perp_in_per.
      assert(Perp C B P B).
        apply(perp_col _ A).
          auto.
          apply perp_left_comm.
          auto.
        apply bet_col in H.
        Col.
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_left_comm.
      auto.
    assert(LeA A B P C B D).
      apply (l11_30 C B P C B D); auto.
        apply conga_sym.
        auto.
      apply conga_refl; auto.
    assert(HH:=lea_asym C B D A B P H0 H24).
    contradiction.
Qed.

Lemma lcos_per : forall A B C lp l a, Q_CongA_Acute a -> Q_Cong l -> Q_Cong lp ->
  Lcos lp l a -> l A C -> lp A B -> a B A C -> Per A B C.
Proof.
    intros.
    induction(eq_dec_points B C).
      subst C.
      apply l8_5.
    unfold Lcos in H2.
    spliter.
    ex_and H9 A0.
    ex_and H10 B0.
    ex_and H9 C0.
    assert(CongA B0 A0 C0 B A C).
      apply (anga_conga a); auto.
    assert(Cong A0 C0 A C).
      apply (lg_cong l); auto.
    assert(Cong A0 B0 A B).
      apply (lg_cong lp); auto.
    assert(HH:=l11_49 B0 A0 C0 B A C H13 H15 H14).
    spliter.
    assert(B0 <> C0).
      intro.
      subst C0.
      apply H6.
      apply (cong_identity _ _ B0).
      Cong.
    apply H17 in H18.
    spliter.
    eapply (l11_17 A0 B0 C0).
      apply l8_2.
      auto.
    auto.
Qed.

Lemma is_null_anga_dec : forall a, Q_CongA_Acute a -> Q_CongA_Null_Acute a \/ ~ Q_CongA_Null_Acute a.
Proof.
    intros a H.
    assert (H' := H).
    unfold Q_CongA_Acute in H.
    destruct H as [A [B [C [Hacute HConga]]]].
    elim (out_dec B A C); intro Hout.
      left.
      unfold Q_CongA_Null_Acute.
      split; auto.
      intros.
      apply (l11_21_a A B C); auto.
      apply HConga.
      assumption.
    right.
    unfold Q_CongA_Null_Acute.
    intro H.
    destruct H as [Hclear H]; clear Hclear.
    apply Hout.
    apply H.
    apply HConga.
    apply acute_distincts in Hacute.
    spliter.
    apply conga_refl; auto.
Qed.

Lemma lcos_lg : forall a lp l A B C, Lcos lp l a -> Perp A B B C -> a B A C -> l A C -> lp A B.
Proof.
    intros.
    assert(HH:=H).
    unfold Lcos in HH.
    spliter.
    ex_and H6 A'.
    ex_and H7 B'.
    ex_and H6 C'.
    assert(Cong A C A' C').
      apply (lg_cong l); auto.
    assert(CongA B A C B' A' C').
      apply (anga_conga a); auto.
    induction(is_null_anga_dec a).
      assert(HP := null_lcos_eql lp l a H H12).
      unfold Q_CongA_Null_Acute in H12.
      spliter.
      assert(HH:= (H13 B A C H1)).
      apply perp_comm in H0.
      apply perp_not_col in H0.
      apply False_ind.
      apply H0.
      apply out_col in HH.
      Col.
      apply conga_distinct in H11.
      spliter.
      assert(CongA A B C A' B' C').
        apply l11_16; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_comm.
          auto.
          apply perp_not_eq_2 in H0.
          auto.
          apply l8_2.
          auto.
        intro.
        subst C'.
        apply H12.
        unfold Q_CongA_Null_Acute.
        split; auto.
        intros.
        assert(CongA A0 B0 C0 B' A' B').
          apply (anga_conga a); auto.
        apply (l11_21_a B' A' B') .
          apply out_trivial; auto.
        apply conga_sym.
        auto.
      assert(Cong C B C' B' /\ Cong A B A' B' /\ CongA B C A B' C' A').
        apply(l11_50_2 C A B C' A' B').
          apply perp_comm in H0.
          apply perp_not_col in H0.
          intro.
          apply H0.
          Col.
          auto.
          apply conga_comm.
          auto.
        Cong.
      spliter.
      apply (lg_cong_lg lp A' B');auto.
      Cong.
    assumption.
Qed.

Lemma l13_7 : forall a b l la lb lab lba, Lcos la l a -> Lcos lb l b ->
  Lcos lab la b -> Lcos lba lb a -> EqL lab lba.
Proof.
    intros.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    apply lcos_lg_anga in H2.
    spliter.
    clean_duplicated_hyps.
    induction (is_null_anga_dec a).
      assert(HH:=null_lcos_eql lba lb  a H2 H3).
      assert(HP:=null_lcos_eql la l  a H H3).
      assert(Lcos lab l b) by (rewrite HP;assumption).
      assert(HQ:= l13_6 b lb lab l H0 H5).
      rewrite <- HQ;assumption.
      induction (is_null_anga_dec b).
        assert(HH:=null_lcos_eql lab la  b H1 H5).
        assert(HP:=null_lcos_eql lb l  b H0 H5).
        assert(Lcos lba l a) by (rewrite HP;auto).
        assert(HQ:= l13_6 a la lba l H H6).
        rewrite HH in HQ;assumption.
        assert(HH:=lcos_const la l a H).
        ex_and HH C.
        ex_and H6 A.
        ex_and H8 B.
        assert(HH:= anga_distincts a C A B H14 H9).
        spliter.
        assert(~Col A B C).
          intro.
          apply H3.
          assert(Col C A B).
            Col.
          assert(HH:= anga_col_null a C A B H14 H9 H18).
          spliter.
          auto.
        assert(HH:=l10_2_existence B A C).
        ex_and HH P.
        assert( ~ Col B A P).
          eapply (osym_not_col _ _ C).
            apply l10_4.
            auto.
          intro.
          apply H17.
          Col.
        assert(l B A).
          apply lg_sym; auto.
        assert(HH:= lcos_const_o lb l b B A P H19 H5 H12 H10 H11 H20 H0).
        ex_and HH D.
        assert(TS B A P C).
          apply l10_14.
            intro.
            subst P.
            assert(Col C B A).
              apply(l10_8 B A C); auto.
            apply H19.
            Col.
            auto.
          auto.
        assert(TS B A D C).
          eapply (l9_8_2 _ _ P).
            auto.
          apply one_side_symmetry.
          auto.
        assert(Per A C B).
          apply (lcos_per _ _ _ la l a); auto.
          apply lg_sym; auto.
        assert(Per A D B).
          apply (lcos_per _ _ _ lb l b); auto.
          apply anga_sym; auto.
        assert(~ Col C D A).
          intro.
          assert(Per B C D).
            apply(per_col B C A D); auto.
              apply l8_2.
              auto.
            Col.
          assert(Per B D C).
            apply(per_col B D A C); auto.
              unfold OS in H21.
              ex_and H21 T.
              unfold TS in H21.
              spliter.
              intro.
              subst D.
              apply H21.
              Col.
              apply l8_2.
              auto.
            Col.
          assert(C = D).
            apply (l8_7 B); auto.
          subst D.
          unfold TS in H25.
          spliter.
          ex_and H32 T.
          assert(C=T).
            apply between_identity.
            auto.
          subst T.
          contradiction.
        assert(HH:= l8_18_existence C D A H28).
        ex_and HH E.
        assert(CongA B A C D A E /\ CongA B A D C A E /\ Bet C E D).
          apply(l13_2 A B C D E).
            apply invert_two_sides.
            apply l9_2.
            auto.
            apply l8_2.
            auto.
            apply l8_2.
            auto.
            auto.
          apply perp_sym.
          auto.
        spliter.
        assert(a D A E).
          eapply (anga_conga_anga a B A C); auto.
          apply anga_sym; auto.
        assert(b C A E).
          eapply (anga_conga_anga b B A D); auto.
        assert(Perp C E A E).
          eapply (perp_col _ D) .
            intro.
            subst E.
            apply H5.
            unfold Q_CongA_Null_Acute.
            split; auto.
            intros.
            assert(CongA A0 B0 C0 C A C).
              apply (anga_conga b); auto.
            apply (l11_21_a C A C A0 B0 C0 ).
              apply out_trivial; auto.
            apply conga_sym.
            auto.
            auto.
          auto.
        assert(lab A E).
          apply (lcos_lg b lab la A E C H1).
            apply perp_sym in H36.
            apply perp_right_comm in H36.
            auto.
            apply anga_sym; auto.
          apply lg_sym; auto.
        assert(Perp D E A E).
          eapply (perp_col _ C) .
            intro.
            subst E.
            apply H3.
            unfold Q_CongA_Null_Acute.
            split; auto.
            intros.
            assert(CongA A0 B0 C0 D A D).
              apply (anga_conga a); auto.
            apply (l11_21_a D A D A0 B0 C0 ).
              apply out_trivial; auto.
              apply perp_not_eq_2 in H36.
              auto.
            apply conga_sym.
            auto.
            Perp.
          Col.
        assert(lba A E).
          apply (lcos_lg a lba lb A E D).
            auto.
            Perp.
            auto.
            apply anga_sym; auto.
          auto.
        apply ex_eql.
        exists A.
        exists E.
        split.
          unfold Len.
          split; auto.
        unfold Len.
        split; auto.
      assumption.
    assumption.
Qed.

Lemma out_acute : forall A B C, Out B A C -> Acute A B C.
Proof.
    intros.
    assert( A <> B /\ C <> B).
      unfold Out in H.
      tauto.
    spliter.
    assert(HH:= not_col_exists A B H0).
    ex_and HH Q.
    assert(exists P : Tpoint, Perp A B P B /\ OS A B Q P).
      apply(l10_15 A B B Q).
        Col.
      auto.
    ex_and H3 P.
    assert(Per P B A).
      apply perp_in_per.
      apply perp_left_comm in H3.
      apply perp_in_comm.
      apply perp_perp_in.
      Perp.
    unfold Acute.
    exists A.
    exists B.
    exists P.
    split.
      apply l8_2.
      auto.
    unfold LtA.
    split.
      unfold LeA.
      exists C.
      split.
        apply col_in_angle; auto.
        apply perp_not_eq_2 in H3.
        auto.
      apply conga_refl; auto.
    intro.
    apply l11_21_a in H6.
      apply perp_left_comm in H3.
      apply perp_not_col in H3.
      apply out_col in H6.
      contradiction.
    assumption.
Qed.



Lemma perp_acute : forall A B C P,  Col A C P -> Perp_at P B P A C -> Acute A B P.
Proof.
    intros.
    assert(HH0:=H0).
    assert(HH:= l11_43 P A B).
    induction(col_dec P A B).
      assert(Perp B A A C).
        eapply (perp_col _ P).
          intro.
          subst A.
          assert(Perp_at B B P C B).
            apply perp_perp_in.
            apply perp_in_perp_bis in H0.
            induction H0.
              apply perp_not_eq_1 in H0.
              tauto.
            Perp.
          assert(P=B).
            eapply(l8_14_3 B P B C); Perp.
          subst P.
          apply perp_in_perp_bis in H0.
          induction H0.
            apply perp_not_eq_1 in H0.
            tauto.
          apply perp_not_eq_1 in H0.
          tauto.
          apply perp_in_perp_bis in H0.
          induction H0.
            apply perp_not_eq_1 in H0.
            tauto.
          auto.
        Col.
      apply perp_comm in H2.
      apply perp_perp_in in H2.
      apply perp_in_comm in H2.
      apply perp_in_sym in H2.
      eapply (perp_in_col_perp_in _ _ _ _ P) in H2.
        assert( A = P).
          eapply(l8_14_3 A C B P); Perp.
        subst P.
        apply out_acute.
        apply perp_in_perp_bis in H2.
        induction H2.
          apply out_trivial.
          apply perp_not_eq_2 in H2.
          auto.
        apply perp_not_eq_1 in H2.
        tauto.
        apply perp_in_perp_bis in H0.
        induction H0; apply perp_not_eq_1 in H0; tauto.
      Col.
    apply acute_sym.
    assert_diffs.
    apply l11_43; auto.
    left.
    assert(A <> P).
      intro.
      subst P.
      apply H1.
      Col.
    eapply (perp_in_col_perp_in _ _ _ _ P) in H0; auto.
    apply perp_in_per.
    Perp.
Qed.

Lemma null_lcos : forall l a,Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Null_Acute a -> Lcos l l a.
Proof.
    intros.
    unfold Q_CongA_Null_Acute in H1.
    spliter.
    assert(HH:=ex_points_anga a H1).
    ex_and HH A.
    ex_and H3 B.
    ex_and H4 C.
    assert(HH:=H2 A B C H3).
    unfold Lcos.
    repeat split; auto.
    assert(B <> A).
      unfold Out in HH.
      spliter.
      auto.
    lg_instance l A' B'.
    assert(HP:=ex_point_lg_out l B A H4 H H0).
    ex_and HP P.
    exists B.
    exists P.
    exists P.
    repeat split; auto.
      apply l8_2.
      apply l8_5.
    apply (anga_out_anga _ A _ C); auto.
      apply l6_6.
      auto.
    apply (out2_out_2 _ _ _ A).
      apply l6_6.
      auto.
    auto.
Qed.

Lemma lcos_exists : forall l a, Q_CongA_Acute a -> Q_Cong l -> ~ Q_Cong_Null l -> exists lp, Lcos lp l a.
Proof.
    intros.
    lg_instance l A B.
    induction(is_null_anga_dec a).
      exists l.
      apply null_lcos; auto.
      anga_instance1 a A B C.
        assert(~ Col B C A).
          intro.
          assert(Out B A C /\ Q_CongA_Null_Acute a).
            apply(anga_col_null a A B C H H4).
            Col.
          apply H3.
          tauto.
        assert(HH:= l8_18_existence B C A H5).
        ex_and HH P.
        assert(HH:=lg_exists B P).
        ex_and HH lp.
        exists lp.
        assert(Acute A B C).
          unfold Q_CongA_Acute in H.
          ex_and H A'.
          ex_and H10 B'.
          ex_and H C'.
          assert(HH:=H10 A B C).
          destruct HH.
          assert(HP:= H12 H4).
          apply (acute_lea_acute _ _ _ A' B' C'); auto.
          unfold LeA.
          exists C'.
          split.
            apply inangle3123.
              apply conga_distinct in HP.
              tauto.
            apply conga_distinct in HP.
            tauto.
          apply conga_sym.
          auto.
        unfold Lcos.
        repeat split; auto.
        exists B.
        exists P.
        exists A.
        repeat split; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_sym.
          apply (perp_col _ C).
            intro.
            subst P.
            assert(Per A B C).
              apply perp_in_per.
              apply perp_in_comm.
              apply perp_perp_in.
              Perp.
            apply acute_not_per in H10.
            contradiction.
            Perp.
          Col.
          apply (lg_sym l); auto.
        assert(HH:=H10).
        unfold Acute in HH.
        apply(anga_sym a); auto.
        apply(anga_out_anga a A B C A P); auto.
          apply out_trivial.
          intro.
          subst B.
          apply H5.
          Col.
        eapply (perp_acute_out _ _ A).
          apply acute_sym.
          auto.
          Perp.
        Col.
      intro.
      apply H1.
      unfold Q_Cong_Null.
      split; auto.
      subst B.
      exists A.
      auto.
    assumption.
Qed.


Lemma lcos_uniqueness : forall l a l1 l2, Lcos l1 l a-> Lcos l2 l a -> EqL l1 l2.
Proof.
intros.
unfold Lcos in *.
spliter.
ex_and H6 A1.
ex_and H7 B1.
ex_and H6 C1.
ex_and H3 A2.
ex_and H10 B2.
ex_and H3 C2.

assert(Cong A1 C1 A2 C2).
apply (lg_cong l); auto.

assert(CongA B1 A1 C1 B2 A2 C2).
apply (anga_conga a); auto.

induction(eq_dec_points C1 B1).
subst C1.

assert(EqL l l1).
apply ex_eqL; auto.
exists A1.
exists B1.
split; auto.

assert(Out A2 B2 C2).
apply (l11_21_a B1 A1 B1).
apply out_trivial.
intro.
subst B1.
apply conga_distinct in H14.
tauto.
auto.

assert(C2 = B2 \/ A2 = B2).
apply(l8_9 C2 B2 A2).
auto.
apply out_col in H16.
Col.
induction H17.
subst C2.

assert(EqL l l2).
apply ex_eqL; auto.
exists A2.
exists B2.
split; auto.
transitivity l; auto.
symmetry; auto.

subst B2.
apply conga_distinct in H14.
tauto.

apply conga_distinct in H14.
spliter.
assert(CongA C1 B1 A1 C2 B2 A2).
apply l11_16; auto.
intro.
subst C2.

assert(Out A1 B1 C1).
apply (l11_21_a B2 A2 B2).
apply out_trivial; auto.
apply conga_sym.
auto.
assert(C1 = B1 \/ A1 = B1).
apply(l8_9 C1 B1 A1 ); auto.
apply out_col in H20.
Col.
induction H21.
subst C1.
tauto.
subst B1.
tauto.

assert( Cong C1 B1 C2 B2 /\ Cong A1 B1 A2 B2 /\ CongA B1 C1 A1 B2 C2 A2).
apply(l11_50_2 C1 A1 B1 C2 A2 B2).
intro.
assert(C1 = B1 \/ A1 = B1).
apply(l8_9 C1 B1 A1 ); auto.
Col.
induction H22.
contradiction.
subst B1.
tauto.
apply conga_comm.
auto.
apply conga_comm.
auto.
Cong.
spliter.

apply ex_eqL; auto.
exists A1.
exists B1.
split; auto.
apply (lg_cong_lg l2 A2 B2); auto.
Cong.
Qed.

Lemma lcos_eqa_lcos : forall lp l a b, Lcos lp l a -> EqA a b -> Lcos lp l b.
Proof.
    intros.
    assert(HH:=lcos_lg_anga l lp a H).
    spliter.
    clear H1.
    assert(HH:= H0).
    unfold EqA in HH.
    assert (Q_CongA a) by (apply anga_is_ang;auto).
    assert (Q_CongA b) by (apply eqA_preserves_ang with a;auto).
    assert (Q_CongA_Acute b).
      apply (eqA_preserves_anga a b); auto.
    unfold Lcos in *.
    spliter.
    repeat split; auto.
    ex_and H9 A.
    ex_and H10 B.
    ex_and H9 C.
    exists A.
    exists B.
    exists C.
    repeat split; auto.
    apply HH;auto.
Qed.

Lemma lcos_eq_refl : forall la a, Q_Cong la -> ~ Q_Cong_Null la -> Q_CongA_Acute a -> Eq_Lcos la a la a.
Proof.
    intros.
    unfold Eq_Lcos.
    assert(HH:=lcos_exists la a H1 H H0).
    ex_and HH lp.
    exists lp.
    split; auto.
Qed.

Lemma lcos_eq_sym : forall la a lb b, Eq_Lcos la a lb b -> Eq_Lcos lb b la a.
Proof.
    intros.
    unfold Eq_Lcos in *.
    ex_and H lp.
    exists lp.
    split; auto.
Qed.

Lemma lcos_eq_trans : forall la a lb b lc c, Eq_Lcos la a lb b -> Eq_Lcos lb b lc c -> Eq_Lcos la a lc c.
Proof.
    intros.
    unfold Eq_Lcos in *.
    ex_and H lab.
    ex_and H0 lbc.
    assert(HH:= l13_6 b lab lbc lb H1 H0).
    assert(Lcos lbc la a).
      rewrite <- HH.
      apply lcos_lg_anga in H.
      tauto.
    exists lbc.
    split; auto.
Qed.

Lemma lcos2_comm : forall lp l a b, Lcos2 lp l a b -> Lcos2 lp l b a.
Proof.
    intros.
    unfold Lcos2 in *.
    ex_and H la.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    assert(exists lb, Lcos lb l b).
      apply(lcos_exists l b); auto.
      assert(HH:= lcos_lg_not_null la l a H).
      tauto.
    ex_and H7 lb.
    apply lcos_lg_anga in H8.
    spliter.
    exists lb.
    split.
      auto.
    assert(exists lp', Lcos lp' lb a).
      apply(lcos_exists lb a); auto.
      assert(HH:= lcos_lg_not_null lb l b H7).
      tauto.
    ex_and H11 lp'.
    assert(EqL lp lp').
      apply(l13_7 a b l la lb lp lp'); auto.
    apply lcos_lg_anga in H12.
    rewrite H11. tauto.
Qed.

Lemma lcos2_exists : forall l a b, Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Acute a -> Q_CongA_Acute b -> 
 exists lp, Lcos2 lp l a b.
Proof.
    intros.
    assert(HH:= lcos_exists l a H1 H H0).
    ex_and HH la.
    apply lcos_lg_anga in H3.
    spliter.
    assert(~ Q_Cong_Null la /\ ~ Q_Cong_Null l).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    clear H8.
    assert(HH:= lcos_exists la b H2 H5 H7).
    ex_and HH lab.
    exists lab.
    unfold Lcos2.
    exists la.
    split; auto.
Qed.

Lemma lcos2_exists' : forall l a b, Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Acute a -> Q_CongA_Acute b ->
 exists la, exists lab, Lcos la l a /\ Lcos lab la b.
Proof.
    intros.
    assert(HH:=lcos_exists l a H1 H H0).
    ex_and HH la.
    exists la.
    apply lcos_lg_anga in H3.
    spliter.
    assert(HP:=lcos_not_lg_null la l a H3).
    assert(HH:=lcos_exists la b H2 H5 HP).
    ex_and HH lab.
    exists lab.
    split; auto.
Qed.

Lemma lcos2_eq_refl : forall l a b, Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Acute a -> Q_CongA_Acute b -> Eq_Lcos2 l a b l a b.
Proof.
    intros.
    assert(HH:= lcos2_exists l a b H H0 H1 H2).
    ex_and HH lab.
    unfold Eq_Lcos2.
    exists lab.
    split; auto.
Qed.

Lemma lcos2_eq_sym : forall l1 a b l2 c d, Eq_Lcos2 l1 a b l2 c d -> Eq_Lcos2 l2 c d l1 a b.
Proof.
    intros.
    unfold Eq_Lcos2 in *.
    ex_and H lp.
    exists lp.
    auto.
Qed.

Lemma lcos2_uniqueness: forall l l1 l2 a b, Lcos2 l1 l a b -> Lcos2 l2 l a b -> EqL l1 l2.
Proof.
    intros.
    unfold Lcos2 in *.
    ex_and H la.
    ex_and H0 lb.
    assert(EqL la lb).
      apply (l13_6 a _ _ l); auto.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H1.
    spliter.
    assert(Lcos l2 la b).
      rewrite H3;auto.
    apply (l13_6 b _ _ la); auto.
Qed.

Lemma lcos2_eql_lcos2 : forall lla llb la lb a b, Lcos2 la lla a b -> EqL lla llb -> EqL la lb -> Lcos2 lb llb a b.
Proof.
    intros.
    unfold Lcos2 in *.
    ex_and H l.
    exists l.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H2.
    spliter.
    split.
    rewrite <- H0;auto.
    rewrite <- H1;auto.
Qed.

Lemma lcos2_lg_anga : forall lp l a b, Lcos2 lp l a b -> Lcos2 lp l a b /\ Q_Cong lp /\ Q_Cong l /\ Q_CongA_Acute a /\ Q_CongA_Acute b.
Proof.
    intros.
    split; auto.
    unfold Lcos2 in H.
    ex_and H ll.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    split; auto.
Qed.

Lemma lcos2_eq_trans : forall l1 a b l2 c d l3 e f, Eq_Lcos2 l1 a b l2 c d -> Eq_Lcos2 l2 c d l3 e f
                                   -> Eq_Lcos2 l1 a b l3 e f.
Proof.
    intros.
    unfold Eq_Lcos2 in *.
    ex_and H lp.
    ex_and H0 lq.
    exists lp.
    split; auto.
    assert(EqL lp lq).
      eapply (lcos2_uniqueness l2 _ _ c d); auto.
    apply lcos2_lg_anga in H2.
    apply lcos2_lg_anga in H1.
    spliter.
    eapply (lcos2_eql_lcos2 l3 _ lq); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos_eq_lcos2_eq : forall la lb a b c, Q_CongA_Acute c -> Eq_Lcos la a lb b -> Eq_Lcos2 la a c lb b c.
Proof.
    intros.
    assert(HH0:=H0).
    unfold Eq_Lcos in HH0.
    ex_and HH0 lp.
    apply lcos_lg_anga in H1.
    apply lcos_lg_anga in H2.
    spliter.
    clear H7.
    assert(~ Q_Cong_Null lp /\ ~ Q_Cong_Null la).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    unfold Eq_Lcos2.
    assert(HH:= lcos_exists lp c H H4 H7).
    ex_and HH lq.
    exists lq.
    split.
      unfold Lcos2.
      exists lp.
      split; auto.
    unfold Lcos2.
    exists lp.
    split; auto.
Qed.

Lemma lcos2_lg_not_null: forall lp l a b, Lcos2 lp l a b -> ~ Q_Cong_Null l /\ ~ Q_Cong_Null lp.
Proof.
    intros.
    unfold Lcos2 in H.
    ex_and H la.
    apply lcos_lg_not_null in H.
    apply lcos_lg_not_null in H0.
    spliter.
    split; auto.
Qed.

Lemma lcos3_lcos_1_2 : forall lp l a b c, Lcos3 lp l a b c <-> exists la, Lcos la l a /\ Lcos2 lp la b c.
Proof.
    intros.
    split.
      intro.
      unfold Lcos3 in H.
      ex_and H la.
      ex_and H0 lab.
      exists la.
      split; auto.
      unfold Lcos2.
      exists lab.
      split; auto.
    intro.
    ex_and H la.
    unfold Lcos2 in H0.
    ex_and H0 lab.
    unfold Lcos3.
    exists la.
    exists lab.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_lcos_2_1 : forall lp l a b c, Lcos3 lp l a b c <-> exists lab, Lcos2 lab l a b /\ Lcos lp lab c.
Proof.
    intros.
    split.
      intro.
      unfold Lcos3 in H.
      ex_and H la.
      ex_and H0 lab.
      exists lab.
      split.
        unfold Lcos2.
        exists la.
        split; assumption.
      assumption.
    intro.
    ex_and H lab.
    unfold Lcos3.
    unfold Lcos2 in H.
    ex_and H la.
    exists la.
    exists lab.
    split; auto.
Qed.


Lemma lcos3_permut3 : forall lp l a b c, Lcos3 lp l a b c -> Lcos3 lp l b a c.
Proof.
    intros.
    assert(HH:= lcos3_lcos_2_1 lp l a b c).
    destruct HH.
    assert(exists lab : Tpoint -> Tpoint -> Prop, Lcos2 lab l a b /\ Lcos lp lab c).
      apply lcos3_lcos_2_1; auto.
    ex_and H2 lab.
    apply lcos2_comm in H2.
    apply lcos3_lcos_2_1.
    exists lab.
    split; auto.
Qed.


Lemma lcos3_permut1 : forall lp l a b c, Lcos3 lp l a b c -> Lcos3 lp l a c b.
Proof.
    intros.
    assert(HH:= lcos3_lcos_1_2 lp l a b c).
    destruct HH.
    assert(exists la : Tpoint -> Tpoint -> Prop, Lcos la l a /\ Lcos2 lp la b c).
      apply lcos3_lcos_1_2; auto.
    ex_and H2 la.
    apply lcos2_comm in H3.
    apply lcos3_lcos_1_2.
    exists la.
    split; auto.
Qed.

Lemma lcos3_permut2 : forall lp l a b c, Lcos3 lp l a b c -> Lcos3 lp l c b a.
Proof.
    intros.
    apply lcos3_permut3.
    apply lcos3_permut1.
    apply lcos3_permut3.
    auto.
Qed.

Lemma lcos3_exists : forall l a b c, Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Acute a -> Q_CongA_Acute b -> Q_CongA_Acute c ->
 exists lp, Lcos3 lp l a b c.
Proof.
    intros.
    assert(HH:= lcos_exists l a H1 H H0).
    ex_and HH la.
    apply lcos_lg_anga in H4.
    spliter.
    assert(~ Q_Cong_Null la /\ ~ Q_Cong_Null l).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    clear H9.
    clear H7.
    assert(HH:= lcos_exists la b H2 H6 H8).
    ex_and HH lab.
    apply lcos_lg_anga in H7.
    spliter.
    assert(~ Q_Cong_Null lab /\ ~ Q_Cong_Null la).
      apply (lcos_lg_not_null _ _ b).
      auto.
    spliter.
    assert(HH:= lcos_exists lab c H3 H10 H12).
    ex_and HH lp.
    exists lp.
    unfold Lcos3.
    exists la.
    exists lab.
    split;auto.
Qed.

(*----------------------------------------*)

Lemma lcos3_eq_refl : forall l a b c, Q_Cong l -> ~ Q_Cong_Null l -> Q_CongA_Acute a -> Q_CongA_Acute b -> Q_CongA_Acute c -> Eq_Lcos3 l a b c l a b c.
Proof.
    intros.
    assert(HH:= lcos3_exists l a b c H H0 H1 H2 H3).
    ex_and HH lp.
    unfold Eq_Lcos3.
    exists lp.
    split; auto.
Qed.

Lemma lcos3_eq_sym : forall l1 a b c l2 d e f, Eq_Lcos3 l1 a b c l2 d e f -> Eq_Lcos3 l2 d e f l1 a b c.
Proof.
    intros.
    unfold Eq_Lcos3 in *.
    ex_and H lp.
    exists lp.
    auto.
Qed.

Lemma lcos3_uniqueness: forall l l1 l2 a b c, Lcos3 l1 l a b c -> Lcos3 l2 l a b c -> EqL l1 l2.
Proof.
    intros.
    unfold Lcos3 in *.
    ex_and H la.
    ex_and H1 lab.
    ex_and H0 la'.
    ex_and H3 lab'.
    assert(EqL la la').
      apply (l13_6 a _ _ l); auto.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H4.
    spliter.
    assert(Lcos lab' la b).
      rewrite H5;auto.
    assert(EqL lab lab') by
      (apply (l13_6 b _ _ la); auto).
    assert(Lcos l2 lab c).
      rewrite H19. auto.
    apply (l13_6 c _ _ lab); auto.
Qed.


Lemma lcos3_eql_lcos3 : forall lla llb la lb a b c, Lcos3 la lla a b c -> EqL lla llb -> EqL la lb -> Lcos3 lb llb a b c.
Proof.
    intros.
    unfold Lcos3 in *.
    ex_and H lpa.
    exists lpa.
    ex_and H2 lpab.
    exists lpab.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    spliter.
    split.
    rewrite <- H0;auto.
    split.
      auto.
    rewrite <- H1;auto.
Qed.

Lemma lcos3_lg_anga : forall lp l a b c, Lcos3 lp l a b c -> Lcos3 lp l a b c /\ Q_Cong lp /\ Q_Cong l /\ Q_CongA_Acute a /\ Q_CongA_Acute b /\ Q_CongA_Acute c.
Proof.
    intros.
    split; auto.
    unfold Lcos3 in H.
    ex_and H la.
    ex_and H0 lab.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_lg_not_null: forall lp l a b c, Lcos3 lp l a b c -> ~ Q_Cong_Null l /\ ~ Q_Cong_Null lp.
Proof.
    intros.
    unfold Lcos3 in H.
    ex_and H la.
    ex_and H0 lab.
    apply lcos_lg_not_null in H.
    apply lcos_lg_not_null in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_eq_trans : forall l1 a b c l2 d e f l3 g h i,
 Eq_Lcos3 l1 a b c l2 d e f -> Eq_Lcos3 l2 d e f l3 g h i -> Eq_Lcos3 l1 a b c l3 g h i.
Proof.
    intros.
    unfold Eq_Lcos3 in *.
    ex_and H lp.
    ex_and H0 lq.
    exists lp.
    split; auto.
    assert(EqL lp lq).
      eapply (lcos3_uniqueness l2 _ _ d e f); auto.
    apply lcos3_lg_anga in H2.
    apply lcos3_lg_anga in H1.
    spliter.
    eapply (lcos3_eql_lcos3 l3 _ lq); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos_eq_lcos3_eq : forall la lb a b c d, Q_CongA_Acute c -> Q_CongA_Acute d -> Eq_Lcos la a lb b -> Eq_Lcos3 la a c d lb b c d.
Proof.
    intros.
    assert(HH1:=H1).
    unfold Eq_Lcos in HH1.
    ex_and HH1 lp.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    spliter.
    assert(~ Q_Cong_Null lp /\ ~ Q_Cong_Null la).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    assert(HH:= lcos_exists lp c H H5 H10).
    ex_and HH lq.
    apply lcos_lg_anga in H12.
    spliter.
    assert(~ Q_Cong_Null lq /\ ~ Q_Cong_Null lp).
      apply (lcos_lg_not_null _ _ c); auto.
    spliter.
    assert(HH:= lcos_exists lq d H0 H14 H16).
    ex_and HH lm.
    unfold Eq_Lcos3.
    exists lm.
    split; unfold Lcos3.
      exists lp.
      exists lq.
      split; auto.
    exists lp.
    exists lq.
    split; auto.
Qed.

Lemma lcos2_eq_lcos3_eq : forall la lb a b c d e, Q_CongA_Acute e -> Eq_Lcos2 la a b lb c d -> Eq_Lcos3 la a b e lb c d e.
Proof.
    intros.
    assert(HH0:=H0).
    unfold Eq_Lcos2 in HH0.
    ex_and HH0 lp.
    apply lcos2_lg_anga in H1.
    apply lcos2_lg_anga in H2.
    spliter.
    assert(~ Q_Cong_Null la /\ ~ Q_Cong_Null lp).
      eapply (lcos2_lg_not_null _ _ a b).
      auto.
    spliter.
    assert(HH:= lcos_exists lp e H H3 H12).
    ex_and HH lq.
    apply lcos_lg_anga in H13.
    spliter.
    assert(~ Q_Cong_Null lq /\ ~ Q_Cong_Null lp).
      apply (lcos_lg_not_null _ _ e); auto.
    spliter.
    unfold Eq_Lcos3.
    exists lq.
    split; apply lcos3_lcos_2_1; exists lp; split; auto.
Qed.

End Cosinus2.