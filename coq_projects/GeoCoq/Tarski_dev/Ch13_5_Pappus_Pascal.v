(* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_4_cos.
Require Export GeoCoq.Tarski_dev.Annexes.project.

Section Pappus_Pascal.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma l13_10_aux1 : forall O A B P Q la lb lp lq,
 Col O A B -> Col O P Q -> Perp O P P A -> Perp O Q Q B ->
 Q_Cong la -> Q_Cong lb -> Q_Cong lp -> Q_Cong lq -> la O A -> lb O B -> lp O P -> lq O Q ->
 exists a, Q_CongA_Acute a /\ Lcos lp la a /\ Lcos lq lb a.
Proof.
    intros.
    assert(Acute A O P).
      apply (perp_acute _ _ P);finish.
    assert(P <> O).
      intro.
      subst P.
      apply perp_not_eq_1 in H1.
      tauto.
    assert(A <> O).
      intro.
      subst A.
      apply perp_not_col in H1.
      apply H1.
      Col.
    assert(Q <> O).
      intro.
      subst Q.
      apply perp_not_eq_1 in H2.
      tauto.
    assert(B <> O).
      intro.
      subst B.
      apply perp_not_col in H2.
      apply H2.
      Col.
    assert(HH:= anga_exists A O P H13 H12 H11).
    ex_and HH a.
    assert(a B O Q).
      assert(~ Par O P A P).
        intro.
        unfold Par in H18.
        induction H18.
          unfold Par_strict in H18.
          spliter.
          apply H21.
          exists P.
          split; Col.
        spliter.
        apply perp_comm in H1.
        apply perp_not_col in H1.
        apply H1.
        Col.
      assert(A <> P).
        apply perp_not_eq_2 in H1.
        auto.
      assert(Proj O O O P A P).
        unfold Proj.
        repeat split; Col.
      assert(Proj A P O P A P).
        unfold Proj.
        repeat split; Col.
        left.
        apply par_reflexivity.
        auto.
      assert(Proj B Q O P A P).
        unfold Proj.
        repeat split; Col.
        left.
        apply (l12_9 _ _ _ _ O P); Cop.
          apply perp_sym.
          eapply (perp_col _ Q); Col.
          Perp.
        Perp.
      induction H.
        assert(Bet O P Q).

        apply(per23_preserves_bet O A B P Q); auto.
        apply perp_in_per.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.
apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.

   (*       apply(project_preserves_bet O P A P O A B O P Q); auto. *)
        assert(CongA A O P B O Q).
          eapply (out_conga B _ Q B _ Q).
            apply conga_refl; auto.
            unfold Out.
            repeat split; auto.
            unfold Out.
            repeat split; auto.
            apply out_trivial; auto.
          apply out_trivial; auto.
        apply (anga_conga_anga _ A O P); auto.
      induction H.
        assert(Bet P Q O).

apply between_symmetry.
apply(per23_preserves_bet O B A Q P); Between.
Col.

apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.

 (*         apply(project_preserves_bet O P A P A B O P Q O); auto.*)
        assert(CongA A O P B O Q).
          eapply (out_conga B _ Q B _ Q).
            apply conga_refl; auto.
            unfold Out.
            repeat split; auto.
            left.
            Between.
            unfold Out.
            repeat split; auto.
            left.
            Between.
            apply out_trivial; auto.
          apply out_trivial; auto.
        apply (anga_conga_anga _ A O P); auto.
      assert(Bet Q O P).

apply(per13_preserves_bet B O A Q P); auto.
Col.
apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.

 (*       apply(project_preserves_bet O P A P B O A Q O P); auto. *)
      assert(CongA A O P B O Q).
        eapply (l11_14 ); Between.
      apply (anga_conga_anga _ A O P); auto.
    exists a.
    repeat split; auto.
      exists O.
      exists P.
      exists A.
      repeat split; auto.
        apply perp_in_per.
        Perp.
      apply anga_sym; auto.
    exists O.
    exists Q.
    exists B.
    repeat split; auto.
      apply perp_in_per.
      Perp.
    apply anga_sym; auto.
Qed.

Lemma l13_10_aux2 : forall O A B la lla lb llb,
 Col O A B  -> Q_Cong la -> Q_Cong lla -> Q_Cong lb -> Q_Cong llb -> la O A -> lla O A -> lb O B -> llb O B ->
 A <> O -> B <> O -> exists a, Q_CongA_Acute a /\ Lcos lla la a /\ Lcos llb lb a.
Proof.
    intros.
    assert(HH:=anga_exists A O A H8 H8 (acute_trivial A O H8)).
    ex_and HH a.
    exists a.
    split; auto.
    assert(Q_CongA_Null_Acute a).
      assert(Out O A A /\ Q_CongA_Null_Acute a).
        apply(anga_col_null a A O A); auto.
        Col.
      tauto.
    split.
      assert(EqL la lla).
        apply ex_eql.
        exists O.
        exists A.
        repeat split; auto.
      rewrite <- H13.
      apply null_lcos; auto.
      intro.
      unfold Q_Cong_Null in H14.
      spliter.
      ex_and H15 X.
      assert(HH:= lg_cong la O A X X H0 H4 H16).
      treat_equalities.
      tauto.
    assert(HH:=anga_exists B O B H9 H9 (acute_trivial B O H9)).
    ex_and HH b.
    assert(EqA a b).
      assert(HH:=null_anga A O B O a b).
      apply HH; split; auto.
    assert(EqL lb llb).
      apply ex_eql.
      exists O.
      exists B.
      repeat split; auto.
    rewrite <- H16.
    apply null_lcos; auto.
    intro.
    unfold Q_Cong_Null in H17.
    spliter.
    ex_and H18 X.
    assert(HH:= lg_cong lb O B X X H2 H6 H19).
    treat_equalities.
    tauto.
Qed.


Lemma l13_6_bis : forall lp l1 l2 a, Lcos lp l1 a -> Lcos lp l2 a -> EqL l1 l2.
Proof.
    intros.
    induction(is_null_anga_dec a).
      apply lcos_lg_anga in H.
      apply lcos_lg_anga in H0.
      spliter.
      assert(HH:= null_lcos_eql lp l1 a H H1).
      assert(HP:= null_lcos_eql lp l2 a H0 H1).
      transitivity lp; auto.
      symmetry; auto.
      apply lcos_lg_anga in H.
      apply lcos_lg_anga in H0.
      spliter.
      assert (HH:= H).
      assert(HH0:= H0).
      unfold Lcos in HH.
      unfold Lcos in HH0.
      spliter.
      ex_and H11 A.
      ex_and H16 B.
      ex_and H11 C.
      ex_and H15 A'.
      ex_and H19 B'.
      ex_and H15 C'.
      assert(HH:=not_null_not_col a B A C H4 H1 H18).
      assert(HP:=not_null_not_col a B' A' C' H4 H1 H21).
      assert(B <> C).
        intro.
        subst C.
        apply HH.
        Col.
      assert(B' <> C').
        intro.
        subst C'.
        apply HP.
        Col.
      assert(HQ:= anga_distincts a B A C H4  H18).
      assert(HR:= anga_distincts a B' A' C' H4 H21).
      spliter.
      assert(Cong A B A' B').
        apply (lg_cong lp); auto.
      assert(CongA B A C B' A' C').
        apply (anga_conga a); auto.
      assert(CongA C B A C' B' A').
        apply l11_16; auto.
      assert(Cong A C A' C' /\ Cong B C B' C' /\ CongA A C B A' C' B').
        apply(l11_50_1 A B C A' B' C'); auto.
          intro.
          apply HH.
          Col.
        apply conga_comm.
        auto.
      spliter.
      apply (all_eql A' C').
        split; auto.
      split; auto.
      eapply (lg_cong_lg _ A C); auto.
    unfold Lcos in *;intuition.
Qed.


Lemma lcos3_lcos2 : forall l1 l2 a b c d n, Eq_Lcos3 l1 a b n l2 c d n -> Eq_Lcos2 l1 a b l2 c d.
Proof.
    intros.
    unfold Eq_Lcos3 in H.
    ex_and H lp.
    unfold Eq_Lcos2.
    apply lcos3_lcos_2_1 in H.
    apply lcos3_lcos_2_1 in H0.
    ex_and H ll1.
    ex_and H0 ll2.
    assert (EqL ll1 ll2).
      eapply(l13_6_bis lp _ _ n); auto.
    exists ll1.
    split; auto.
    apply lcos2_lg_anga in H.
    apply lcos2_lg_anga in H0.
    spliter.
    apply(lcos2_eql_lcos2 l2 l2 ll2 ll1 c d); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos2_lcos : forall l1 l2 a b c, Eq_Lcos2 l1 a c l2 b c -> Eq_Lcos l1 a l2 b.
Proof.
    intros.
    unfold Eq_Lcos2 in H.
    ex_and H lp.
    unfold Lcos2 in H.
    unfold Lcos2 in H0.
    ex_and H lx.
    ex_and H0 ly.
    unfold Eq_Lcos.
    assert(EqL lx ly).
      eapply(l13_6_bis lp _ _ c); auto.
    exists lx.
    split; auto.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    rewrite H3;auto.
Qed.

Lemma lcos_per_anga : forall O A P la lp a, Lcos lp la a -> la O A -> lp O P -> Per A P O -> a A O P.
Proof.
    intros.
    assert(HH:= H).
    unfold Lcos in HH.
    spliter.
    ex_and H6 O'.
    ex_and H7 P'.
    ex_and H6 A'.
    assert(Cong O A O' A').
      apply (lg_cong la); auto.
    assert(Cong O P O' P').
      apply (lg_cong lp); auto.
    assert(HH:= lcos_lg_not_null lp la a H).
    spliter.
    induction(eq_dec_points A P).
      subst A.
      assert(Cong O' A' O' P').
        apply (cong_transitivity _ _ O P); Cong.
      assert(A' = P').
        induction(col_dec A' P' O').
          assert(A' = P' \/ O' = P').
            apply l8_9; auto.
          induction H16.
            auto.
          subst P'.
          eapply (cong_identity _  O' O'); Cong.
        assert(Lt P' A' A' O' /\ Lt P' O' A' O').
          assert_diffs; apply(l11_46 A' P' O'); auto.
        spliter.
        unfold Lt in H17.
        spliter.
        apply False_ind.
        apply H18.
        Cong.
      subst A'.
      assert(Q_CongA_Null_Acute a).
        apply(out_null_anga a P' O' P'); auto.
        apply out_trivial.
        intro.
        subst P'.
        apply H12.
        unfold Q_Cong_Null.
        split.
          auto.
        exists O'.
        auto.
      apply(is_null_all a P O).
        intro.
        subst P.
        apply H12.
        unfold Q_Cong_Null.
        split.
          auto.
        exists O.
        auto.
      auto.
    assert(O <> P).
      intro.
      subst P.
      apply H12.
      split.
        auto.
      exists O.
      auto.
    induction(col_dec A P O).
      assert (HH:=anga_distincts a P' O' A' H5 H9).
      spliter.
      assert(A' <> P').
        intro.
        subst A'.
        assert(A = P \/ O = P).
          apply l8_9; auto.
        induction H19.
          auto.
        contradiction.
      assert(~ Col A P O).
        apply(per_not_col A P O); auto.
      contradiction.
    assert (HH:=anga_distincts a P' O' A' H5 H9).
    spliter.
    assert(A' <> P').
      intro.
      subst A'.
      assert(Cong O P O A).
        apply (cong_transitivity _ _ O' P'); Cong.
      assert(Lt P A A O /\ Lt P O A O).
        assert_diffs; apply(l11_46 A P O); auto.
      spliter.
      unfold Lt in H21.
      spliter.
      apply H22.
      Cong.
    assert(CongA A P O A' P' O').
      apply l11_16; auto.
    assert(Cong P A P' A' /\ CongA P A O P' A' O' /\ CongA P O A P' O' A').
      assert(Lt P A A O /\ Lt P O A O).
        assert_diffs; apply(l11_46 A P O); auto.
      spliter.
      unfold Lt in H22.
      spliter.
      apply(l11_52 A P O A' P' O' ); Cong.
    spliter.
    apply conga_comm in H23.
    apply (anga_conga_anga a A' O' P'); auto.
      apply (anga_sym a); auto.
    apply conga_sym.
    auto.
Qed.

Lemma lcos_lcos_cop__col : forall la lb lp a b O A B P,
 Lcos lp la a -> Lcos lp lb b -> la O A -> lb O B -> lp O P -> a A O P -> b B O P -> Coplanar O A B P ->
 Col A B P.
Proof.
    intros.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    assert(Per O P A).
      apply (lcos_per O P A lp la a); auto.
      apply anga_sym; auto.
    assert(Per O P B).
      apply (lcos_per O P B lp lb b); auto.
      apply anga_sym; auto.
    apply cop_per2__col with O; Perp.
    intro.
    subst P.
    assert(HH:=lcos_lg_not_null lp la a H).
    spliter.
    apply H15.
    unfold Q_Cong_Null.
    split; auto.
    exists O.
    auto.
Qed.

(*****strange ****)

Lemma per13_preserves_bet_inv : forall A B C A' C', Bet A' B C' -> B <> A' -> B <> C' ->  Col A B C  -> Per B A' A -> Per B C' C -> Bet A B C.
Proof.
intros.
assert(Col A' B C').
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.
assert(HH:=l8_9 B C' C H4 H6 ).
induction HH.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col B A' A).
ColR.
assert(HH:=l8_9 B A' A H3 H7).
induction HH;
contradiction.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp_bis in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp_bis in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A'); Perp; Cop.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A' A B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C' C B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(OS A' A B C').
apply out_one_side.
left; auto.
repeat split.
intro.
subst A'.
apply H11.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
assumption.

assert(OS C' C B A').
apply out_one_side.
left; auto.
repeat split.
intro.
subst C'.
apply H12.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold OS in H10.
ex_and H10 X.
unfold TS in H10.
spliter.
apply H10.
Col.
left.
Between.

assert(OS A' A B C).
apply(one_side_transitivity _ _ _ C'); auto.
apply invert_one_side.
apply one_side_symmetry.
assumption.

assert(OS C C' B A).
apply(one_side_transitivity _ _ _ A'); auto.
apply invert_one_side.
assumption.
apply one_side_symmetry.
assumption.

apply invert_one_side in H15.

assert(HP:= col_one_side_out A A' B C H2 H15).

assert(Out C B A).
apply(col_one_side_out C C' B A); Col.

unfold Out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.

(****************************)

spliter.
assert(Perp A' C' A A').
apply (perp_col _ B); Perp.
intro.
subst C'.
apply between_identity in H.
subst A'.
apply perp_distinct in H9.
tauto.
apply perp_not_col in H14.

apply False_ind.
apply H14.
ColR.
Qed.

Lemma l13_10_aux3 : forall A B C A' B' C' O,
  ~ Col O A A' ->
  B <> O -> C <> O -> Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Perp2 B C' C B' O -> Perp2 C A' A C' O ->
  Bet A O B -> Bet A' O B'.
Proof.
    intros.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    assert(Col O A C).
      apply (col_transitivity_1 _ B); Col.
    assert(Col O A' C').
      apply (col_transitivity_1 _ B'); Col.
    assert(Bet C A O \/ Bet A C O \/ Bet O C B \/ Bet O B C).
      apply(fourth_point A O B C); auto.
      ColR.
    induction H15.
      assert(Bet O C' A').
        apply(perp2_preserves_bet23 O A C C' A'); Between.
          Col.
          intro.
          apply H.
               ColR.
               apply perp2_sym.
        auto.

      assert(Bet B' O C').
        apply(perp2_preserves_bet13 O B C B' C'); eBetween.
          intro.
          apply H.
          ColR.
          eBetween.

    (***************)
    induction H15.
      assert(Bet C O B).
        eBetween.
      assert(Bet O A' C').
        apply(perp2_preserves_bet23 O C A A' C'); Between.
        intro.
        apply H.
ColR.

      assert(Bet B' O C').
        apply(perp2_preserves_bet13 O B C B' C'); Between.
          intro.
          apply H.
ColR.
eBetween.
    induction H15.
      assert(Bet A O C).
        eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); Between.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet C' O A').
        apply(perp2_preserves_bet13 O C A C' A'); Col.
Between.
          intro.
          apply H.
ColR.
eBetween.
    assert(Bet A O C).
      eBetween.
    assert(Bet O C' B').
      apply(perp2_preserves_bet23 O B C C' B'); Col.
      intro.
      apply H.
ColR.
    assert(Bet C' O A').
      apply(perp2_preserves_bet13 O C A C' A'); Col.
Between.
        intro.
        apply H.
ColR.
    eBetween.
Qed.

Lemma l13_10_aux4 : forall A B C A' B' C' O,
  ~ Col O A A' -> B <> O -> C <> O -> Col O A B -> Col O B C -> B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Perp2 B C' C B' O -> Perp2 C A' A C' O -> Bet O A B ->
  Out O A' B'.
Proof.
    intros.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    assert(Col O A C).
    ColR.
    induction(eq_dec_points A B).
      subst B.
    assert (HH : Par C A' C B').
      assert(~ Col A C' O).
        intro.
        apply H.
        ColR.
    assert(HH:= perp2_pseudo_trans C A' A C' C B' O H9 H8 H14).
      ex_and HH X.
      ex_and H15 Y.
      apply (l12_9 _ _ _ _ X Y); Perp.
        Cop.
        Cop.
        Cop.
        exists O.
        left.
        split; Col.
      assert(A' = B').
        assert(Col A' B' C).
          induction HH.
            apply False_ind.
            apply H14.
            exists C.
            split; Col.
          spliter.
          Col.
        apply (l6_21 O C' C B'); Col.
          intro.
          apply H.
ColR.
        intro.
        subst B'.
apply par_distinct in HH.
tauto.
ColR.
      subst B'.
      apply out_trivial.
      auto.


    assert(Bet C O A \/ Bet O C A \/ Bet A C B \/ Bet A B C).
      apply(fourth_point O A B C); auto.

    induction H15.
      assert(Bet B' O C').
        assert(Bet C O B).
        eBetween.
        apply(perp2_preserves_bet13 O B C B' C'); Between.
          intro.
          apply H.
ColR.
  (*        assert(Col O A B').

            apply (col_transitivity_1 _ C); Col.
          apply (col_transitivity_1 _ B'); Col.
        apply perp2_sym.
        auto.*)
      assert(Bet A' O C').
        apply(perp2_preserves_bet13 O A C A' C');Between.
        ColR.
apply perp2_sym.
assumption.
repeat split; auto.
apply(l5_2 C' O A' B'); Between.

    induction H15.
      assert(Bet O C B).
eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); Col.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet O A' C').
        apply(perp2_preserves_bet23 O C A A' C'); Between.
 ColR.
        intro.
        apply H.
ColR.
      repeat split; auto.
apply(l5_3 O A' B' C'); auto.

    induction H15.
      assert(Bet O A C).
eBetween.
      assert(Bet O C' A').
        apply(perp2_preserves_bet23 O A C C' A'); auto.
ColR.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet O C B).
eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); auto.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
repeat split; auto.
right.
eBetween.

(*      assert(Bet O B' A').
eBetween.
*)
    assert(Bet O A C).
eBetween.
    assert( Bet O B C).
eBetween.

    assert(Bet O C' B').
      apply(perp2_preserves_bet23  O B C C' B'); Col.
      intro.
      apply H.
ColR.
    assert(Bet O C' A').
      apply(perp2_preserves_bet23  O A C C' A'); auto.
ColR.
        intro.
        apply H.
ColR.
      apply perp2_sym.
      auto.
    repeat split; auto.
    apply (l5_1 _ C'); auto.
Qed.

Lemma l13_10_aux5 : forall A B C A' B' C' O,
 ~ Col O A A' -> B <> O -> C <> O -> Col O A B -> Col O B C ->
 B' <> O -> C' <> O -> Col O A' B' -> Col O B' C'->
 Perp2 B C' C B' O -> Perp2 C A' A C' O -> Out O A B ->
 Out O A' B'.
Proof.
    intros.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    induction H10.
    spliter.
    induction H13.
      eapply (l13_10_aux4 A B C _ _ C'); auto.
    apply l6_6.
    apply(l13_10_aux4 B A C B' A' C'); try assumption.
      intro.
      apply H.
      ColR.
      Col.
      ColR.
      Col.
      ColR.
      apply perp2_sym.
      assumption.
    apply perp2_sym.
    auto.
Qed.

Lemma cop_per2__perp : forall A B X Y,
 A <> B -> X <> Y ->
 (B <> X \/ B <> Y) ->
 Coplanar A B X Y ->
 Per A B X -> Per A B Y ->
 Perp A B X Y.
Proof.
    intros.
    induction H1.
      assert(HH:=H3).
      apply per_perp_in in H3; auto.
      apply perp_in_perp_bis in H3.
      induction H3.
        apply perp_not_eq_1 in H3.
        tauto.
      apply perp_sym.
      apply (perp_col _ B); auto.
        Perp.
      apply col_permutation_5.
      apply cop_per2__col with A; Perp; Cop.
    assert(HH:=H4).
    apply per_perp_in in H4; auto.
    apply perp_in_perp_bis in H4.
    induction H4.
      apply perp_not_eq_1 in H4.
      tauto.
    apply perp_sym.
    apply perp_left_comm.
    apply (perp_col _ B); auto.
      Perp.
    apply col_permutation_5.
    eapply cop_per2__col with A; Perp; Cop.
Qed.

Lemma l13_10 : forall A B C A' B' C' O,
  ~ Col O A A' -> B <> O -> C <> O ->
  Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' ->
  Perp2 B C' C B' O -> Perp2 C A' A C' O ->
  Perp2 A B' B A' O.
Proof.
    intros.
    assert(HH8:= H8).
    assert(HH9:= H9).
    assert(Col O A C).
      apply (col_transitivity_1 _ B); Col.
    assert(Col O A' C').
      apply (col_transitivity_1 _ B'); Col.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(~ Col A B' O).
      intro.
      apply H.
      apply (col_transitivity_1 _ B'); Col.
    apply perp2_perp_in in HH8.
      ex_and HH8 L.
      ex_and H14 L'.
      apply perp2_perp_in in HH9.
        ex_and HH9 M.
        ex_and H19 M'.
        assert(HH:=l8_18_existence A B' O H13).
        ex_and HH N.
        unfold Perp2.
        exists O.
        exists N.
        repeat split.
          Col.
          Perp.
        assert(HH:=lg_exists O A).
        ex_and HH la.
        assert(HH:=lg_exists O B).
        ex_and HH lb.
        assert(HH:=lg_exists O C).
        ex_and HH lc.
        assert(HH:=lg_exists O A').
        ex_and HH la'.
        assert(HH:=lg_exists O B').
        ex_and HH lb'.
        assert(HH:=lg_exists O C').
        ex_and HH lc'.
        assert(HH:=lg_exists O L).
        ex_and HH ll.
        assert(HH:=lg_exists O L').
        ex_and HH ll'.
        assert(HH:=lg_exists O M).
        ex_and HH lm.
        assert(HH:=lg_exists O M').
        ex_and HH lm'.
        assert(HH:=lg_exists O N).
        ex_and HH ln.
        assert(O <> L).
          apply perp_in_perp_bis in H17.
          induction H17.
            apply perp_not_eq_1 in H17.
            tauto.
          apply perp_not_eq_1 in H17.
          auto.
        assert(O <> L').
          apply perp_in_perp_bis in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_not_eq_1 in H18.
          auto.
        assert(~ Col O B B').
          intro.
          apply H.
          assert(Col O A B').
            eapply (col_transitivity_1 _ B); Col.
          eapply (col_transitivity_1 _ B'); Col.
        assert(~ Col O C C').
          intro.
          apply H.
          assert(Col O A C').
            eapply (col_transitivity_1 _ C); Col.
          eapply (col_transitivity_1 _ C'); Col.
        assert(exists a, Q_CongA_Acute a /\ Lcos ll lb a /\ Lcos ll' lc a).
          induction(eq_dec_points B L).
            subst L.
            assert(C = L').
              eapply (l6_21 O B B' L'); Col.
              intro.
              subst L'.
              contradiction.
            subst L'.
            apply (l13_10_aux2 O B C); Col.
          apply (l13_10_aux1 O B C L L'); Col.
            apply perp_in_perp_bis in H17.
            induction H17.
              apply perp_not_eq_1 in H17.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ C');auto.
            Perp.
          apply perp_in_perp_bis in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ B'); auto.
            intro.
            subst L'.
            assert(Col O B L).
              eapply (col_transitivity_1 _ C); Col.
            apply H52.
            apply(l6_21 O C C' B B L); Col.
            intro.
            subst C'.
            unfold Perp_at in H17.
            tauto.
          Perp.
        ex_and H52 l'.
        assert(exists a, Q_CongA_Acute a /\ Lcos ll lc' a /\ Lcos ll' lb' a).
          induction(eq_dec_points C' L).
            subst L.
            assert(B' = L').
              eapply (l6_21 O C' C L'); Col.
              intro.
              subst L'.
              apply H51.
              Col.
            subst L'.
            eapply (l13_10_aux2 O C' B'); Col.
          apply (l13_10_aux1 O C' B' L L'); Col.
            apply perp_in_perp_bis in H17.
            induction H17.
              apply perp_not_eq_1 in H17.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ B); Col.
            Perp.
          apply perp_in_perp_bis in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ C);Col.
            intro.
            subst L'.
            assert(Col O C' L).
              eapply (col_transitivity_1 _ B'); Col.
            apply H55.
            apply(l6_21 O B' B C' C' L); Col.
            intro.
            subst C'.
            unfold Perp_at in H17.
            tauto.
          Perp.
        ex_and H55 l.
        assert(exists a, Q_CongA_Acute a /\ Lcos lm lc a /\ Lcos lm' la a).
          induction (eq_dec_points C M).
            subst M.
            assert(A = M').
              eapply (l6_21 O C C' M'); Col.
              intro.
              subst M'.
              contradiction.
            subst M'.
            apply (l13_10_aux2 O C A); Col.
          apply (l13_10_aux1 O C A M M'); Col.
            apply perp_in_perp_bis in H22.
            induction H22.
              apply perp_not_eq_1 in H22.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ A');auto.
            Perp.
          apply perp_in_perp_bis in H23.
          induction H23.
            apply perp_not_eq_1 in H23.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ C'); auto.
            intro.
            subst M'.
            assert(Col O C M).
              eapply (col_transitivity_1 _ A); Col.
            apply H58.
            apply(l6_21 O A A' C C M); Col.
            intro.
            subst A'.
            unfold Perp_at in H22.
            tauto.
          Perp.
        ex_and H58 m'.
        assert(exists a, Q_CongA_Acute a /\ Lcos lm la' a /\ Lcos lm' lc' a).
          induction(eq_dec_points A' M).
            subst M.
            assert(C' = M').
              eapply (l6_21 O A' A M'); Col.
              intro.
              subst M'.
              apply H.
              Col.
            subst M'.
            eapply (l13_10_aux2 O A' C'); Col.
            intro.
            subst A'.
            apply H.
            Col.
          apply (l13_10_aux1 O A' C' M M'); Col.
            apply perp_in_perp_bis in H22.
            induction H22.
              apply perp_not_eq_1 in H22.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ C);Col.
            Perp.
          apply perp_in_perp_bis in H23.
          induction H23.
            apply perp_not_eq_1 in H23.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ A);Col.
            intro.
            subst M'.
            assert(Col O A' M).
              eapply (col_transitivity_1 _ C'); Col.
            apply H61.
            apply(l6_21 O C' C A' A' M); Col.
            intro.
            subst A'.
            unfold Perp_at in H22.
            tauto.
          Perp.
        ex_and H61 m.
        assert(exists a, Q_CongA_Acute a /\ Lcos ln la a).
          assert(exists a, Q_CongA_Acute a /\ a A O N).
            apply(anga_exists A O N).
              intro.
              subst A.
              apply H.
              Col.
              apply perp_not_eq_2 in H25.
              auto.
            induction(eq_dec_points A N).
              subst N.
              apply acute_trivial.
              intro.
              subst A.
              apply H.
              Col.
            eapply (perp_acute _ _ N).
              Col.
            apply perp_in_left_comm.
            apply perp_perp_in.
            apply perp_sym.
            apply (perp_col _ B').
              auto.
              Perp.
            Col.
          ex_and H64 n'.
          exists n'.
          split.
            auto.
          unfold Lcos.
          repeat split; auto.
          exists O.
          exists N.
          exists A.
          repeat split; auto.
            induction(eq_dec_points A N).
              subst N.
              apply l8_2.
              apply l8_5.
            apply perp_in_per.
            apply perp_in_comm.
            apply perp_perp_in.
            apply perp_left_comm.
            apply (perp_col _ B').
              auto.
              Perp.
            Col.
          apply anga_sym; auto.
        ex_and H64 n'.
        assert(exists a, Q_CongA_Acute a /\ Lcos ln lb' a).
          assert(exists a, Q_CongA_Acute a /\ a B' O N).
            apply(anga_exists B' O N).
              intro.
              subst B'.
              apply H50.
              Col.
              apply perp_not_eq_2 in H25.
              auto.
            induction(eq_dec_points B' N).
              subst N.
              apply acute_trivial.
              auto.
            eapply (perp_acute _ _ N).
              Col.
            apply perp_in_left_comm.
            apply perp_perp_in.
            apply perp_sym.
            apply (perp_col _ A).
              auto.
              Perp.
            Col.
          ex_and H66 n.
          exists n.
          split.
            auto.
          unfold Lcos.
          repeat split; auto.
          exists O.
          exists N.
          exists B'.
          repeat split; auto.
            induction(eq_dec_points B' N).
              subst N.
              apply l8_2.
              apply l8_5.
            apply perp_in_per.
            apply perp_in_comm.
            apply perp_perp_in.
            apply perp_left_comm.
            apply (perp_col _ A).
              auto.
              Perp.
            Col.
          apply anga_sym; auto.
        ex_and H66 n.
        assert(Eq_Lcos lc l' lb' l).
          unfold Eq_Lcos.
          exists ll'.
          split; auto.
        assert(Eq_Lcos lb l' lc' l).
          unfold Eq_Lcos.
          exists ll.
          split; auto.
        assert(Eq_Lcos lc m' la' m).
          unfold Eq_Lcos.
          exists lm.
          split; auto.
        assert(Eq_Lcos la m' lc' m).
          unfold Eq_Lcos.
          exists lm'.
          split; auto.
        assert(Eq_Lcos la n' lb' n).
          unfold Eq_Lcos.
          exists ln.
          split; auto.
        assert(exists lp, Lcos lp lb n').
          apply(lcos_exists lb n'); auto.
          intro.
          unfold Q_Cong_Null in H73.
          spliter.
          ex_and H74 X.
          apply H0.
          eapply (cong_identity _ _ X).
          apply (lg_cong lb); auto.
          apply (lg_sym lb); auto.
        ex_and H73 bn'.
        assert(exists lp, Lcos lp ll n').
          apply(lcos_exists ll n'); auto.
          intro.
          unfold Q_Cong_Null in H73.
          spliter.
          ex_and H75 X.
          apply H48.
          apply (cong_identity _ _ X).
          apply (lg_cong ll); auto.
        ex_and H73 bl'n'.
        assert(exists lp, Lcos lp bn' l').
          apply(lcos_exists bn' l'); auto.
            apply lcos_lg_anga in H74.
            spliter.
            auto.
          assert(HH:= lcos_lg_not_null bn' lb n' H74 ).
          tauto.
        ex_and H73 bn'l'.
        assert(Lcos2 bl'n' lb l' n').
          unfold Lcos2.
          exists ll.
          split; auto.
        assert(Lcos2 bn'l' lb n' l').
          unfold Lcos2.
          exists bn'.
          split; auto.
        assert(EqL bl'n' bn'l').
          apply lcos2_comm in H77.
          apply (lcos2_uniqueness lb _ _ l' n'); auto.
        apply lcos_lg_anga in H75.
        apply lcos_lg_anga in H76.
        spliter.
        assert(Eq_Lcos2 lb l' n' lb n' l').
          unfold Eq_Lcos2.
          exists bl'n'.
          split; auto.
          eapply (lcos2_eql_lcos2 lb _ bn'l').
            auto.
            reflexivity.
          symmetry; auto.
        assert(Eq_Lcos2 lb l' n' lc' l n').
          apply lcos_eq_lcos2_eq; auto.
        assert(Eq_Lcos3 lb l' n' m lc' l n' m).
          apply lcos2_eq_lcos3_eq; auto.
        assert(Eq_Lcos3 lb l' n' m lc' m l n').
          unfold Eq_Lcos3 in H87.
          ex_and H87 lp.
          unfold Eq_Lcos3.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(Eq_Lcos3 la m' l n' lc' m l n').
          apply lcos_eq_lcos3_eq; auto.
        assert(Eq_Lcos3 lb l' n' m la m' l n').
          apply (lcos3_eq_trans _ _ _ _ lc' m l n'); auto.
          apply lcos3_eq_sym; auto.
        assert(Eq_Lcos3 lb l' n' m la n' m' l).
          unfold Eq_Lcos3 in H90.
          ex_and H90 lp.
          unfold Eq_Lcos3.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(Eq_Lcos3 la n' m' l lb' n m' l).
          apply lcos_eq_lcos3_eq; auto.
        assert(Eq_Lcos3 lb l' n' m lb' n m' l).
          apply (lcos3_eq_trans _ _ _ _ la n' m' l); auto.
        assert(Eq_Lcos3 lb l' n' m lb' l n m').
          unfold Eq_Lcos3 in H93.
          ex_and H93 lp.
          unfold Eq_Lcos3.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(Eq_Lcos3 lb' l n m' lc l' n m').
          apply lcos_eq_lcos3_eq; auto.
          apply lcos_eq_sym; auto.
        assert(Eq_Lcos3 lb l' n' m lc l' n m').
          apply (lcos3_eq_trans _ _ _ _ lb' l n m'); auto.
        assert(Eq_Lcos3 lb l' n' m lc m' l' n).
          unfold Eq_Lcos3 in H96.
          ex_and H96 lp.
          unfold Eq_Lcos3.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(Eq_Lcos3 la' m l' n lc m' l' n).
          apply lcos_eq_lcos3_eq; auto.
          apply lcos_eq_sym; auto.
        assert(Eq_Lcos3 lb l' n' m la' m l' n).
          apply (lcos3_eq_trans _ _ _ _ lc m' l' n); auto.
          apply lcos3_eq_sym; auto.
        assert(Eq_Lcos3 lb l' n' m la' n l' m).
          unfold Eq_Lcos3 in H99.
          ex_and H99 lp.
          unfold Eq_Lcos3.
          exists lp.
          split; auto.
          apply lcos3_permut2.
          auto.
        assert(Eq_Lcos2 lb l' n' la' n l').
          apply (lcos3_lcos2 _ _ _ _ _ _ m); auto.
        assert(Eq_Lcos2 lb n' l' la' n l').
          unfold Eq_Lcos2 in H101.
          ex_and H101 lp.
          unfold Eq_Lcos2.
          exists lp.
          split; auto.
          apply lcos2_comm.
          auto.
        assert(Eq_Lcos lb n' la' n).
          apply (lcos2_lcos) in H102.
          auto.
        clear H85 H86 H87 H88 H89 H90 H91 H92 H93 H94 H95 H96 H97 H98 H99 H100 H101 H102.
(*************** we construct the length ln'  ********************)
        unfold Eq_Lcos in H103.
        ex_and H103 ln'.
        assert(O <> N).
          apply perp_not_eq_2 in H25; auto.
        apply lcos_lg_anga in H85.
        spliter.
(*************** we prove : n' A O N  ********************)
        assert(n' A O N).
          apply(lcos_per_anga _ _ _ la ln); auto.
          induction(eq_dec_points A N).
            subst N.
            apply l8_2.
            apply l8_5.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_left_comm.
          apply (perp_col _ B'); Col.
(*************** we prove : n B O N  ********************)
        assert(n B' O N).
          apply(lcos_per_anga _ _ _ lb' ln); auto.
          induction(eq_dec_points B' N).
            subst N.
            apply l8_2.
            apply l8_5.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_left_comm.
          apply (perp_col _ A); Col.
          Perp.
(*************** two cases  ********************)
        assert(Bet A O B \/ Out O A B \/ ~ Col A O B).
          apply(or_bet_out A O B); auto.
(*************** case : Bet A O B  ********************)
        induction H93.
(*************** we extend NO with N' such as ln' O N' ********************)
          assert(HH:=ex_point_lg_bet ln' N O H89).
          ex_and HH N'.
          assert(O <> N').
            intro.
            subst N'.
            assert(HH:=lcos_lg_not_null ln' lb n' H85).
            spliter.
            apply H96.
            unfold Q_Cong_Null.
            split; auto.
            exists O.
            auto.
          assert(A' <> B).
            intro.
            subst A'.
            contradiction.
(*************** we prove (Per O N' B) using Lcos ln' lb n'  ********************)        
            assert(Per O N' B).
            apply(lcos_per O N' B ln' lb n'); auto.
            assert(CongA N O A B O N').
(*************** pair of vertical angles (angles opposés par Le sommet) ********************)  
              apply(l11_13 N' O A A O N' N B ); Between.
              apply conga_left_comm.
              apply conga_refl; auto.
            apply (anga_conga_anga n' A O N); auto.
            apply conga_comm.
            auto.
(*************** we prove (Per O N' A') usinglcos ln' la' n  ********************) 
          assert(Per O N' A').
            apply(lcos_per O N' A' ln' la' n); auto.
            assert(CongA N O B' A' O N').
              apply(l11_13 N' O B' B' O N' N A' ); Between.
                apply conga_left_comm.
                apply conga_refl; auto.
                apply between_symmetry.
                apply(l13_10_aux3 A B C A' B' C' O); auto.
              intro.
              subst A'.
              apply H.
              Col.
            eapply (anga_conga_anga  n B' O N); auto.
            apply conga_comm.
            auto.
(*************** we prove (Perp O N B A')  ********************) 
          apply (perp_col _ N'); Col.
          apply cop_per2__perp; auto.
          induction(eq_dec_points N' B).
            right.
            subst N'.
            auto.
          left.
          auto.
          apply coplanar_perm_16.
          apply col_cop__cop with N; Col.
          apply coplanar_perm_5.
          apply col_cop__cop with B'; Col.
          exists A.
          right.
          left.
          split; Col.
        induction H93.
(*************** case : out O A B  ********************)
(*************** we construct N' on the half-line ON such as ln' O N' /\ out O N' N  ********************)        
          assert(exists N' : Tpoint, ln' O N' /\ Out O N' N).
            apply(ex_point_lg_out ln' O N H87 H89).
            assert(HH:=lcos_lg_not_null ln' la' n H86).
            spliter.
            auto.
          ex_and H94 N'.
(*************** we prove (Per O N' B) using Lcos ln' lb n'  ********************)
          assert(Per O N' B).
            apply(lcos_per O N' B ln' lb n'); auto.
            assert(CongA A O N B O N').
              apply(out_conga A O N A O N A N B N').
                apply conga_refl ; auto.
                apply out_trivial; auto.
                apply out_trivial; auto.
                auto.
              apply l6_6.
              auto.
            apply (anga_conga_anga n' A O N); auto.
            apply conga_right_comm.
            auto.
(*************** we prove (Per O N' A) using Lcos ln' la' n  ********************)
          assert(Per O N' A').
            apply(lcos_per O N' A' ln' la' n); auto.
            assert(CongA B' O N A' O N').
              apply(out_conga B' O N B' O N B' N A' N').
                apply conga_refl; auto.
                apply out_trivial; auto.
                apply out_trivial; auto.
                eapply (l13_10_aux5 B A C B' A' C'); Col.
                  intro.
                  subst A'.
                  apply H.
                  Col.
                  apply perp2_sym.
                  auto.
                  apply perp2_sym.
                  auto.
                apply l6_6.
                auto.
              apply l6_6.
              auto.
            apply (anga_conga_anga n B' O N); auto.
            apply conga_right_comm.
            auto.
          apply(perp_col _ N').
            auto.
            apply (cop_per2__perp); auto.
              intro.
              subst N'.
              unfold Out in H95.
              tauto.
              intro.
              subst A'.
              contradiction.
            induction(eq_dec_points N' B).
              subst N'.
              right.
              intro.
              subst A'.
              contradiction.
            left.
            auto.
            apply coplanar_perm_16.
            apply col_cop__cop with N; Col.
            apply coplanar_perm_5.
            apply col_cop__cop with B'; Col.
            exists A.
            right.
            left.
            split; Col.
          apply out_col in H95.
          Col.
        apply False_ind.
        apply H93.
        Col.
      split; intro; apply H; ColR.
      split; intro; apply H; ColR.
Qed.

End Pappus_Pascal.

(** lcos_lcos_col -> lcos2_cop__col
    per_per_perp -> cop_per2__perp *)

Section Pappus_Pascal_2.

Context `{T2D:Tarski_2D}.
Context `{TE:@Tarski_euclidean Tn TnEQD}.

Lemma par__perp2 : forall A B C D P, Par A B C D -> Perp2 A B C D P.
Proof.
    intros.
    apply par_distincts in H.
    spliter.
    unfold Perp2.
    assert(HH:= perp_exists P A B H0).
    ex_and HH Q.
    exists P.
    exists Q.
    repeat split.
      Col.
      Perp.
    apply perp_sym.
    apply (par_perp__perp A B); auto.
    apply perp_sym; auto.
Qed.

Lemma l13_11 : forall A B C A' B' C' O,
  ~ Col O A A' ->
  B <> O -> C <> O ->
  Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Par B C' C B' -> Par C A' A C' ->
  Par A B' B A'.
Proof.
    intros.
    assert(HH:=par__perp2 B C' C B' O H8).
    assert(HP:=par__perp2 C A' A C' O H9).
    assert(HQ:=perp2_par A B' B A' O).
    apply HQ.
    apply(l13_10 A B C A' B' C' O); auto.
Qed.


Lemma l13_14 : forall O A B C O' A' B' C',
  Par_strict O A O' A' -> Col O A B -> Col O B C -> Col O A C ->
  Col O' A' B' -> Col O' B' C' -> Col O' A' C' ->
  Par A C' A' C -> Par B C' B' C -> Par A B' A' B.
Proof.
    intros.
    assert(HP:= H).
    unfold Par_strict in HP.
    spliter.
    assert(~Col O A A').
      intro.
      apply H11.
      exists A'.
      split; Col.
    induction(eq_dec_points A C).
      subst C.
      induction H6.
        apply False_ind.
        apply H6.
        exists A.
        split; Col.
      spliter.
      assert(A' =  C').
        eapply (l6_21 A C' O' A'); Col.
        intro.
        apply H11.
        exists A.
        split.
          Col.
        eapply (col_transitivity_1 _ C').
          intro.
          subst C'.
          apply H11.
          exists A.
          Col.
          Col.
        Col.
      subst C'.
      Par.
    assert(A' <> C').
      intro.
      subst C'.
      induction H6.
        apply H6.
        exists A'.
        split; Col.
      spliter.
      apply H13.
      eapply (l6_21 A A' O A); Col.
    assert(Par_strict A C A' C').
      unfold Par_strict.
      repeat split; auto; try apply all_coplanar.
      intro.
      apply H11.
      ex_and H15 X.
      exists X.
      split.
        ColR.
      ColR.
    assert(Plg A C A' C').
      apply(pars_par_plg A C A' C').
        auto.
      apply par_right_comm.
      auto.
    induction(eq_dec_points B C).
      subst C.
      assert(B' = C').
        eapply (l6_21 B C' A' C').
          intro.
          apply H11.
          exists B.
          split.
            Col.
          ColR.
          auto.
          induction H7.
            apply False_ind.
            apply H7.
            exists B.
            split; Col.
          spliter.
          Col.
          Col.
          ColR.
          Col.
      subst.
      Par.
    assert(B' <> C').
      intro.
      subst C'.
      induction H7.
        apply H7.
        exists B'.
        split; Col.
      spliter.
      apply H17.
      eapply (l6_21 A C B' B).
        intro.
        induction H6.
          apply H6.
          exists C.
          split; Col.
        spliter.
        apply H15.
        exists B'.
        split; Col.
        auto.
        ColR.
        Col.
        Col.
        Col.
    assert(Par_strict B C B' C').
      unfold Par_strict.
      repeat split; auto; try apply all_coplanar.
      intro.
      apply H11.
      ex_and H19 X.
      exists X.
      split.
        assert(Col X O B).
          ColR.
        induction(eq_dec_points O B).
          subst O.
          ColR.
        ColR.
      assert(Col X O' B').
        ColR.
      induction(eq_dec_points O' B').
        subst O'.
        ColR.
      ColR.
    assert(Plg B C B' C').
      apply(pars_par_plg B C B' C').
        auto.
      apply par_right_comm.
      auto.
    assert(Parallelogram A C A' C').
      apply plg_to_parallelogram.
      auto.
    assert(Parallelogram B C B' C').
      apply plg_to_parallelogram.
      auto.
    apply plg_mid in H21.
    apply plg_mid in H22.
    ex_and H21 M.
    ex_and H22 N.
    assert(M = N).
      eapply (l7_17 C C'); auto.
    subst N.
    assert(Parallelogram A B A' B').
      apply(mid_plg A B A' B' M).
        left.
        intro.
        subst A'.
        apply H12.
        Col.
        assumption.
      assumption.
    apply par_right_comm.
    induction(eq_dec_points A B).
      subst B.
      assert(B' = A').
        eapply (symmetric_point_uniqueness A M); auto.
      subst B'.
      apply par_reflexivity.
      intro.
      subst A'.
      apply H12.
      Col.
    apply plg_par; auto.
    intro.
    subst A'.
    apply H11.
    exists B.
    split; Col.
Qed.

End Pappus_Pascal_2.