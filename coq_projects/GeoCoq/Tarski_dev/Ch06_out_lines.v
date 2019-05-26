Require Export GeoCoq.Tarski_dev.Ch05_bet_le.

Ltac eCol := eauto with col.

Section T6_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma bet_out : forall A B C, B <> A -> Bet A B C -> Out A B C.
Proof.
    intros.
    unfold Out.
    repeat split; auto.
    intro; treat_equalities; auto.
Qed.

Lemma out_dec : forall P A B, Out P A B \/ ~ Out P A B.
Proof.
    intros.
    unfold Out.
    elim (bet_dec P A B);intro; elim (bet_dec P B A);intro; elim (eq_dec_points A P);intro; elim (eq_dec_points B P);intro; tauto.
Qed.

Lemma out_diff1 : forall A B C, Out A B C -> B <> A.
Proof.
    intros.
    unfold Out in H.
    spliter.
    assumption.
Qed.

Lemma out_diff2 : forall A B C, Out A B C -> C <> A.
Proof.
    intros.
    unfold Out in H.
    spliter.
    assumption.
Qed.

Lemma out_distinct : forall A B C, Out A B C -> B <> A /\ C <> A.
Proof.
    intros.
    split.
      eapply out_diff1;eauto.
    eapply out_diff2;eauto.
Qed.

Lemma out_col : forall A B C, Out A B C -> Col A B C.
Proof.
    intros.
    unfold Col.
    unfold Out in H.
    spliter.
    induction H1;Between.
Qed.

Lemma l6_2 : forall A B C P,  A<>P -> B<>P -> C<>P -> Bet A P C -> (Bet B P C <-> Out P A B).
Proof.
    intros.
    unfold Out.
    split.
      intros.
      repeat split; try assumption; eapply l5_2;eBetween.
    intro; spliter; induction H5; eBetween.
Qed.

Lemma bet_out__bet : forall A B C P, Bet A P C -> Out P A B -> Bet B P C.
Proof.
    intros A B C P HBet HOut.
    destruct (eq_dec_points C P).
      subst; Between.
    apply (l6_2 A); trivial; destruct HOut as [HPA [HPB]]; auto.
Qed.

Lemma l6_3_1 : forall A B P, Out P A B -> (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C).
Proof.
    unfold Out.
    intros.
    spliter.
    repeat split; try assumption.
    induction H1.
      assert(exists C, Bet A P C /\ P <> C) by (apply point_construction_different).
      ex_and H2 C.
      exists C.
      repeat split; eBetween.
    assert(exists C, Bet B P C /\ P <> C) by (apply point_construction_different).
    ex_and H2 C.
    exists C.
    repeat split;eBetween.
Qed.

Lemma l6_3_2 : forall A B P,
  (A<>P /\ B<>P /\ exists C, C<>P /\ Bet A P C /\ Bet B P C) -> Out P A B.
Proof.
    intros.
    spliter.
    ex_and H1 C.
    unfold Out.
    repeat split; try assumption; eapply l5_2; eBetween.
Qed.

Lemma l6_4_1 : forall A B P, Out P A B -> Col A P B /\ ~ Bet A P B.
Proof.
    unfold Out.
    intros.
    spliter.
    unfold Col.
    induction H1; split.
      Between.
      intro; apply H; eapply between_equality;eauto.
      right; left; assumption.
    intro; apply H0; eapply between_equality; eBetween.
Qed.

Lemma l6_4_2 : forall A B P, Col A P B /\ ~ Bet A P B -> Out P A B.
Proof.
    unfold Col.
    intros.
    spliter.
    unfold Out.
    induction H.
      contradiction.
    induction (eq_dec_points A P).
      subst P; intuition.
    induction (eq_dec_points B P).
      subst P; intuition.
    induction H; repeat split; Between.
Qed.

(** out reflexivity. l6_5 *)

Lemma out_trivial : forall P A, A<>P -> Out P A A.
Proof.
    intros.
    unfold Out.
    repeat split; Between.
Qed.

(** out symmetry. *)

Lemma l6_6 : forall P A B, Out P A B -> Out P B A.
Proof.
    unfold Out.
    intuition.
Qed.

(** out transitivity. *)

Lemma l6_7 : forall P A B C, Out P A B -> Out P B C -> Out P A C.
Proof.
    unfold Out.
    intros.
    spliter.
    repeat split; try assumption.
    induction H4; induction H2.
      left; eapply between_exchange4; eauto.
      eapply l5_3; eauto.
      eapply (l5_1 P B); auto.
    right; eBetween.
Qed.

Lemma bet_out_out_bet : forall A B C A' C',
 Bet A B C -> Out B A A' -> Out B C C' -> Bet A' B C'.
Proof.
    intros.
    unfold Out in *.
    spliter.
    induction H5; induction H3.
      assert(Bet A' B C) by (apply outer_transitivity_between2 with A; Between).
      apply outer_transitivity_between with C; auto.
      assert(Bet A' B C) by (apply outer_transitivity_between2 with A; Between).
      apply between_inner_transitivity with C; assumption.
      assert(Bet A' B C) by (apply between_exchange3 with A; Between).
      apply outer_transitivity_between with C; auto.
    assert(Bet A' B C) by (apply between_exchange3 with A; Between).
    eapply between_inner_transitivity with C; assumption.
Qed.

Lemma out2_bet_out : forall A B C X P,
 Out B A C -> Out B X P -> Bet A X C -> Out B A P /\ Out B C P.
Proof.
    intros.
    unfold Out in *.
    spliter.
    induction H5; induction H3.
      repeat split; try assumption.
        left; eapply between_exchange4 with X; try assumption.
        apply between_inner_transitivity with C; assumption.
      apply l5_1 with X; try auto.
      apply between_exchange2 with A; assumption.
      repeat split; try assumption.
        apply l5_3 with X; try assumption.
        apply between_inner_transitivity with C; assumption.
      right; apply between_exchange4 with X; try assumption.
      apply between_exchange2 with A; assumption.
      repeat split; try assumption.
        apply l5_1 with X; try auto.
        apply between_exchange2 with C; Between.
      left; apply between_exchange4 with X; try assumption.
      apply between_inner_transitivity with A; Between.
    repeat split; try assumption.
      right; apply between_exchange4 with X; try assumption.
      apply between_exchange2 with C; Between.
    apply l5_3 with X; try assumption.
    apply between_inner_transitivity with A; Between.
Qed.

Lemma l6_11_uniqueness : forall A B C R X Y,
  R<>A -> B<>C ->
  Out A X R -> Cong A X B C ->
  Out A Y R -> Cong A Y B C ->
  X=Y.
Proof.
    unfold Out.
    intros.
    spliter.
    assert (Cong A X A Y) by eCong.
    induction H8; induction H6.
      apply l4_19 with A R; try assumption.
      apply l4_3 with A A; Between; Cong.
      assert (Bet A X Y) by eBetween.
      eapply between_cong; eauto.
      assert (Bet A Y X) by eBetween.
      apply sym_equal; apply between_cong with A; Cong.
    assert (Bet A X Y \/ Bet A Y X) by (eapply l5_1; eauto).
    induction H10.
      apply between_cong with A; assumption.
    apply sym_equal; apply between_cong with A; Cong.
Qed.

Lemma l6_11_existence : forall A B C R,
  R<>A -> B<>C -> exists X, Out A X R /\ Cong A X B C.
Proof.
    intros.
    assert (exists X : Tpoint, (Bet A R X \/ Bet A X R) /\ Cong A X B C) by (apply (segment_construction_2);assumption).
    ex_and H1 X.
    exists X.
    unfold Out;repeat split; try intro;treat_equalities;intuition.
Qed.

Lemma segment_construction_3 : forall A B X Y, A <> B -> X <> Y -> exists C, Out A B C /\ Cong A C X Y.
Proof.
    intros.
    destruct (l6_11_existence A X Y B) as [C [HC1 HC2]]; auto.
    apply l6_6 in HC1.
    exists C; auto.
Qed.

Lemma l6_13_1 : forall P A B, Out P A B -> Le
 P A P B -> Bet P A B.
Proof.
    unfold Out.
    intros.
    spliter.
    induction H2; try assumption.
    unfold Le
 in H0.
    ex_and H0 Y.
    assert(Y = A).
      apply (l6_11_uniqueness P P A B); Between; Cong.
        unfold Out; repeat split; auto.
        intro; treat_equalities; auto.
      unfold Out; repeat split; auto.
    subst Y; assumption.
Qed.

Lemma l6_13_2 : forall P A B, Out P A B -> Bet P A B -> Le
 P A P B.
Proof.
    intros.
    unfold Le.
    exists A.
    split; Cong.
Qed.

Lemma l6_16_1 : forall P Q S X, P<>Q -> Col S P Q -> Col X P Q -> Col X P S.
Proof.
    intros.
    destruct (eq_dec_points S P).
      subst; Col.
    assert((Bet P S X \/ Bet P X S) -> (Bet P S X \/ Bet S X P)) by (intro; induction H3; Between).
    unfold Col.
    induction H0;induction H1.
      right; apply H3; eapply (l5_2 Q P); Between.
      induction H1; left; eBetween.
      induction H0; left; eBetween.
    induction H0; induction H1.
      right; apply H3; eapply l5_1; eauto.
      right; right; eBetween.
      right; left; eBetween.
    right; apply H3; eapply l5_3; eBetween.
Qed.

Lemma col_transitivity_1 : forall P Q A B,
  P<>Q -> Col P Q A -> Col P Q B -> Col P A B.
Proof.
    intros.
    induction (eq_dec_points A P).
      subst; unfold Col; Between.
    assert (T:=l6_16_1 P Q A B).
    apply col_permutation_1; apply T; Col.
Qed.

Lemma col_transitivity_2 : forall P Q A B,
 P<>Q -> Col P Q A -> Col P Q B -> Col Q A B.
Proof.
    intros.
    apply (col_transitivity_1 Q P A B);Col.
Qed.

(** Unicity of intersection *)

Lemma l6_21 : forall A B C D P Q,
  ~ Col A B C -> C<>D -> Col A B P -> Col A B Q -> Col C D P -> Col C D Q -> P=Q.
Proof.
    intros.
    elim (eq_dec_points P Q); intro; try assumption.
    cut False.
      intro; intuition.
    apply not_col_distincts in H.
    spliter.
    assert (Col C P Q) by (apply col_transitivity_1 with D; Col).
    assert (Col Q B C).
      induction (eq_dec_points Q A).
        subst; apply col_transitivity_1 with P; Col.
      apply col_transitivity_1 with P; try Col; apply col_permutation_1; apply col_transitivity_1 with A; Col.
    assert (Col A B C).
      induction (eq_dec_points Q A).
        subst Q; assumption.
      induction (eq_dec_points Q B).
        subst; apply col_permutation_2; apply col_transitivity_1 with P; try Col.
      apply col_permutation_2; apply col_transitivity_1 with Q; try Col.
    contradiction.
Qed.

End T6_1.

Hint Resolve col_transitivity_1 col_transitivity_2 out_col : col.

Section T6_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(* This is l6_25 of Tarski *)
Lemma not_col_exists : forall A B,
 A<>B -> exists C, ~ Col A B C.
Proof.
    intros.
    assert (T:=lower_dim_ex).
    induction T.
    induction H0.
    induction H0.
    induction (col_dec A B x).
      induction(col_dec A B x0).
        induction(col_dec A B x1).
          induction (eq_dec_points A x).
            assert (~(Col x x0 x1)) by (unfold Col; auto).
            treat_equalities; eCol.
          assert (Col A x x0)  by eCol.
          assert (Col A x x1)  by eCol.
          assert (Col A x0 x1) by eCol.
          assert (Col x x0 x1) by eCol.
          contradiction.
        exists x1; assumption.
      exists x0; assumption.
    exists x; assumption.
Qed.

(*
Lemma t2_8 : forall A B C D E : Tpoint,
 Bet A B C -> Bet D B E -> Cong A B D B -> Cong B C B E -> Cong A E C D.
Proof.
    intros.
    induction (eq_dec_points A B); try (treat_equalities; Cong).
    assert (Cong A B D B -> Cong B C B E -> Cong A D D A -> Cong B D B A -> Bet A B C -> Bet D B E -> A <> B -> Cong C D E A).
      apply five_segment.
    apply cong_symmetry.
    apply cong_right_commutativity.
    apply H4; Cong; Between.
Qed.
*)

Lemma col3 : forall X Y A B C,
 X <> Y ->
 Col X Y A -> Col X Y B -> Col X Y C ->
 Col A B C.
Proof.
    intros.
    assert (Col X A B) by (apply col_transitivity_1 with Y; assumption).
    induction(eq_dec_points C X).
      subst X; apply col_permutation_1; assumption.
    apply col_permutation_1.
    apply col_transitivity_1 with X; try assumption.
      apply col_permutation_2.
      apply col_transitivity_1 with Y; assumption.
    apply col_permutation_2.
    apply col_transitivity_1 with Y; assumption.
Qed.

Lemma colx : forall A B C X Y, A <> B -> Col X Y A -> Col X Y B -> Col A B C -> Col X Y C.
Proof.
    intros.
    destruct (eq_dec_points X Y).
      subst; Col.
    apply (col3 A B); auto; apply col_permutation_1.
      apply col_transitivity_1 with Y; Col.
      apply (col_transitivity_2 X); Col.
Qed.

Lemma out2__bet : forall A B C, Out A B C -> Out C A B -> Bet A B C.
Proof.
    intros A B C Hout1 Hout2.
    apply l6_4_1 in Hout2.
    destruct Hout2 as [_ Hout2].
    destruct Hout1 as [_ [_ [|]]].
    assumption.
    exfalso.
    apply Hout2.
    assumption.
Qed.

Lemma bet2_le2__le1346 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' -> Le
 A B A' B' -> Le
 B C B' C' ->
  Le
 A C A' C'.
Proof.
  intros A B C A' B' C' HBet HBet' HleAB HleBC.

  elim(eq_dec_points A B).
  { intro.
    subst B.
    apply (le_transitivity _ _ B' C'); auto.
    apply le_comm.
    exists B'.
    split; Between; Cong.
  }
  intro.
  elim(eq_dec_points B C).
  { intro.
    subst C.
    apply (le_transitivity _ _ A' B'); auto.
    exists B'; Cong.
  }
  intro.

  assert(A' <> B') by (intro; subst B'; assert(A = B); auto; apply (le_zero _ _ A'); auto).
  assert(B' <> C') by (intro; subst C'; assert(B = C); auto; apply (le_zero _ _ B'); auto).
  destruct HleAB as [B0 []].
  assert(A' <> B0) by (intro; subst B0; assert(A = B); auto; apply (cong_reverse_identity A'); Cong).
  assert(HC0 := segment_construction A' B0 B C).
  destruct HC0 as [C0 []].
  assert(B0 <> C0) by (intro; subst C0; assert(B = C); auto; apply (cong_reverse_identity B0); auto).
  exists C0.
  split.
  2: apply (l2_11 _ B _ _ B0); Cong.
  apply (outer_transitivity_between2 _ B0); auto.
  assert(Bet B0 B' C') by (apply between_symmetry; apply (between_inner_transitivity _ _ _ A'); Between).
  apply l6_13_1.
  - elim(eq_dec_points B0 B').
    { intro.
      subst.
      apply (l6_2 _ _ A'); Between.
    }
    intro.
    apply (l6_7 _ _ B').
    apply (l6_2 _ _ A'); Between.
    apply bet_out; auto.
  - apply (le_transitivity _ _ B' C').
      apply (l5_6 B C B' C'); Cong.
      apply le_comm.
      exists B'.
      split; Between; Cong.
Qed.

Lemma bet2_le2__le2356 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' ->
  Le A B A' B' -> Le A' C' A C -> Le B' C' B C.
Proof.
  intros A B C A' B' C' HBet HBet' HLe1 HLe2.
  elim(eq_dec_points A B).
  { intro; treat_equalities.
    apply (le_transitivity _ _ A' C'); auto.
    destruct (l5_12_a A' B' C'); auto.
  }
  intro.
  assert (A<>C) by (intro; treat_equalities; auto).
  destruct (l5_5_1 A B A' B' HLe1) as [B0 [HBet1 HCong1]].
  assert (A<>B0) by (intro; treat_equalities; auto).
  destruct HLe2 as [C0 [HBet2 HCong2]].
    assert (A<>C0) by (intro; treat_equalities; auto).
  assert (Bet A B0 C0).
  { apply l6_13_1.
      apply (l6_7 _ _ B); [|apply (l6_7 _ _ C)]; [apply l6_6| |apply l6_6]; apply bet_out; auto.
    apply (l5_6 A' B' A' C'); Cong.
    destruct (l5_12_a A' B' C'); auto.
  }
  apply (l5_6 B0 C0 B C); Cong; [apply (le_transitivity _ _ B C0)|].
    destruct (l5_12_a B B0 C0); eBetween.
    destruct (l5_12_a B C0 C); eBetween.
    apply cong_commutativity; apply (l4_3 _ _ A _ _ A'); Between; Cong.
Qed.

Lemma bet2_le2__le1245 : forall A B C A' B' C', Bet A B C -> Bet A' B' C' ->
  Le B C B' C' -> Le A' C' A C -> Le A' B' A B.
Proof.
  intros A B C A' B' C'; intros.
  apply le_comm.
  apply (bet2_le2__le2356 C _ _ C'); Le; Between.
Qed.

Lemma cong_preserves_bet : forall B A' A0 E D' D0,
  Bet B A' A0 -> Cong B A' E D' -> Cong B A0 E D0 -> Out E D' D0 ->
  Bet E D' D0.
Proof.
    intros.
    unfold Out in H2.
    spliter.
    induction H4.
      assumption.
    assert (Le
 E D0 E D').
      eapply l5_5_2.
      exists D'.
      split.
        assumption.
      Cong.
    assert(Le
 E D' E D0).
      eapply l5_6.
      repeat split.
        2:apply H0.
        2:apply H1.
      eapply l5_5_2.
      exists A0.
      split.
        assumption.
      Cong.
    assert(Cong E D' E D0).
      apply le_anti_symmetry.
        assumption.
      assumption.
    assert(D0 = D').
      eapply between_cong.
        apply H4.
      Cong.
    subst D'.
    Between.
Qed.

Lemma out_cong_cong : forall B A A0 E D D0,
 Out B A A0 -> Out E D D0 ->
 Cong B A E D -> Cong B A0 E D0 ->
 Cong A A0 D D0.
Proof.
    intros.
    unfold Out in H.
    spliter.
    induction H4.
      assert (Bet E D D0).
        eapply cong_preserves_bet.
          2:apply H1.
          2:apply H2.
          assumption.
        assumption.
      apply cong_commutativity.
      eapply l4_3.
        apply between_symmetry.
        apply H4.
        apply between_symmetry.
        apply H5.
        Cong.
      Cong.
    assert (Bet E D0 D).
      eapply cong_preserves_bet.
        2:apply H2.
        2:apply H1.
        assumption.
      apply l6_6.
      assumption.
    eapply l4_3;eBetween;Cong.
Qed.

Lemma not_out_bet : forall A B C, Col A B C -> ~ Out B A C -> Bet A B C.
Proof.
    intros.
    unfold Out in H0.
    induction (eq_dec_points A B).
      subst.
      Between.
    induction (eq_dec_points B C).
      subst.
      Between.
    unfold Col in *.
    decompose [or] H;clear H.
      assumption.
      exfalso.
      apply H0.
      intuition.
    exfalso.
    apply H0.
    intuition.
Qed.

Lemma or_bet_out : forall A B C, Bet A B C \/ Out B A C \/ ~Col A B C.
Proof.
    intros.
    destruct (col_dec A B C); auto.
    destruct (out_dec B A C); auto.
    left; apply not_out_bet; trivial.
Qed.

Lemma not_bet_out : forall A B C,
 Col A B C -> ~Bet A B C -> Out B A C.
Proof.
    intros.
    destruct (or_bet_out A B C) as [HBet|[HOut|HNCol]]; trivial; contradiction.
Qed.

Lemma not_bet_and_out :
 forall A B C,
 ~ (Bet A B C /\ Out B A C).
Proof.
    intros.
    intro.
    spliter.
    unfold Out in H0.
    spliter.
    induction H2.
      assert ( A = B).
        eapply between_equality.
          apply H.
        assumption.
      contradiction.
    assert(C = B).
      eapply between_equality.
        apply between_symmetry.
        apply H.
      assumption.
    contradiction.
Qed.

Lemma out_to_bet :
 forall A B C A' B' C',
  Col A' B' C' ->
 (Out B A C <-> Out B' A' C') ->
  Bet A B C ->
  Bet A' B' C'.
Proof.
    intros.
    induction(out_dec B A C).
      unfold Out in H2.
      spliter.
      induction H4.
        assert( A = B).
          eapply between_equality.
            apply H1.
          assumption.
        contradiction.
      assert(C = B).
        apply(between_symmetry) in H4.
        eapply between_equality.
          apply between_symmetry.
          apply H1.
        apply between_symmetry.
        assumption.
      contradiction.
    destruct H0.
    assert (~Out B' A' C').
      intro.
      apply H2.
      apply H3.
      assumption.
    apply not_out_bet.
      assumption.
    assumption.
Qed.

Lemma col_out2_col  : forall A B C AA CC, Col A B C -> Out B A AA -> Out B C CC -> Col AA B CC.
Proof.
    intros.
    induction H.
      assert (Bet AA B CC).
        eapply bet_out_out_bet.
          apply H.
          assumption.
        assumption.
      unfold Col.
      left.
      assumption.
    induction H.
      assert(Out B AA CC).
        eapply l6_7.
          eapply l6_6.
          apply H0.
        apply l6_6.
        eapply l6_7.
          apply l6_6.
          apply H1.
        apply bet_out.
          unfold Out in *.
          spliter.
          assumption.
          unfold Out in *.
          spliter.
          assumption.
      apply col_permutation_4.
      apply out_col.
      assumption.
    assert(Out B AA CC).
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H1.
      eapply l6_6.
      eapply l6_7.
        eapply l6_6.
        apply H0.
      apply bet_out.
        unfold Out in *.
        spliter.
        assumption.
        unfold Out in *.
        spliter.
      apply between_symmetry.
      assumption.
    apply col_permutation_4.
    apply out_col.
    assumption.
Qed.

Lemma bet2_out_out : forall A B C B' C', B <> A -> B' <> A -> Out A C C' -> Bet A B C -> Bet A B' C' -> Out A B B'.
Proof.
    intros.
    induction(eq_dec_points B' C').
      subst C'.
      unfold Out in *.
      spliter.
      repeat split; try assumption.
      induction H5.
        left.
        eapply between_exchange4.
          apply H2.
        assumption.
      eapply l5_3.
        apply H2.
      assumption.
    unfold Out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H6.
      assert(Bet A B C').
        eapply between_exchange4.
          apply H2.
        assumption.
      eapply l5_3.
        apply H7.
      assumption.
    assert(Bet B' C' C).
      eapply between_exchange3.
        apply H3.
      assumption.
    assert(Bet A B' C).
      eapply outer_transitivity_between.
        apply H3.
        assumption.
      assumption.
    eapply l5_3.
      apply H2.
    assumption.
Qed.

Lemma bet2__out : forall A B C B', A <> B -> A <> B' -> Bet A B C -> Bet A B' C -> Out A B B'.
Proof.
    intros.
    apply bet2_out_out with C C; auto.
    apply bet_neq12__neq in H1; auto.
    apply out_trivial; auto.
Qed.

Lemma out2_out_1 : forall B C D X,
 Out B X C -> Out B X D -> Out B C D.
Proof.
    intros.
    unfold Out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H2; induction H4.
      eapply l5_1.
        2: apply H4.
        auto.
      assumption.
      left.
      eapply between_exchange4.
        apply H4.
      assumption.
      right.
      eapply between_exchange4.
        apply H2.
      assumption.
    eapply l5_3.
      apply H4.
    apply H2.
Qed.

Lemma out2_out_2 : forall B C D X,
 Out B C X -> Out B D X -> Out B C D.
Proof.
    intros.
    eapply out2_out_1.
      apply l6_6.
      apply H.
    apply l6_6.
    assumption.
Qed.

Lemma out_bet_out_1 : forall A B C P,
 Out P A C -> Bet A B C -> Out P A B.
Proof.
    intros.
    induction (eq_dec_points B P).
      subst P.
      apply False_ind.
      apply (not_bet_and_out A B C).
      split; assumption.
    unfold Out in *.
    spliter.
    repeat split.
      assumption.
      assumption.
    induction H3.
      left.
      eapply between_inner_transitivity.
        apply H3.
      assumption.
    right.
    eapply between_exchange2.
      apply H3.
    apply between_symmetry.
    assumption.
Qed.

Lemma out_bet_out_2 : forall A B C P,
 Out P A C -> Bet A B C -> Out P B C.
Proof.
    intros.
    apply l6_6.
    eapply out_bet_out_1.
      apply l6_6.
      apply H.
    apply between_symmetry.
    assumption.
Qed.

Lemma out_bet__out : forall A B P Q,
 Bet P Q A -> Out Q A B -> Out P A B.
Proof.
    intros A B P Q HBet Hout.
    destruct Hout as [HAQ [HBQ [HQAB|HQBA]]]; [|apply l6_6];
      apply bet_out; eBetween; intro; treat_equalities; auto.
    apply HBQ; apply (between_equality _ _ A); Between.
Qed.

Lemma segment_reverse : forall A B C, Bet A B C -> exists B', Bet A B' C /\ Cong C B' A B.
Proof.
  intros.
  destruct (eq_dec_points A B).
    subst B; exists C; finish.
  destruct (segment_construction_3 C A A B) as [B' []]; auto.
    intro; treat_equalities; auto.
  exists B'; split; trivial.
  apply between_symmetry, (cong_preserves_bet A B C); Cong.
  apply l6_6; assumption.
Qed.

Lemma diff_col_ex : forall A B, exists C, A <> C /\ B <> C /\ Col A B C.
Proof.
    intros.
    assert (exists C, Bet A B C /\ B <> C).
      apply point_construction_different.
    ex_and H C.
    exists C.
    split.
      intro.
      induction (eq_dec_points A B).
        subst B.
        subst C.
        intuition.
      subst C.
      Between.
    assert_cols.
    auto.
Qed.

Lemma diff_bet_ex3 : forall A B C,
 Bet A B C ->
 exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    induction (eq_dec_points A B).
      induction (eq_dec_points B C).
        assert (exists D, Bet B C D /\ C <> D).
          apply point_construction_different.
        ex_and H2 D.
        exists D.
        repeat split.
          subst C.
          subst A.
          assumption.
          subst A.
          subst C.
          assumption.
          assumption.
        unfold Col.
        left.
        subst A.
        subst C.
        assumption.
      assert (exists D, Bet B C D /\ C <> D).
        apply point_construction_different.
      ex_and H2 D.
      exists D.
      repeat split.
        intro.
        subst D.
        apply between_symmetry in H.
        apply H1.
        eapply between_equality.
          apply H2.
        apply H.
        intro.
        subst D.
        subst A.
        apply between_identity in H2.
        apply H3.
        subst B.
        reflexivity.
        assumption.
      unfold Col.
      left.
      eapply outer_transitivity_between.
        apply H.
        apply H2.
      assumption.
    induction (eq_dec_points B C).
      subst C.
      cut(exists D : Tpoint, A <> D /\ B <> D /\ Col A B D).
        intro.
        ex_and H1 D.
        exists D.
        repeat split.
          assumption.
          assumption.
          assumption.
        assumption.
      apply diff_col_ex.
    assert (exists D, Bet B C D /\ C <> D).
      apply point_construction_different.
    ex_and H2 D.
    exists D.
    repeat split.
      intro.
      subst D.
      assert (B = C).
        eapply between_equality.
          apply H2.
        apply between_symmetry.
        assumption.
      apply H1.
      assumption.
      intro.
      subst D.
      apply between_identity in H2.
      subst C.
      apply H1.
      reflexivity.
      assumption.
    unfold Col.
    left.
    eapply outer_transitivity_between.
      apply H.
      assumption.
    assumption.
Qed.

Lemma diff_col_ex3 : forall A B C,
 Col A B C -> exists D, A <> D /\ B <> D /\ C <> D /\ Col A B D.
Proof.
    intros.
    assert(cas1 := diff_bet_ex3 A B C).
    assert(cas2 := diff_bet_ex3 B C A).
    assert(cas3 := diff_bet_ex3 C A B).
    unfold Col in H.
    induction H.
      apply (diff_bet_ex3 A B C).
      assumption.
    induction H.
      assert (HH:=H).
      induction (eq_dec_points B C).
        subst C.
        assert (exists C, A <> C /\ B <> C /\ Col A B C).
          apply (diff_col_ex).
        ex_and H0 D.
        exists D.
        repeat split; assumption.
      apply cas2 in HH.
      ex_and HH D.
      exists D.
      repeat split; try assumption.
      apply col_permutation_2.
      eapply col_transitivity_1.
        apply H0.
        assumption.
      unfold Col.
      left.
      assumption.
    induction (eq_dec_points A C).
      subst C.
      assert (exists C, A <> C /\ B <> C /\ Col A B C).
        apply (diff_col_ex).
      ex_and H0 D.
      exists D.
      repeat split; assumption.
    assert (HH:=H).
    apply cas3 in HH.
    ex_and HH D.
    exists D.
    repeat split; try assumption.
    apply col_permutation_5.
    eapply col_transitivity_1.
      apply H0.
      apply col_permutation_4.
      assumption.
    unfold Col.
    right;right.
    apply between_symmetry.
    assumption.
Qed.

End T6_2.

Hint Resolve bet_out out_trivial l6_6 : out.