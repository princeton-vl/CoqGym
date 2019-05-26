 (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_2_length.

Section Angles_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(************************************* angle *****************************)

Lemma ang_exists : forall A B C, A <> B -> C <> B -> exists a, Q_CongA a /\ a A B C.
Proof.
    intros.
    exists (fun D E F => CongA A B C D E F).
    split.
      unfold Q_CongA.
      exists A.
      exists B.
      exists C.
      split; auto.
      split; auto.
      intros.
      split.
        auto.
      auto.
    apply conga_refl; auto.
Qed.

Lemma ex_points_ang : forall a , Q_CongA a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    unfold Q_CongA in H.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:= H1 A B C).
    destruct HH.
    exists A.
    exists B.
    exists C.
    apply H2.
    apply conga_refl; auto.
Qed.

End Angles_1.

Ltac ang_instance a A B C :=
  assert(tempo_ang:= ex_points_ang a);
  match goal with
    |H: Q_CongA a |-  _ => assert(tempo_H:=H); apply tempo_ang in tempo_H;
                       elim tempo_H; intros A ; let tempo_HP := fresh "tempo_HP" in intro tempo_HP; clear tempo_H;
                       elim tempo_HP; intro B; let tempo_HQ := fresh "tempo_HQ" in intro tempo_HQ ; clear tempo_HP ;
                       elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_ang.

Section Angles_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ang_conga : forall a A B C A' B' C', Q_CongA a -> a A B C -> a A' B' C' -> CongA A B C A' B' C'.
Proof.
    intros.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:=H3 A B C).
    assert(HH1:= H3 A' B' C').
    destruct HH.
    destruct HH1.
    apply H5 in H0.
    apply H7 in H1.
    eapply conga_trans.
      apply conga_sym.
      apply H0.
    auto.
Qed.

Lemma is_ang_conga : forall A B C A' B' C' a, Ang A B C a -> Ang A' B' C' a -> CongA A B C A' B' C'.
Proof.
    intros.
    unfold Ang in *.
    spliter.
    eapply (ang_conga a); auto.
Qed.

Lemma is_ang_conga_is_ang : forall A B C A' B' C' a, Ang A B C a -> CongA A B C A' B' C' -> Ang A' B' C' a.
Proof.
    intros.
    unfold Ang in *.
    spliter.
    split.
      auto.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_not_ang : forall A B C A' B' C' a , Q_CongA a -> ~(CongA A B C A' B' C') -> a A B C -> ~(a A' B' C').
Proof.
    intros.
    intro.
    assert(HH:=ang_conga a A B C A' B' C' H H1 H2).
    contradiction.
Qed.

Lemma not_conga_is_ang : forall A B C A' B' C' a , ~(CongA A B C A' B' C') -> Ang A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold Ang in H0.
    spliter.
    intro.
    apply H.
    apply (ang_conga a); auto.
Qed.

Lemma not_cong_is_ang1 : forall A B C A' B' C' a , ~(CongA A B C A' B' C') -> Ang A B C a -> ~(Ang A' B' C' a).
Proof.
    intros.
    intro.
    unfold Ang in *.
    spliter.
    apply H.
    apply (ang_conga a); auto.
Qed.

Lemma ex_eqa : forall a1 a2, (exists A , exists B, exists C, Ang A B C a1 /\ Ang A B C a2)  -> EqA a1 a2.
Proof.
    intros.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:=H).
    assert(HH0:=H0).
    unfold Ang in HH.
    unfold Ang in HH0.
    spliter.
    unfold EqA.
    repeat split; auto; intro.
      assert(CongA A B C A0 B0 C0).
        eapply (is_ang_conga _ _ _ _ _ _ a1); auto.
        split; auto.
      assert(Ang A0 B0 C0 a2).
        apply (is_ang_conga_is_ang A B C); auto.
      unfold Ang in H7.
      tauto.
    assert(CongA A B C A0 B0 C0).
      eapply (is_ang_conga _ _ _ _ _ _ a2); auto.
      split; auto.
    assert(Ang A0 B0 C0 a1).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold Ang in H7.
    tauto.
Qed.

Lemma all_eqa : forall A B C a1 a2, Ang A B C a1 -> Ang A B C a2 -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_ang_distinct : forall A B C a , Ang A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    unfold Ang in H.
    spliter.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    unfold CongA in H0.
    spliter.
    tauto.
Qed.


Lemma null_ang : forall A B C D a1 a2, Ang A B A a1 -> Ang C D C a2 -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B A).
      apply H.
    eapply (is_ang_conga_is_ang C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_ang_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_ang_distinct in H.
    tauto.
Qed.

Lemma flat_ang : forall A B C A' B' C' a1 a2, Bet A B C -> Bet A' B' C' -> Ang A B C a1 -> Ang A' B' C' a2  -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B C).
      apply H1.
    eapply (is_ang_conga_is_ang A' B' C').
      apply H2.
    apply is_ang_distinct in H1.
    apply is_ang_distinct in H2.
    spliter.
    eapply conga_line; auto.
Qed.

Lemma ang_distinct: forall a A B C, Q_CongA a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(Ang A B C a).
      split; auto.
    apply (is_ang_distinct _ _ _ a); auto.
Qed.

Lemma ex_ang : forall A B C, B <> A -> B <> C -> exists a, Q_CongA a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => CongA A B C X Y Z).
    unfold Q_CongA.
    split.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      split.
        auto.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

(************************************* Acute angle *****************************************)

Lemma anga_exists : forall A B C, A <> B -> C <> B -> Acute A B C -> exists a, Q_CongA_Acute a /\ a A B C.
Proof.
    intros.
    exists (fun D E F => CongA A B C D E F).
    split.
      unfold Q_CongA.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      intros.
      split; auto.
    apply conga_refl; auto.
Qed.

Lemma anga_is_ang : forall a, Q_CongA_Acute a -> Q_CongA a.
Proof.
    intros.
    unfold Q_CongA_Acute in H.
    unfold Q_CongA.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    apply acute_distincts in H.
    spliter.
    split.
      auto.
    split.
      auto.
    intros.
    split.
      intro.
      assert(Ang X Y Z a).
        unfold Ang.
        split.
          unfold Q_CongA.
          exists A.
          exists B.
          exists C.
          split.
            assumption.
          split.
            assumption.
          auto.
        assert(HH:= H0 X Y Z).
        apply HH.
        auto.
      unfold Ang in H3.
      spliter.
      auto.
    intro.
    apply H0.
    auto.
Qed.

Lemma ex_points_anga : forall a , Q_CongA_Acute a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    assert(HH:=H).
    apply anga_is_ang in H.
    ang_instance a A B C.
    exists A.
    exists B.
    exists C.
    assumption.
Qed.

End Angles_2.

Ltac anga_instance a A B C :=
  assert(tempo_anga:= ex_points_anga a);
  match goal with
    |H: Q_CongA_Acute a |-  _ => assert(tempo_H:=H); apply tempo_anga in tempo_H;
                                 elim tempo_H; intros A ;
                                 let tempo_HP := fresh "tempo_HP" in
                                 intro tempo_HP; clear tempo_H;
                                 elim tempo_HP; intro B;
                                 let tempo_HQ := fresh "tempo_HQ" in
                                 intro tempo_HQ ; clear tempo_HP ;
                        elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_anga.

Require Import Setoid.

Section Angles_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma anga_conga : forall a A B C A' B' C', Q_CongA_Acute a -> a A B C -> a A' B' C' -> CongA A B C A' B' C'.
Proof.
    intros.
    apply (ang_conga a); auto.
    apply anga_is_ang.
    auto.
Qed.

Lemma is_anga_to_is_ang : forall A B C a, Ang_Acute A B C a -> Ang A B C a.
Proof.
    intros.
    unfold Ang_Acute in H.
    unfold Ang.
    spliter.
    split.
      apply anga_is_ang.
      auto.
    auto.
Qed.

Lemma is_anga_conga : forall A B C A' B' C' a, Ang_Acute A B C a -> Ang_Acute A' B' C' a -> CongA A B C A' B' C'.
Proof.
    intros.
    unfold Ang_Acute in *.
    spliter.
    apply (anga_conga a); auto.
Qed.

Lemma is_anga_conga_is_anga : forall A B C A' B' C' a, Ang_Acute A B C a -> CongA A B C A' B' C' -> Ang_Acute A' B' C' a.
Proof.
    intros.
    unfold Ang_Acute in *.
    spliter.
    split.
      auto.
    apply anga_is_ang in H.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_is_anga : forall A B C A' B' C' a , ~ CongA A B C A' B' C' -> Ang_Acute A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold Ang_Acute in H0.
    spliter.
    intro.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma not_cong_is_anga1 : forall A B C A' B' C' a , ~ CongA A B C A' B' C' -> Ang_Acute A B C a -> ~ Ang_Acute A' B' C' a.
Proof.
    intros.
    intro.
    unfold Ang_Acute in *.
    spliter.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma ex_eqaa : forall a1 a2, (exists A , exists B, exists C, Ang_Acute A B C a1 /\ Ang_Acute A B C a2)  -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    split; apply is_anga_to_is_ang; auto.
Qed.

Lemma all_eqaa : forall A B C a1 a2, Ang_Acute A B C a1 -> Ang_Acute A B C a2 -> EqA a1 a2.
Proof.
    intros.
    apply ex_eqaa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_anga_distinct : forall A B C a , Ang_Acute A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    apply (is_ang_distinct A B C a).
    apply is_anga_to_is_ang.
    auto.
Qed.

Global Instance eqA_equivalence : Equivalence EqA.
Proof.
split.
unfold Reflexive.
intros.
unfold EqA.
intros;tauto.
unfold Symmetric, EqA.
intros.
firstorder.
unfold Transitive, EqA.
intros.
rewrite H.
apply H0.
Qed.

Lemma null_anga : forall A B C D a1 a2, Ang_Acute A B A a1 -> Ang_Acute C D C a2 -> EqA a1 a2.
Proof.
    intros.
    eapply (all_eqaa A B A).
      apply H.
    eapply (is_anga_conga_is_anga C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_anga_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_anga_distinct in H.
    tauto.
Qed.

Lemma anga_distinct: forall a A B C, Q_CongA_Acute a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(Ang_Acute A B C a).
      split; auto.
    apply (is_anga_distinct _ _ _ a); auto.
Qed.

Lemma out_is_len_eq : forall A B C l, Out A B C -> Len A B l -> Len A C l -> B = C.
Proof.
    intros.
    assert(Cong A B A C).
      apply (is_len_cong _ _ _ _ l); auto.
    assert(A <> C).
      unfold Out in H.
      spliter.
      auto.
    eapply (l6_11_uniqueness A A C C ); Cong.
    apply out_trivial.
    auto.
Qed.

Lemma out_len_eq : forall A B C l, Q_Cong l -> Out A B C -> l A B -> l A C -> B = C.
Proof.
    intros.
    apply (out_is_len_eq A _ _ l).
      auto.
      split; auto.
    split; auto.
Qed.

Lemma ex_anga : forall A B C, Acute A B C -> exists a, Q_CongA_Acute a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => CongA A B C X Y Z).
    unfold Q_CongA_Acute.
    assert (HH := acute_distincts A B C H).
    spliter.
    split.
      exists A.
      exists B.
      exists C.
      split; auto.
      intros.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

Lemma not_null_ang_ang : forall a, Q_CongA_nNull a -> Q_CongA a.
Proof.
    intros.
    unfold Q_CongA_nNull  in H.
    spliter; auto.
Qed.

Lemma not_null_ang_def_equiv : forall a, Q_CongA_nNull a <-> (Q_CongA a /\ exists A, exists B, exists C, a A B C /\  ~Out B A C).
Proof.
    intros.
    split.
      intro.
      unfold Q_CongA_nNull in H.
      spliter.
      assert(HH:= H).
      unfold Q_CongA in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold Q_CongA_nNull.
    split; auto.
    intros.
    assert(CongA A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (l11_21_a A0 B0 C0); auto.
Qed.

Lemma not_flat_ang_def_equiv : forall a, Q_CongA_nFlat a <-> (Q_CongA a /\ exists A, exists B, exists C, a A B C /\  ~Bet A B C).
Proof.
    intros.
    split.
      intro.
      unfold Q_CongA_nFlat in H.
      spliter.
      assert(HH:= H).
      unfold Q_CongA in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold Q_CongA_nFlat.
    split; auto.
    intros.
    assert(CongA A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (bet_conga__bet A0 B0 C0); auto.
Qed.

Lemma ang_const : forall a A B, Q_CongA a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    apply(swap_diff) in H1.
    assert(HH:= H2 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H3.
      apply conga_refl; auto.
    assert(HH :=not_col_exists A B H0).
    ex_and HH P.
    induction(eq_dec_points A0 C0).
      subst C0.
      exists A.
      assert(HH:= (H2 A B A)).
      destruct HH.
      apply H7.
      apply conga_trivial_1; auto.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H H7 H1).
    ex_and HH C; auto.
    exists C.
    apply H2.
    auto.
Qed.

End Angles_3.

Ltac ang_instance1 a A B C :=
	assert(tempo_ang:= ang_const a A B);
        match goal with
           |H: Q_CongA a |-  _ => assert(tempo_H:= H);apply tempo_ang in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_ang.

Section Angles_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ang_sym : forall a A B C, Q_CongA a -> a A B C -> a C B A.
Proof.
    intros.
    unfold Q_CongA in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H2 C B A).
    destruct HH.
    apply H5.
    auto.
Qed.

Lemma ang_not_null_lg : forall a l A B C, Q_CongA a -> Q_Cong l -> a A B C -> l A B -> ~ Q_Cong_Null l.
Proof.
    intros.
    intro.
    unfold Q_CongA in H.
    unfold Q_Cong_Null in H3.
    spliter.
    unfold Q_Cong in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H6 A B C).
    destruct HH.
    assert(CongA A0 B0 C0 A B C).
      apply H8.
      auto.
    apply conga_distinct in H8.
      spliter.
      ex_and H0 A1.
      ex_and H14 B1.
      assert(HH:= H0 A B).
      destruct HH.
      ex_and H4 A'.
      assert(HH:= H0 A' A').
      destruct HH.
      assert(Cong A1 B1 A' A').
        apply H17.
        auto.
      assert(Cong A1 B1 A B).
        apply H15.
        auto.
      apply cong_identity in H17.
        subst B1.
        apply cong_symmetry in H19.
        apply cong_identity in H19.
        contradiction.
      auto.
    auto.
Qed.

Lemma ang_distincts : forall a A B C, Q_CongA a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= ang_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply ang_sym; auto.
    assert(HQ:= ang_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold Q_Cong_Null.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold Q_Cong_Null.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma anga_sym : forall a A B C, Q_CongA_Acute a -> a A B C -> a C B A.
Proof.
    intros.
    unfold Q_CongA_Acute in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H1 A B C).
    destruct HH.
    apply H3 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H1 C B A).
    destruct HH.
    apply H4.
    auto.
Qed.

Lemma anga_not_null_lg : forall a l A B C, Q_CongA_Acute a -> Q_Cong l -> a A B C -> l A B -> ~ Q_Cong_Null l.
Proof.
    intros.
    intro.
    unfold Q_CongA_Acute in H.
    unfold Q_Cong_Null in H3.
    spliter.
    unfold Q_Cong in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H5 A B C).
    destruct HH.
    assert(CongA A0 B0 C0 A B C).
      apply H7.
      auto.
    apply conga_distinct in H8.
    spliter.
    ex_and H0 A1.
    ex_and H13 B1.
    assert(HH:= H0 A B).
    destruct HH.
    ex_and H4 A'.
    assert(HH:= H0 A' A').
    destruct HH.
    assert(Cong A1 B1 A' A').
      apply H16.
      auto.
    assert(Cong A1 B1 A B).
      apply H14.
      auto.
    apply cong_identity in H17.
    subst B1.
    apply cong_symmetry in H18.
    apply cong_identity in H18.
    contradiction.
Qed.

Lemma anga_distincts : forall a A B C, Q_CongA_Acute a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= anga_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply anga_sym; auto.
    assert(HQ:= anga_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold Q_Cong_Null.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold Q_Cong_Null.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma ang_const_o : forall a A B P, ~Col A B P -> Q_CongA a -> Q_CongA_nNull a -> Q_CongA_nFlat a -> exists C, a A B C /\ OS A B C P.
Proof.
    intros.
    assert(HH:= H0).
    unfold Q_CongA in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    apply(swap_diff) in H4.
    assert(HH:= H5 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H6.
      apply conga_refl; auto.
    assert(HH:=ang_distincts a A0 B0 C0 H0 H8).
    assert(A0 <> C0).
      intro.
      subst C0.
      unfold Q_CongA_nNull in H1.
      spliter.
      assert(HH:=H11 A0 B0 A0 H8).
      apply HH.
      apply out_trivial; auto.
    spliter.
    assert(A <> B).
      intro.
      subst B.
      apply H.
      Col.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H10 H9 H4).
    ex_and HH C; auto.
    exists C.
    assert(a A B C).
      assert(HH:= H5 A B C).
      destruct HH.
      apply H15.
      auto.
    split.
      auto.
    induction H14.
      auto.
    unfold Q_CongA_nNull in H1.
    spliter.
    assert(HH:= H16 A B C H15).
    unfold Q_CongA_nFlat in H2.
    spliter.
    assert(Hh:=H17 A B C H15).
    apply False_ind.
    assert(HH0:=ang_distincts a A B C H0 H15).
    spliter.
    assert(HP:=or_bet_out A B C).
    induction HP.
      contradiction.
    induction H20.
      contradiction.
    contradiction.
Qed.

Lemma anga_const : forall a A B, Q_CongA_Acute a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    apply anga_is_ang in H.
    apply ang_const; auto.
Qed.

End Angles_4.

Ltac anga_instance1 a A B C :=
	assert(tempo_anga:= anga_const a A B);
        match goal with
           |H: Q_CongA_Acute a |-  _ => assert(tempo_H:= H); apply tempo_anga in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_anga.

Section Angles_5.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma null_anga_null_anga' : forall a, Q_CongA_Null_Acute a <-> is_null_anga' a.
Proof.
    intro.
    split.
      intro.
      unfold Q_CongA_Null_Acute in H.
      unfold is_null_anga'.
      spliter.
      split.
        auto.
      anga_instance a A B C.
      assert(HH:= H0 A B C H1).
      exists A.
      exists B.
      exists C.
      split; auto.
    intro.
    unfold is_null_anga' in H.
    unfold Q_CongA_Null_Acute.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    split; auto.
    intros.
    assert(CongA A B C A0 B0 C0).
      apply (anga_conga a); auto.
    apply (l11_21_a A B C); auto.
Qed.

Lemma is_null_anga_out : forall a A B C, Q_CongA_Acute a -> a A B C -> Q_CongA_Null_Acute a -> Out B A C.
Proof.
    intros.
    unfold Q_CongA_Null_Acute in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.


Lemma acute_not_bet : forall A B C, Acute A B C -> ~Bet A B C.
Proof.
    intros.
    unfold Acute in H.
    ex_and H A0.
    ex_and H0 B0.
    ex_and H C0.
    unfold LtA in H0.
    spliter.
    unfold LeA in H0.
    ex_and H0 P.
    unfold InAngle in H0.
    spliter.
    ex_and H5 X.
    intro.
    apply conga_distinct in H2.
    spliter.
    assert(A<>C) by (intro; Between).
    induction H6.
      subst X.
      apply H1.
      apply conga_line; auto.
    assert(Bet A0 B0 P).
      apply (bet_conga__bet A B C); auto.
    assert(Bet A0 B0 C0).
      unfold Out in H6.
      spliter.
      induction H15.
        eBetween.
      eBetween.
    apply H1.
    apply (conga_line A B C); auto.
Qed.

Lemma anga_acute : forall a A B C , Q_CongA_Acute a -> a A B C -> Acute A B C.
Proof.
    intros.
    unfold Q_CongA_Acute in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= acute_lea_acute A B C A0 B0 C0).
    apply HH.
      auto.
    unfold LeA.
    exists C0.
    split.
      unfold InAngle.
      apply acute_distincts in H.
      spliter.
      repeat split; auto.
      exists C0.
      split.
        Between.
      right.
      apply out_trivial.
      auto.
    assert(HP:= H1 A B C).
    destruct HP.
    apply conga_sym.
    apply H3.
    auto.
Qed.

Lemma not_null_not_col : forall a A B C, Q_CongA_Acute a -> ~ Q_CongA_Null_Acute a -> a A B C -> ~Col A B C.
Proof.
    intros.
    intro.
    apply H0.
    unfold Q_CongA_Null_Acute.
    split.
      auto.
    assert(Acute A B C).
      apply (anga_acute a); auto.
    intros.
    assert(Out B A C).
      apply acute_col__out; auto.
    assert(HH:= anga_conga a A B C A0 B0 C0 H H1 H4).
    apply (l11_21_a A B C); auto.
Qed.


Lemma ang_cong_ang : forall a A B C A' B' C', Q_CongA a -> a A B C -> CongA A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    assert(Ang A B C a).
      unfold Ang.
      split; auto.
    assert(Ang A' B' C' a).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold Ang in H3.
    tauto.
Qed.

Lemma is_null_ang_out : forall a A B C, Q_CongA a -> a A B C -> Q_CongA_Null a -> Out B A C.
Proof.
    intros.
    unfold Q_CongA_Null in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.

Lemma out_null_ang : forall a A B C, Q_CongA a -> a A B C -> Out B A C -> Q_CongA_Null a.
Proof.
    intros.
    unfold Q_CongA_Null.
    split.
      auto.
    intros.
    assert(HH:=l11_21_a A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma bet_flat_ang : forall a A B C, Q_CongA a -> a A B C -> Bet A B C -> Ang_Flat a.
Proof.
    intros.
    unfold Ang_Flat.
    split.
      auto.
    intros.
    assert(HH:=bet_conga__bet A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma out_null_anga : forall a A B C, Q_CongA_Acute a -> a A B C -> Out B A C -> Q_CongA_Null_Acute a.
Proof.
    intros.
    unfold Q_CongA_Null_Acute.
    split.
      auto.
    intros.
    assert(HH:=l11_21_a A B C A0 B0 C0 H1).
    apply HH.
    apply (anga_conga a); auto.
Qed.

Lemma anga_not_flat : forall a, Q_CongA_Acute a -> Q_CongA_nFlat a.
Proof.
    intros.
    unfold Q_CongA_nFlat.
    split.
      apply anga_is_ang in H.
      auto.
    intros.
    assert(HH:= anga_acute a A B C H H0).
    unfold Q_CongA_Acute in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HP:= H1 A B C).
    apply acute_not_bet.
    auto.
Qed.


Lemma anga_const_o : forall a A B P, ~Col A B P -> ~ Q_CongA_Null_Acute a -> Q_CongA_Acute a -> exists C, a A B C /\ OS A B C P.
Proof.
    intros.
    assert(Q_CongA a).
      apply anga_is_ang; auto.
    assert(Q_CongA_nNull a).
      unfold Q_CongA_nNull.
      split.
        auto.
      intros A' B' C' HP.
      intro.
      apply H0.
      eapply (out_null_anga a A' B' C'); auto.
    assert(Q_CongA_nFlat a).
      apply anga_not_flat.
      auto.
    assert(HH:= ang_const_o a A B P H H2 H3 H4).
    auto.
Qed.

Lemma anga_conga_anga : forall a A B C A' B' C' , Q_CongA_Acute a -> a A B C -> CongA A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    unfold Q_CongA_Acute in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH := H2 A B C).
    assert(HP := H2 A' B' C').
    destruct HH.
    destruct HP.
    apply H4 in H0.
    assert(CongA A0 B0 C0 A' B' C').
      eapply conga_trans.
        apply H0.
      apply H1.
    apply H5.
    auto.
Qed.

Lemma anga_out_anga : forall a A B C A' C', Q_CongA_Acute a -> a A B C -> Out B A A' -> Out B C C' -> a A' B C'.
Proof.
    intros.
    assert(HH:= H).
    unfold Q_CongA_Acute in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    assert(HP:= H4 A B C).
    destruct HP.
    assert(CongA A0 B0 C0 A B C).
      apply H6.
      auto.
    assert(HP:= anga_distincts a A B C H H0).
    spliter.
    assert(CongA A B C A' B C').
      apply (out_conga A B C A B C).
        apply conga_refl; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        auto.
      auto.
    assert(HH:= H4 A' B C').
    destruct HH.
    apply H11.
    apply (conga_trans _ _ _ A B C); auto.
Qed.

Lemma out_out_anga : forall a A B C A' B' C', Q_CongA_Acute a -> Out B A C -> Out B' A' C' -> a A B C -> a A' B' C'.
Proof.
    intros.
    assert(CongA A B C A' B' C').
      apply l11_21_b; auto.
    apply (anga_conga_anga a A B C); auto.
Qed.

Lemma is_null_all : forall a A B, A <> B -> Q_CongA_Null_Acute a -> a A B A.
Proof.
    intros.
    unfold Q_CongA_Null_Acute in H0.
    spliter.
    assert(HH:= H0).
    unfold Q_CongA_Acute in HH.
    ex_and HH A0.
    ex_and H2 B0.
    ex_and H3 C0.
    apply acute_distincts in H2.
    spliter.
    apply H3.
    assert (a A0 B0 C0).
      apply H3.
      apply conga_refl; auto.
    assert(HH:= (H1 A0 B0 C0 H5)).
    apply l11_21_b; auto.
    apply out_trivial.
    auto.
Qed.

Lemma anga_col_out : forall a A B C, Q_CongA_Acute a -> a A B C -> Col A B C -> Out B A C.
Proof.
    intros.
    assert(Acute A B C).
      apply (anga_acute a); auto.
    unfold Col in H1.
    induction H1.
      apply acute_not_bet in H2.
      contradiction.
    unfold Out.
    apply (anga_distinct a A B C) in H.
      spliter.
      repeat split; auto.
      induction H1.
        right.
        auto.
      left.
      Between.
    auto.
Qed.

Lemma ang_not_lg_null : forall a la lc A B C, Q_Cong la -> Q_Cong lc -> Q_CongA a ->
 la A B -> lc C B -> a A B C -> ~ Q_Cong_Null la /\ ~ Q_Cong_Null lc.
Proof.
    intros.
    assert(HH:=ang_distincts a A B C H1 H4).
    spliter.
    split.
      intro.
      unfold Q_Cong_Null in H7.
      spliter.
      ex_and H8 P.
      assert(HH:= lg_cong la A B P P H H2 H9).
      apply cong_identity in HH.
      contradiction.
    intro.
    unfold Q_Cong_Null in H7.
    spliter.
    ex_and H8 P.
    assert(HH:= lg_cong lc C B P P H0 H3 H9).
    apply cong_identity in HH.
    contradiction.
Qed.

Lemma anga_not_lg_null : forall a la lc A B C, Q_Cong la -> Q_Cong lc ->
 Q_CongA_Acute a -> la A B -> lc C B -> a A B C -> ~ Q_Cong_Null la /\ ~ Q_Cong_Null lc.
Proof.
    intros.
    apply anga_is_ang in H1.
    apply(ang_not_lg_null a la lc A B C); auto.
Qed.

Lemma anga_col_null : forall a A B C, Q_CongA_Acute a -> a A B C -> Col A B C -> Out B A C /\ Q_CongA_Null_Acute a.
Proof.
    intros.
    assert(HH:= anga_distincts a A B C H H0).
    spliter.
    assert(Out B A C).
      induction H1.
        assert(HP:=anga_acute a A B C H H0).
        assert(HH:=acute_not_bet A B C HP).
        contradiction.
      induction H1.
        unfold Out.
        repeat split; auto.
      unfold Out.
      repeat split; auto.
      left.
      Between.
    split.
      auto.
    apply (out_null_anga a A B C); auto.
Qed.

Lemma eqA_preserves_ang: forall a b, Q_CongA a -> EqA a b -> Q_CongA b.
Proof.
intros.
unfold Q_CongA in *.
decompose [ex and] H.
exists x. exists x0. exists x1.
split.
assumption.
split.
assumption.
intros.
rewrite H4.
unfold EqA in H0.
apply H0.
Qed.

Lemma eqA_preserves_anga : forall a b, Q_CongA_Acute a -> Q_CongA b -> EqA a b -> Q_CongA_Acute b.
Proof.
    intros.
    assert (Q_CongA a).
        apply eqA_preserves_ang with b;auto.
        symmetry;auto.
    unfold EqA in H1.
    anga_instance a A B C.

    assert(HH:= H1 A B C).
    destruct HH.
    unfold Q_CongA_Acute.
    exists A.
    exists B.
    exists C.
    split.
      unfold Q_CongA_Acute in H.
      ex_and H A'.
      ex_and H6 B'.
      ex_and H C'.
      assert(a A' B' C').
        assert(HP:= H6 A B C).
        destruct HP.
        assert(CongA A B C A' B' C') by (apply conga_sym;auto).
        assert(HP:=is_ang_conga_is_ang A B C A' B' C' a).
        assert(Ang A' B' C' a).
          apply HP.
            split; auto.
          auto.
        unfold Ang in H10.
        spliter.
        auto.
      apply (acute_lea_acute _ _ _ A' B' C').
        auto.
      unfold LeA.
      exists C'.
      split.
        assert (HH:= is_ang_distinct A' B' C' a).
        assert( A' <> B' /\ C' <> B').
          apply HH.
          split; auto.
        spliter.
        apply inangle3123; auto.
      eapply (is_ang_conga _ _ _ _ _ _ a).
        split; auto.
      split; auto.
    intros.
    split.
      intro.
      assert(HH:= H1 X Y Z).
      destruct HH.
      assert(Ang X Y Z a).
        eapply (is_ang_conga_is_ang A B C).
          split; auto.
        auto.
      unfold Ang in H9.
      spliter.
      auto.
    intro.
    assert(HH:= H1 X Y Z).
    destruct HH.
    assert(a X Y Z).
      auto.
    eapply (is_ang_conga _ _ _ _ _ _ a).
      split; auto.
    split; auto.
Qed.

End Angles_5.