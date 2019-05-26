 (* Gabriel Braun April 2013 *)
Require Export GeoCoq.Tarski_dev.Ch13_1.

Section Length_1.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** Pappus Desargues *)

(******************** length *********************)

Lemma lg_exists : forall A B, exists l, Q_Cong l /\ l A B.
Proof.
    intros.
    unfold Q_Cong.
    exists (fun x y => Cong A B x y).
    split.
      exists A.
      exists B.
      intros.
      split; auto.
    Cong.
Qed.


Lemma lg_cong : forall l A B C D, Q_Cong l -> l A B -> l C D -> Cong A B C D.
Proof.
    intros.
    unfold Q_Cong in H.
    ex_and H X.
    ex_and H2 Y.
    assert(HH:= H A B).
    destruct HH.
    assert(HH:= H C D).
    destruct HH.
    apply H3 in H0.
    apply H5 in H1.
    apply cong_transitivity with X Y; Cong.
Qed.

Lemma lg_cong_lg : forall l A B C D, Q_Cong l -> l A B -> Cong A B C D -> l C D.
Proof.
    intros.
    unfold Q_Cong in H.
    ex_and H A0.
    ex_and H2 B0.
    assert(HP:= H A B).
    assert(HQ:= H C D).
    destruct HP.
    destruct HQ.
    apply H4.
    eapply cong_transitivity.
      apply H3.
      assumption.
    assumption.
Qed.

Lemma lg_sym : forall l A B, Q_Cong l -> l A B -> l B A.
Proof.
    intros.
    apply (lg_cong_lg l A B); Cong.
Qed.

Lemma ex_points_lg : forall l, Q_Cong l -> exists A, exists B, l A B.
Proof.
    intros.
    unfold Q_Cong in H.
    ex_and H A.
    ex_and H0 B.
    assert(HH:= H A B).
    destruct HH.
    exists A.
    exists B.
    apply H0.
    Cong.
Qed.

End Length_1.

Ltac lg_instance l A B :=
  assert(tempo_sg:= ex_points_lg l);
  match goal with
    |H: Q_Cong l |-  _ => assert(tempo_H:=H); apply tempo_sg in tempo_H; elim tempo_H; intros A ; let tempoHP := fresh "tempo_HP" in intro tempoHP; clear tempo_H; elim tempoHP; intro B; intro; clear tempoHP
  end;
  clear tempo_sg.

Section Length_2.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma is_len_cong : forall A B C D l, Len A B l -> Len C D l -> Cong A B C D.
Proof.
    intros.
    unfold Len in *.
    spliter.
    eapply (lg_cong l); auto.
Qed.

Lemma is_len_cong_is_len : forall A B C D l, Len A B l -> Cong A B C D -> Len C D l.
Proof.
    intros.
    unfold Len in *.
    spliter.
    split.
      auto.
    unfold Q_Cong in H.
    ex_and H a.
    ex_and H2 b.
    assert(HH:= H A B).
    destruct HH.
    assert(HH1:= H C D).
    destruct HH1.
    apply H3 in H1.
    apply H4.
    apply cong_transitivity with A B; trivial.
Qed.

Lemma not_cong_is_len : forall A B C D l , ~(Cong A B C D) -> Len A B l -> ~(l C D).
Proof.
    intros.
    unfold Len in H0.
    spliter.
    intro.
    apply H.
    apply (lg_cong l); auto.
Qed.

Lemma not_cong_is_len1 : forall A B C D l , ~Cong A B C D -> Len A B l -> ~ Len C D l.
Proof.
    intros.
    intro.
    unfold Len in *.
    spliter.
    apply H.
    apply (lg_cong l); auto.
Qed.

Lemma lg_null_instance : forall l A, Q_Cong_Null l -> l A A.
Proof.
    intros.
    unfold Q_Cong_Null in H.
    spliter.
    unfold Q_Cong in H.
    ex_and H X.
    ex_and H1 Y.
    assert(HH:= H A A).
    destruct HH.
    ex_and H0 P.
    assert(HH:=(H P P)).
    destruct HH.
    apply H4 in H3.
    apply H1.
    apply cong_symmetry in  H3.
    apply cong_reverse_identity in H3.
    subst Y.
    apply cong_trivial_identity.
Qed.

Lemma lg_null_trivial : forall l A, Q_Cong l -> l A A -> Q_Cong_Null l.
Proof.
    intros.
    unfold Q_Cong_Null.
    split.
      auto.
    exists A.
    auto.
Qed.

Lemma lg_null_dec : forall l, Q_Cong l -> Q_Cong_Null l \/ ~ Q_Cong_Null l.
Proof.
    intros.
    assert(HH:=H).
    unfold Q_Cong in H.
    ex_and H A.
    ex_and H0 B.
    induction(eq_dec_points A B).
      subst B.
      left.
      unfold Q_Cong_Null.
      split.
        auto.
      exists A.
      apply H.
      Cong.
    right.
    intro.
    unfold Q_Cong_Null in H1.
    spliter.
    ex_and H2 P.
    apply H0.
    assert(Cong A B P P).
      apply H; auto.
    apply cong_identity in H2.
    auto.
Qed.

Lemma ex_point_lg : forall l A, Q_Cong l -> exists B, l A B.
Proof.
    intros.
    induction(lg_null_dec l).
      exists A.
      apply lg_null_instance.
      auto.
      assert(HH:= H).
      unfold Q_Cong in HH.
      ex_and HH X.
      ex_and H1 Y.
      assert(HH:= another_point A).
      ex_and HH P.
      assert(HP:= H2 X Y).
      destruct HP.
      assert(l X Y).
        apply H3.
        apply cong_reflexivity.
      assert(X <> Y).
        intro.
        subst Y.
        apply H0.
        unfold Q_Cong_Null.
        split.
          auto.
        exists X.
        auto.
      assert(HH:= segment_construction_3 A P X Y H1 H6).
      ex_and HH B.
      exists B.
      assert(HH:= H2 A B).
      destruct HH.
      apply H9.
      Cong.
    auto.
Qed.




Lemma ex_point_lg_out : forall l A P, A <> P -> Q_Cong l -> ~ Q_Cong_Null l -> exists B, l A B /\ Out A B P.
Proof.
    intros.
    assert(HH:= H0).
    unfold Q_Cong in HH.
    ex_and HH X.
    ex_and H2 Y.
    assert(HP:= H3 X Y).
    destruct HP.
    assert(l X Y).
      apply H2.
      apply cong_reflexivity.
    assert(X <> Y).
      intro.
      subst Y.
      apply H1.
      unfold Q_Cong_Null.
      split.
        auto.
      exists X.
      auto.
    assert(HH:= segment_construction_3 A P X Y H H6).
    ex_and HH B.
    exists B.
    split.
      assert(HH:= H3 A B).
      destruct HH.
      apply H9.
      Cong.
    apply l6_6.
    auto.
Qed.

Lemma ex_point_lg_bet : forall l A M, Q_Cong l -> exists B : Tpoint, l M B /\ Bet A M B.
Proof.
    intros.
    assert(HH:= H).
    unfold Q_Cong in HH.
    ex_and HH X.
    ex_and H0 Y.
    assert(HP:= H1 X Y).
    destruct HP.
    assert(l X Y).
      apply H0.
      apply cong_reflexivity.
    prolong A M B X Y.
    exists B.
    split; auto.
    eapply (lg_cong_lg l X Y); Cong.
Qed.

End Length_2.

Ltac lg_instance1 l A B :=
  assert(tempo_sg:= ex_point_lg l);
  match goal with
    |H: Q_Cong l |-  _ => assert(tempo_H:=H); apply (tempo_sg A) in tempo_H; ex_elim tempo_H B; exists B
  end;
  clear tempo_sg.

(* TODO : translate this kind of notations *)
Tactic Notation "soit" ident(A) ident(B) "de" "longueur" ident(l) := lg_instance1 l A B.

Ltac lg_instance2 l A P B :=
  assert(tempo_sg:= ex_point_lg_out l);
  match goal with
    |H: A <> P |-  _ =>
                        match goal with
                           |HP : Q_Cong l |-  _ =>
                                               match goal with
                                                 |HQ : ~ Q_Cong_Null l |-  _ => assert(tempo_HQ:=HQ);
                                                                           apply (tempo_sg A P H HP) in tempo_HQ;
                                                                           ex_and tempo_HQ B
                                               end
                        end
  end;
  clear tempo_sg.


Tactic Notation "soit" ident(B) "sur" "la" "demie" "droite" ident(A) ident(P) "/" "longueur" ident(A) ident(B) "=" ident(l) := lg_instance2 l A P B.

Section Length_3.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma ex_points_lg_not_col : forall l P, Q_Cong l -> ~ Q_Cong_Null l -> exists A, exists B, l A B /\ ~Col A B P.
Proof.
    intros.
    assert(HH:=another_point P).
    ex_elim HH A.
    assert(HH:= not_col_exists P A H1).
    ex_elim HH Q.
    exists A.
    assert(A <> Q).
      intro.
      subst Q.
      apply H2.
      Col.
    lg_instance2 l A Q B.
    exists B.
    split.
      auto.
    intro.
    apply H2.
    assert(A <> B).
      intro.
      subst B.
      unfold Out in H5.
      tauto; apply out_col in H5.
    apply out_col in H5.
    ColR.
Qed.

End Length_3.

Ltac lg_instance_not_col l P A B :=
  assert(tempo_sg:= ex_points_lg_not_col l P);
  match goal with
        |HP : Q_Cong l |-  _ => match goal with
                                  |HQ : ~ Q_Cong_Null l |-  _ => assert(tempo_HQ:=HQ);
                                                            apply (tempo_sg HP) in tempo_HQ;
                                                            elim tempo_HQ;
                                                            intro A;
                                                            let tempo_HR := fresh "tempo_HR" in
                                                            intro tempo_HR;
                                                            elim tempo_HR;
                                                            intro B;
                                                            intro;
                                                            spliter;
                                                            clear tempo_HR tempo_HQ
                            end
  end;
  clear tempo_sg.



Tactic Notation "soit" ident(B) "sur" "la" "demie" "droite" ident(A) ident(P) "/" "longueur" ident(A) ident(B) "=" ident(l) := lg_instance2 l A P B.

Require Import Setoid.

Section Length_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Notation "l1 =l= l2" := (EqL l1 l2) (at level 80, right associativity).

Lemma ex_eql : forall l1 l2, (exists A , exists B, Len A B l1 /\ Len A B l2)  -> l1 =l= l2.
Proof.
    intros.
    ex_and H A.
    ex_and H0 B.
    assert(HH:=H).
    assert(HH0:=H0).
    unfold Len in HH.
    unfold Len in HH0.
    spliter.
    unfold EqL.
    repeat split; auto.
      intro.
      assert(Len A0 B0 l1).
        unfold Len.
        split; auto.
      assert(Cong A B A0 B0).
        apply (is_len_cong _ _ _ _ l1); auto.
      assert(Len A0 B0 l2).
        apply(is_len_cong_is_len A B).
          apply H0.
        auto.
      unfold Len in H8.
      spliter.
      auto.
    intro.
    assert(Len A0 B0 l2).
      unfold Len.
      split; auto.
    assert(Cong A B A0 B0).
      apply (is_len_cong _ _ _ _ l2); auto.
    assert(Len A0 B0 l1).
      apply(is_len_cong_is_len A B).
        apply H.
      auto.
    unfold Len in H8.
    spliter.
    auto.
Qed.


Lemma all_eql : forall A B l1 l2, Len A B l1 -> Len A B l2 -> EqL l1 l2.
Proof.
    intros.
    apply ex_eql.
    exists A.
    exists B.
    split; auto.
Qed.



Lemma null_len : forall A B la lb, Len A A la -> Len B B lb -> EqL la lb.
Proof.
    intros.
    eapply (all_eql A A).
      apply H.
    eapply (is_len_cong_is_len B B); Cong.
Qed.

Global Instance eqL_equivalence : Equivalence EqL.
Proof.
split.
- unfold Reflexive.
  intros.
  unfold EqL.
  intros.
  tauto.
- unfold Symmetric.
  intros.
  unfold EqL in *.
  firstorder.
- unfold Transitive.
  unfold EqL.
  intros.
  rewrite H.
  apply H0.
Qed.


Lemma ex_lg : forall A B, exists l, Q_Cong l /\ l A B.
Proof.
    intros.
    exists (fun C D => Cong A B C D).
    unfold Q_Cong.
    split.
      exists A. exists B.
      tauto.
    Cong.
Qed.

Lemma lg_eql_lg : forall l1 l2, Q_Cong l1 -> EqL l1 l2 -> Q_Cong l2.
Proof.
    intros.
    unfold EqL in *.
    unfold Q_Cong in *.
    decompose [ex] H.
    exists x. exists x0.
    intros.
    rewrite H2.
    apply H0.
Qed.

Lemma ex_eqL : forall l1 l2, Q_Cong l1 -> Q_Cong l2 -> (exists A, exists B, l1 A B /\ l2 A B) -> EqL l1 l2.
Proof.
intros.
ex_and H1 A.
ex_and H2 B.
unfold EqL.
assert(HH1:= H).
assert(HH2:= H0).

unfold Q_Cong in HH1.
unfold Q_Cong in HH2.
ex_and HH1 A1.
ex_and H3 B1.
ex_and HH2 A2.
ex_and H3 B2.

repeat split; auto.
intro.
assert(HH:= H4 A0 B0).
assert(HP:= H5 A0 B0).
destruct HP.
apply H6.
assert(HP:= H4 A B).
assert(HQ:= H5 A B).
destruct HP.
destruct HQ.
apply H9 in H1.
apply H11 in H2.
destruct HH.
apply H13 in H3.
apply cong_transitivity with A B; trivial.
apply cong_transitivity with A1 B1; Cong.

intro.
assert(HH:= H4 A0 B0).
assert(HP:= H5 A0 B0).
destruct HH.
apply H6.
assert(HH:= H4 A B).
assert(HQ:= H5 A B).
destruct HH.
destruct HQ.
apply H9 in H1.
apply H11 in H2.
destruct HP.
apply H13 in H3.
apply cong_transitivity with A2 B2; trivial.
apply cong_transitivity with A B; Cong.
Qed.


End Length_4.
