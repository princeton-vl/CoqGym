Require Export GeoCoq.Tarski_dev.Definitions.
Require Export GeoCoq.Tactics.finish.

Ltac prolong A B x C D :=
 assert (sg:= segment_construction A B C D);
 ex_and sg x.

Section T1_1.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma cong_reflexivity : forall A B,
 Cong A B A B.
Proof.
    intros.
    apply (cong_inner_transitivity B A A B); apply cong_pseudo_reflexivity.
Qed.

Lemma cong_symmetry : forall A B C D : Tpoint,
 Cong A B C D -> Cong C D A B.
Proof.
    intros.
    eapply cong_inner_transitivity.
      apply H.
    apply cong_reflexivity.
Qed.

Lemma cong_transitivity : forall A B C D E F : Tpoint,
 Cong A B C D -> Cong C D E F -> Cong A B E F.
Proof.
    intros.
    eapply cong_inner_transitivity; eauto using cong_symmetry.
Qed.

Lemma cong_left_commutativity : forall A B C D,
 Cong A B C D -> Cong B A C D.
Proof.
    intros.
    eapply cong_inner_transitivity.
      apply cong_symmetry.
      apply cong_pseudo_reflexivity.
    assumption.
Qed.

Lemma cong_right_commutativity : forall A B C D,
 Cong A B C D -> Cong A B D C.
Proof.
    intros.
    apply cong_symmetry.
    apply cong_symmetry in H.
    apply cong_left_commutativity.
    assumption.
Qed.

Lemma cong_3421 : forall A B C D,
 Cong A B C D -> Cong C D B A.
Proof.
    auto using cong_symmetry, cong_right_commutativity.
Qed.

Lemma cong_4312 : forall A B C D,
 Cong A B C D -> Cong D C A B.
Proof.
    auto using cong_symmetry, cong_right_commutativity.
Qed.

Lemma cong_4321 : forall A B C D,
 Cong A B C D -> Cong D C B A.
Proof.
    auto using cong_symmetry, cong_right_commutativity.
Qed.


Lemma cong_trivial_identity : forall A B : Tpoint,
 Cong A A B B.
Proof.
    intros.
    prolong A B E A A.
    eapply cong_inner_transitivity.
      apply H0.
    assert(B=E).
      eapply cong_identity.
      apply H0.
    subst.
    apply cong_reflexivity.
Qed.

Lemma cong_reverse_identity : forall A C D,
 Cong A A C D -> C=D.
Proof.
    intros.
    apply cong_symmetry in H.
    eapply cong_identity.
    apply H.
Qed.

Lemma cong_commutativity : forall A B C D,
 Cong A B C D -> Cong B A D C.
Proof.
    intros.
    apply cong_left_commutativity.
    apply cong_right_commutativity.
    assumption.
Qed.

End T1_1.

Hint Resolve cong_commutativity cong_3421 cong_4312 cong_4321 cong_trivial_identity
             cong_left_commutativity cong_right_commutativity
             cong_transitivity cong_symmetry cong_reflexivity : cong.

Ltac Cong := auto 4 with cong.
Ltac eCong := eauto with cong.

Section T1_2.

Context `{Tn:Tarski_neutral_dimensionless}.

(* We pre-compute some trivial lemmas to have more efficient automatic proofs. *)

Lemma not_cong_2134 : forall A B C D, ~ Cong A B C D -> ~ Cong B A C D.
Proof.
auto with cong.
Qed.

Lemma not_cong_1243 : forall A B C D, ~ Cong A B C D -> ~ Cong A B D C.
Proof.
auto with cong.
Qed.

Lemma not_cong_2143 : forall A B C D, ~ Cong A B C D -> ~ Cong B A D C.
Proof.
auto with cong.
Qed.

Lemma not_cong_3412 : forall A B C D, ~ Cong A B C D -> ~ Cong C D A B.
Proof.
auto with cong.
Qed.

Lemma not_cong_4312 : forall A B C D, ~ Cong A B C D -> ~ Cong D C A B.
Proof.
auto with cong.
Qed.

Lemma not_cong_3421 : forall A B C D, ~ Cong A B C D -> ~ Cong C D B A.
Proof.
auto with cong.
Qed.

Lemma not_cong_4321 : forall A B C D, ~ Cong A B C D -> ~ Cong D C B A.
Proof.
auto with cong.
Qed.

End T1_2.

Hint Resolve not_cong_2134 not_cong_1243 not_cong_2143
             not_cong_3412 not_cong_4312 not_cong_3421 not_cong_4321 : cong.

Section T1_3.


Context `{Tn:Tarski_neutral_dimensionless}.

Lemma five_segment_with_def : forall A B C D A' B' C' D',
 OFSC A B C D A' B' C' D' -> A<>B -> Cong C D C' D'.
Proof.
    unfold OFSC.
    intros;spliter.
    apply (five_segment A A' B B'); assumption.
Qed.

Lemma cong_diff : forall A B C D : Tpoint,
 A <> B -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro.
    subst.
    apply H.
    eauto using cong_identity.
Qed.

Lemma cong_diff_2 : forall A B C D ,
 B <> A -> Cong A B C D -> C <> D.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using cong_identity, cong_symmetry.
Qed.

Lemma cong_diff_3 : forall A B C D ,
 C <> D -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    eauto using cong_identity, cong_symmetry.
Qed.

Lemma cong_diff_4 : forall A B C D ,
 D <> C -> Cong A B C D -> A <> B.
Proof.
    intros.
    intro;subst.
    apply H.
    symmetry.
    eauto using cong_identity, cong_symmetry.
Qed.

Lemma cong_3_sym : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A' B' C' A B C.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong_3_swap : forall A B C A' B' C',
  Cong_3 A B C A' B' C' -> Cong_3 B A C B' A' C'.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong_3_swap_2 : forall A B C A' B' C',
 Cong_3 A B C A' B' C' -> Cong_3 A C B A' C' B'.
Proof.
    unfold Cong_3.
    intuition.
Qed.

Lemma cong3_transitivity : forall A0 B0 C0 A1 B1 C1 A2 B2 C2,
 Cong_3 A0 B0 C0 A1 B1 C1 -> Cong_3 A1 B1 C1 A2 B2 C2 -> Cong_3 A0 B0 C0 A2 B2 C2.
Proof.
    unfold Cong_3.
    intros.
    spliter.
    repeat split; eapply cong_transitivity; eCong.
Qed.

End T1_3.

Hint Resolve cong_3_sym : cong.
Hint Resolve cong_3_swap cong_3_swap_2 cong3_transitivity : cong3.
Hint Unfold Cong_3 : cong3.

Section T1_4.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma eq_dec_points : forall A B : Tpoint, A=B \/ ~ A=B.
Proof. exact point_equality_decidability. Qed.

Lemma distinct : forall P Q R : Tpoint, P <> Q -> (R <> P \/ R <> Q).
Proof.
    intros.
    induction (eq_dec_points R P).
      subst R.
      right.
      assumption.
    left.
    assumption.
Qed.

Lemma l2_11 : forall A B C A' B' C',
 Bet A B C -> Bet A' B' C' -> Cong A B A' B' -> Cong B C B' C' -> Cong A C A' C'.
Proof.
    intros.
    induction (eq_dec_points A B).
      subst B.
      assert (A' = B') by
     (apply (cong_identity A' B' A); Cong).
      subst; Cong.
    apply cong_commutativity; apply (five_segment A A' B B' C C' A A'); Cong.
Qed.

Lemma bet_cong3 : forall A B C A' B',  Bet A B C -> Cong A B A' B' -> exists C', Cong_3 A B C A' B' C'.
Proof.
    intros.
    assert (exists x, Bet A' B' x /\ Cong B' x B C) by (apply segment_construction).
    ex_and H1 x.
    assert (Cong A C A' x).
      eapply l2_11.
        apply H.
        apply H1.
        assumption.
      Cong.
    exists x;unfold Cong_3; repeat split;Cong.
Qed.

Lemma construction_uniqueness : forall Q A B C X Y,
 Q <> A -> Bet Q A X -> Cong A X B C -> Bet Q A Y -> Cong A Y B C -> X=Y.
Proof.
    intros.
    assert (Cong A X A Y) by (apply cong_transitivity with B C; Cong).
    assert (Cong Q X Q Y) by (apply (l2_11 Q A X Q A Y);Cong).
    assert(OFSC Q A X Y Q A X X) by (unfold OFSC;repeat split;Cong).
    apply five_segment_with_def in H6; try assumption.
    apply cong_identity with X; Cong.
Qed.

Lemma Cong_cases :
 forall A B C D,
 Cong A B C D \/ Cong A B D C \/ Cong B A C D \/ Cong B A D C \/
 Cong C D A B \/ Cong C D B A \/ Cong D C A B \/ Cong D C B A ->
 Cong A B C D.
Proof.
    intros.
    decompose [or] H;clear H; Cong.
Qed.

Lemma Cong_perm :
 forall A B C D,
 Cong A B C D ->
 Cong A B C D /\ Cong A B D C /\ Cong B A C D /\ Cong B A D C /\
 Cong C D A B /\ Cong C D B A /\ Cong D C A B /\ Cong D C B A.
Proof.
    intros.
    repeat split; Cong.
Qed.

End T1_4.