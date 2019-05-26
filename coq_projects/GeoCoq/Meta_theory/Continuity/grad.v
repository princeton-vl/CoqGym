Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.
Require Import Relations.

Section Grad.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma grad__bet : forall A B C, Grad A B C -> Bet A B C.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; [Between|eBetween].
Qed.

Lemma grad__col : forall A B C, Grad A B C -> Col A B C.
Proof.
  intros; apply bet_col, grad__bet; assumption.
Qed.

Lemma grad_neq__neq13 : forall A B C, Grad A B C -> A <> B -> A <> C.
Proof.
  intros A B C HG HAB Heq.
  subst C.
  apply HAB.
  apply between_identity, grad__bet; trivial.
Qed.

Lemma grad_neq__neq12 : forall A B C, Grad A B C -> A <> C -> A <> B.
Proof.
  intros A B C HG.
  elim HG; clear HG A B C; intros; intro; treat_equalities.
    auto.
  apply H0; auto.
Qed.

Lemma grad112__eq : forall A B, Grad A A B -> A = B.
Proof.
  intros A B HG.
  assert (HA' : exists A', A' = A /\ Grad A A' B) by (exists A; auto).
  destruct HA' as [A' [Heq HG']].
  clear HG.
  revert Heq.
  elim HG'; auto.
  clear HG' A B A'.
  intros; treat_equalities; auto.
Qed.

Lemma grad121__eq : forall A B, Grad A B A -> A = B.
Proof.
  intros A B HG.
  apply between_identity, grad__bet; trivial.
Qed.

Lemma grad__le : forall A B C, Grad A B C -> Le A B A C.
Proof.
  intros.
  apply grad__bet in H.
  apply l5_12_a in H; spliter; auto.
Qed.

Lemma grad2__grad123 : forall A B C D E F, Grad2 A B C D E F -> Grad A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply grad_init.
    apply (grad_stab _ _ C); auto.
Qed.

Lemma grad2__grad456 : forall A B C D E F, Grad2 A B C D E F -> Grad D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply grad_init.
    apply (grad_stab _ _ F); auto.
Qed.

Lemma grad_sum : forall A B C D E,
  Grad A B C -> Grad A B D -> Bet A C E -> Cong A D C E ->
  Grad A B E.
Proof.
  intros A B C D E HGC HGD.
  elim (eq_dec_points A B).
  { intros; subst B.
    assert(A = C) by (apply grad112__eq; trivial).
    assert(A = D) by (apply grad112__eq; trivial).
    treat_equalities; trivial.
  }
  intro HAB.
  revert E.
  induction HGD.
    intro E; apply grad_stab; trivial.
  rename C0 into D; rename C' into D'.
  intros E' HBet' HCong'.
  destruct(segment_construction A C A D) as [E [HBet HCong]].
  assert (HBet1 : Bet A B C) by (apply grad__bet; trivial).
  assert (HBet2 : Bet A B D) by (apply grad__bet; trivial).
  assert(HBet3 : Bet C E E').
  { apply l6_13_1.
      assert_diffs; apply l6_2 with A; Between.
    apply (l5_6 A D A D'); Cong.
    apply bet__le1213; trivial.
  }
  apply grad_stab with E; auto with cong; eBetween.
  apply cong_transitivity with D D'; auto.
  apply l4_3_1 with A C; Cong.
Qed.

Lemma gradexp__grad : forall A B C, GradExp A B C -> Grad A B C.
Proof.
  induction 1.
    apply grad_init.
  apply grad_sum with C C; auto.
Qed.

Lemma gradexp_le__reach : forall A B C D B',
  GradExp A B B' -> Le C D A B' ->
  Reach A B C D.
Proof.
  intros A B C D B' HGE HLe.
  exists B'; split; trivial.
  apply gradexp__grad; trivial.
Qed.

Lemma grad__ex_gradexp_le : forall A B C,
  Grad A B C ->
  exists D, GradExp A B D /\ Le A C A D.
Proof.
  intros A B C.
  induction 1.
    exists B; split; Le; apply gradexp_init.
  destruct IHGrad as [D [HGE HLe]].
  destruct (segment_construction A D A D) as [D' [HBet HCong]].
  exists D'; split.
    apply gradexp_stab with D; Cong.
  apply bet2_le2__le1346 with C D; Le.
  apply gradexp__grad, grad__bet in HGE.
  apply l5_6 with A B A D; Cong; Le.
Qed.

Lemma reach__ex_gradexp_le : forall A B C D, Reach A B C D ->
  exists B', GradExp A B B' /\ Le C D A B'.
Proof.
  intros A B C D HR.
  destruct HR as [B0 [HG HLe]].
  destruct (grad__ex_gradexp_le A B B0 HG) as [B' [HG2 HLe2]].
  exists B'; split; trivial.
  apply le_transitivity with A B0; trivial.
Qed.

Lemma gradexp2__gradexp123 : forall A B C D E F,
  GradExp2 A B C D E F ->
  GradExp A B C.
Proof.
  intros A B C D E F.
  induction 1.
    apply gradexp_init.
  apply (gradexp_stab _ _ C); auto.
Qed.

Lemma gradexp2__gradexp456 : forall A B C D E F,
  GradExp2 A B C D E F ->
  GradExp D E F.
Proof.
  intros A B C D E F.
  induction 1.
    apply gradexp_init.
  apply (gradexp_stab _ _ F); auto.
Qed.


Inductive GradExpInv : Tpoint -> Tpoint -> Tpoint -> Prop :=
    gradexpinv_init : forall A B, GradExpInv A B B
  | gradexpinv_stab : forall A B B' C, Bet A B' B -> Cong A B' B' B -> GradExpInv A B C ->
                    GradExpInv A B' C.

Lemma gradexp_clos_trans : forall A B C, GradExp A B C <->
  clos_refl_trans_n1 Tpoint (fun X Y => Midpoint X A Y) B C.
Proof.
  intros; split; induction 1.
  - constructor.
  - apply Relation_Operators.rtn1_trans with C; [split|]; assumption.
  - constructor.
  - apply gradexp_stab with y; finish.
Qed.

Lemma gradexpinv_clos_trans : forall A B C, GradExpInv A B C <->
  clos_refl_trans_1n Tpoint (fun X Y => Midpoint X A Y) B C.
Proof.
  intros; split; induction 1.
  - constructor.
  - apply Relation_Operators.rt1n_trans with B; [split|]; assumption.
  - constructor.
  - apply gradexpinv_stab with y; finish.
Qed.

Lemma gradexp__gradexpinv : forall A B C, GradExp A B C <-> GradExpInv A B C.
Proof.
  intros.
  rewrite gradexp_clos_trans, gradexpinv_clos_trans.
  rewrite <- clos_rt_rt1n_iff, <- clos_rt_rtn1_iff.
  reflexivity.
Qed.

(** D is the last graduation of AB before or equal to C, and E the first graduation after C *)
Lemma reach__grad_min : forall A B C, A <> B -> Bet A B C -> Reach A B A C ->
  exists D E, Bet A D C /\ Grad A B D /\ E <> C /\ Bet A C E /\ Bet A D E /\ Cong A B D E.
Proof.
  intros A B C HAB HBet HReach.
  destruct HReach as [D [HD1 HD2]].
  apply l6_13_1 in HD2;
    [|apply l6_7 with B; [apply l6_6|]; apply bet_out; auto; apply grad__bet, HD1].
  revert dependent C.
  induction HD1.
    intros; assert (B = C) by (apply between_equality with A; Between); subst C.
    destruct (segment_construction A B A B) as [C []].
    assert_diffs.
    exists B, C; repeat split; finish; constructor.
  intros; destruct (l5_3 A C0 C C'); trivial.
    apply IHHD1; assumption.
  destruct (eq_dec_points C' C0).
  - subst C0.
    destruct (segment_construction A C' A B) as [C'' []].
    assert_diffs.
    exists C', C''; repeat split; Cong.
    apply grad_stab with C; assumption.
  - exists C, C'; repeat split; assumption.
Qed.

Lemma reach__ex_gradexp_lt : forall A B P Q, A <> B -> Reach P Q A B ->
  exists C, GradExp A C B /\ Lt A C P Q.
Proof.
  intros A B P Q HAB HReach.
  apply reach__ex_gradexp_le in HReach.
  destruct HReach as [R [HR1 HR2]].
  generalize dependent B.
  induction HR1; rename A0 into P, B into Q; intros.
  { destruct (midpoint_existence A B) as [C []].
    exists C; split.
      rewrite gradexp__gradexpinv.
      apply gradexpinv_stab with B; auto; constructor.
    apply le3456_lt__lt with A B; trivial.
    split; Le.
    intro; assert (C = B) by (apply (between_cong A); assumption).
    treat_equalities; auto.
  }
  rename C into R, C' into R'.
  destruct (midpoint_existence A B) as [M HM].
  assert_diffs.
  destruct (IHHR1 M) as [C []]; auto.
    apply le_mid2__le12 with B R'; [|split|]; trivial.
  exists C; split; trivial.
  destruct HM.
  apply gradexp_stab with M; trivial.
Qed.

End Grad.

Hint Resolve grad__bet : between.
Hint Resolve grad__col : col.