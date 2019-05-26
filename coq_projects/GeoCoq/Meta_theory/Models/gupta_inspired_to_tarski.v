Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Tarski_dev.Ch05_bet_le.

Section Gupta_inspired_variant_of_Tarski_neutral_dimensionless_to_Tarski_neutral_dimensionless.

Context `{ITnEQD:Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma g2_1 : forall A B, CongG A B A B.
Proof.
intros A B.
apply cong_inner_transitivityG with B A;
apply cong_pseudo_reflexivityG; auto.
Qed.

Lemma g2_2 : forall A B C D,
  CongG A B C D -> CongG C D A B.
Proof.
intros A B C D HCong.
apply cong_inner_transitivityG with C D; auto; apply g2_1.
Qed.

Lemma cong_inner_transitivityT : forall A B C D E F,
  CongG A B C D -> CongG A B E F -> CongG C D E F.
Proof.
intros A B C D E F HCong1 HCong2.
apply cong_inner_transitivityG with A B; apply g2_2; auto.
Qed.

Lemma g2_3 : forall A B C D,
  CongG A B C D -> CongG B A C D.
Proof.
Proof.
intros A B C D HCong.
apply cong_inner_transitivityT with A B; auto.
apply cong_pseudo_reflexivityG.
Qed.

Lemma g2_4 : forall A B C D,
  CongG A B C D -> CongG A B D C.
Proof. intros A B C D HCong; apply g2_2; apply g2_3; apply g2_2; auto. Qed.

Lemma g2_5 : forall A B C D,
  CongG A B C D -> (A = B <-> C = D).
Proof.
intros A B C D HCong.
split; intro H; rewrite H in HCong;
[apply g2_2 in HCong|]; apply cong_identityG in HCong; auto.
Qed.

Lemma g2_6 : forall A B,
  BetG A B B /\ CongG B B A A.
Proof.
intros A B; destruct (segment_constructionG A B A A) as [C [HBet HCong]].
assert (B = C) by (apply g2_5 with A A; auto).
rewrite H in *; auto.
Qed.

Lemma g2_7 : forall A B C A' B' C',
  CongG A B A' B' -> CongG B C B' C' ->
  BetG A B C -> BetG A' B' C' ->
  CongG A C A' C'.
Proof.
intros A B C A' B' C' HCong1 HCong2 HBet1 HBet2.
elim (point_equality_decidabilityG A B); intro HDiff1; [rewrite HDiff1 in *; clear HDiff1|].

  {
  assert (HEq : A' = B') by (apply g2_5 with B B; try apply g2_2; auto).
  rewrite HEq; auto.
  }

  {
  elim (g2_6 A' A); intro HBet3; intro HCong3.
  apply g2_3; apply g2_4; apply five_segmentG with A A' B B'; auto.
  apply g2_3; apply g2_4; auto.
  }
Qed.

Lemma g2_8 : forall A B C D,
  BetG A B C -> BetG A B D -> CongG B C B D -> A <> B -> C = D.
Proof.
intros A B C D HBet1 HBet2 HCong HDiff.
assert (HEq : CongG C C C D).
  {
  apply five_segmentG with A A B B; auto; try apply g2_1.
  apply g2_7 with B B; auto; apply g2_1.
  }
apply g2_5 with C C; auto; apply g2_2; auto.
Qed.

Lemma g2_9 : forall A B C, BetG A B A -> BetG C A B.
Proof.
intros A B C HBet.
apply bet_inner_transitivityG with A; auto; apply g2_6.
Qed.

Lemma g2_10 : forall A B C, BetG A B A -> BetG C B A.
Proof. intros A B C HBet; do 2 apply g2_9; auto. Qed.

Lemma g2_11 : forall A B C,
  BetG A B A -> A <> B ->
  exists D, BetG C D C /\ BetG D C D /\ C <> D.
Proof.
intros A B C HBet1 HDiff1.
destruct (segment_constructionG C C A B) as [D [HBet2 HCong1]].
assert (HDiff2 : C <> D)
  by (intro; apply g2_5 in HCong1; apply HDiff1; apply HCong1; auto).
destruct (segment_constructionG C D B A) as [E [HBet3 HCong2]].
assert (HCong3 : CongG C E A A) by (apply g2_7 with D B; auto).
assert (HEq : C = E) by (apply g2_5 in HCong3; apply HCong3; auto).
rewrite HEq in *; clear HEq; exists D; do 2 (split; auto); apply g2_9; auto.
Qed.

Lemma g2_12 : forall A B C, BetG A B A -> BetG A B C.
Proof. intros A B C HBet; apply bet_symmetryG; apply g2_10; auto. Qed.

Lemma g2_13 : forall A B C, BetG A B A -> A <> B -> BetG C B C.
Proof.
intros A B C HBet1 HDiff.
destruct (segment_constructionG C B B C) as [D [HBet2 HCong1]].
assert (HEq : C = D) by (apply g2_8 with A B; try apply g2_2; try apply g2_12; auto).
rewrite HEq in *; auto.
Qed.

Lemma g2_14 : forall A B C D, BetG A B A -> A <> B -> BetG C D C /\ BetG D C D.
Proof.
intros A B C D HBet1 HDiff1.
split.

  {
  destruct (g2_11 A B D) as [E [HBet2 [HBet3 HDiff2]]]; auto.
  apply g2_13 with E; auto.
  }

  {
  destruct (g2_11 A B C) as [E [HBet2 [HBet3 HDiff2]]]; auto.
  apply g2_13 with E; auto.
  }
Qed.

Lemma g2_15 : forall A B C D E, BetG A B A -> A <> B -> BetG C D E.
Proof.
intros A B C D E HBet HDiff.
apply g2_9. destruct (g2_14 A B D E) as [HBet1 HBet2]; auto.
Qed.

Lemma g2_16 : forall A B C D E, ~ BetG C D E -> BetG A B A -> A = B.
Proof.
intros A B C D E HNBet HBet.
elim (point_equality_decidabilityG A B); intro HDiff; auto.
exfalso; apply HNBet; apply g2_15 with A B; auto.
Qed.

Lemma between_identityT : forall A B, BetG A B A -> A = B.
Proof.
intros A B; apply g2_16 with GPA GPB GPC; intro HNBet; apply lower_dimG; left; auto.
Qed.

Lemma cong_trivial_identityT : forall A B, CongG A A B B.
Proof. intros A B; destruct (g2_6 B A); auto. Qed.

Lemma l2_11T : forall A B C A' B' C',
  BetG A B C -> BetG A' B' C' ->
  CongG A B A' B' -> CongG B C B' C' ->
  CongG A C A' C'.
Proof.
intros A B C A' B' C' HBet1 HBet2 HCong1 HCong2.
elim (point_equality_decidabilityG A B); intro HDiff; [rewrite HDiff in *; clear HDiff|].

  {
  assert (HEq : A' = B') by (apply g2_5 with B B; try apply g2_2; auto).
  rewrite HEq in *; auto.
  }

  {
  apply g2_3; apply g2_4; apply five_segmentG with A A' B B'; auto;
  try apply cong_trivial_identityT; apply g2_3; apply g2_4; auto.
  }
Qed.

Lemma construction_uniquenessT : forall Q A B C X Y,
  Q <> A -> BetG Q A X -> CongG A X B C -> BetG Q A Y -> CongG A Y B C -> X = Y.
Proof.
intros Q A B C X Y HDiff HBet1 HCong1 HBet2 HCong2.
assert (HCong3 : CongG A X A Y) by (apply cong_inner_transitivityG with B C; auto).
assert (HCong4 : CongG Q X Q Y) by (apply l2_11T with A A; auto; apply g2_1).
assert (HCong5 : CongG X X X Y)
  by (apply five_segmentG with Q Q A A; auto; apply g2_1).
apply g2_5 with X X; try apply g2_2; auto.
Qed.

Lemma between_trivialT : forall A B, BetG A B B.
Proof. intros A B; destruct (g2_6 A B); auto. Qed.

Lemma bet_decG : forall A B C, BetG A B C \/ ~ BetG A B C.
Proof.
intros A B C.
destruct (segment_constructionG A B B C) as [D [HBet1 HCong]].
elim (point_equality_decidabilityG C D); intro HDiff1; [rewrite HDiff1 in *; auto|].
elim (point_equality_decidabilityG A B); intro HDiff2;
[rewrite HDiff2 in *; left; apply bet_symmetryG; apply between_trivialT|].
right; intro HBet2; apply HDiff1; apply construction_uniquenessT with A B B C;
auto; apply g2_1.
Qed.

Definition ColG A B C := BetG A B C \/ BetG B C A \/ BetG C A B.

Lemma col_decG : forall A B C, ColG A B C \/ ~ ColG A B C.
Proof.
intros A B C; unfold ColG; induction (bet_decG A B C); induction (bet_decG B C A);
induction (bet_decG C A B); tauto.
Qed.

Lemma inner_paschT : forall A B C P Q,
  BetG A P C -> BetG B Q C ->
  exists x, BetG P x B /\ BetG Q x A.
Proof.
intros A B C P Q HBet1 HBet2.
elim (point_equality_decidabilityG A P); intro HDiff1;
[rewrite HDiff1 in *; exists P; split;
 [apply bet_symmetryG|]; apply between_trivialT|].
elim (point_equality_decidabilityG P C); intro HDiff2;
[rewrite HDiff2 in *; exists Q; split; apply bet_symmetryG;
 try apply between_trivialT; auto|].
elim (point_equality_decidabilityG B Q); intro HDiff3;
[rewrite HDiff3 in *; exists Q; split;
 [|apply bet_symmetryG]; apply between_trivialT|].
elim (point_equality_decidabilityG Q C); intro HDiff4;
[rewrite HDiff4 in *; exists P; split; apply bet_symmetryG;
 try apply between_trivialT; auto|].
elim (col_decG A B C); intro HCol; [|apply inner_paschG with C; auto].
do 2 (try (elim HCol; clear HCol; intro HCol)); rename HCol into HBet3.

  {
  exists B; split; [apply between_trivialT|].
  apply bet_symmetryG; apply bet_inner_transitivityG with C; auto.
  }

  {
  exists C; split.

    {
    apply bet_symmetryG; apply bet_inner_transitivityG with A;
    auto; apply bet_symmetryG; auto.
    }

    {
    apply bet_symmetryG; apply bet_inner_transitivityG with B;
    apply bet_symmetryG; auto.
    }
  }

  {
  exists A; split; [|apply between_trivialT].
  apply bet_symmetryG; apply bet_inner_transitivityG with C;
  auto; apply bet_symmetryG; auto.
  }
Qed.

Global Instance TG_to_T : Tarski_neutral_dimensionless.
Proof.
exact
(Build_Tarski_neutral_dimensionless TpointG BetG CongG
   cong_pseudo_reflexivityG cong_inner_transitivityT cong_identityG
   segment_constructionG five_segmentG
   between_identityT inner_paschT
   GPA GPB GPC
   lower_dimG).
Defined.

Global Instance TG_to_TID :
  Tarski_neutral_dimensionless_with_decidable_point_equality TG_to_T.
Proof. split; exact point_equality_decidabilityG. Defined.

End Gupta_inspired_variant_of_Tarski_neutral_dimensionless_to_Tarski_neutral_dimensionless.

Section Gupta_inspired_variant_of_Tarski_2D_to_Tarski_2D.

Context `{IT2D:Gupta_inspired_variant_of_Tarski_2D}.

Lemma upper_dimT : forall A B C P Q,
  P <> Q -> CongG A P A Q -> CongG B P B Q -> CongG C P C Q ->
  (BetG A B C \/ BetG B C A \/ BetG C A B).
Proof.
intros A B C P Q HPQ HCong1 HCong2 HCong3.
elim (point_equality_decidabilityG A B); intro HAB; try (rewrite HAB in *; clear HAB);
elim (point_equality_decidabilityG A C); intro HAC; try (rewrite HAC in *; clear HAC);
elim (point_equality_decidabilityG B C); intro HBC; try (rewrite HBC in *; clear HBC).

  {
  left; apply between_trivialT.
  }

  {
  right; right; apply between_trivialT.
  }

  {
  left; apply between_trivialT.
  }

  {
  right; right; apply between_trivialT.
  }

  {
  left; apply between_trivialT.
  }

  {
  right; left; apply between_trivialT.
  }

  {
  left; apply between_trivialT.
  }

  {
  apply upper_dimG with P Q; auto.
  }
Qed.

Global Instance TG2D_to_T2D : Tarski_2D TG_to_TID.
Proof. split; exact upper_dimT. Defined.

End Gupta_inspired_variant_of_Tarski_2D_to_Tarski_2D.

Section Gupta_inspired_variant_of_Tarski_euclidean_to_Tarski_euclidean.

Context `{ITE:Gupta_inspired_variant_of_Tarski_euclidean}.


Lemma euclidT : forall A B C D T,
  Bet A D T -> Bet B D C -> A <> D ->
  exists X, exists Y, Bet A B X /\ Bet A C Y /\ Bet X T Y.
Proof.
assert (H := TG_to_TID).
intros A B C D T HBet1 HBet2 HDiff1.
elim (eq_dec_points B D); intro HDiff2;
[treat_equalities; exists T, C; Between|].
elim (eq_dec_points D C); intro HDiff3;
[treat_equalities; exists B, T; Between|].
elim (col_dec A B C); intro HCol; [|apply euclidG with D; auto].
clear HDiff2; clear HDiff3.
do 2 (try (elim HCol; clear HCol; intro HCol)); rename HCol into HBet3.

  {
  elim (eq_dec_points A B); intro HDiff2;
  [treat_equalities; exists T; exists C; Between|].
  elim (l5_2 A B C T); eBetween; intro HBet4.

    {
    elim (eq_dec_points B C); intro HDiff3;
    [treat_equalities; exists T; exists T; Between|].
    exists B; exists T; do 2 (split; Between); eBetween.
    }

    {
    elim (eq_dec_points B T); intro HDiff3;
    [treat_equalities; exists B; exists C; Between|].
    exists B; exists C; Between.
    }
  }

  {
  elim (eq_dec_points A C); intro HDiff2;
  [treat_equalities; exists B; exists T; Between|].
  elim (l5_2 A C B T); eBetween; intro HBet4.

    {
    elim (eq_dec_points B C); intro HDiff3;
    [treat_equalities; exists T; exists T; Between|].
    exists T; exists C; repeat (split; Between); eBetween.
    }

    {
    exists B; exists C; Between.
    }
  }

  {
  elim (l5_3 B A D C); Between; intro HBet4.

    {
    elim (eq_dec_points A B); intro HDiff2;
    [treat_equalities; exists T; exists C; Between|].
    elim (l5_2 B A C T); eBetween; intro HBet5.

      {
      exists B; exists T; Between.
      }

      {
      exists B; exists C; do 2 (split; Between).
      apply outer_transitivity_between2 with A; eBetween.
      intro; treat_equalities; intuition.
      }
    }

    {
    elim (l5_2 A D B T); Between; intro HBet5.

      {
      elim (eq_dec_points B D); intro HDiff2;
      [treat_equalities; exists T; exists C; Between|].
      exists T; exists C; do 2 (try split; Between); eBetween.
      }

      {
      exists B; exists C; do 2 (split; Between).
      apply outer_transitivity_between with A; eBetween;
      try (intro; treat_equalities; intuition).
      }
    }
  }
Qed.

Global Instance TG_euclidean_to_T_euclidean :
  Tarski_euclidean TG_to_TID.
Proof. split; exact euclidT. Defined.

End Gupta_inspired_variant_of_Tarski_euclidean_to_Tarski_euclidean.