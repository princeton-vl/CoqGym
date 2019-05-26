Require Import GeoCoq.Axioms.beeson_s_axioms.
Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

Section Tarski_to_intuitionistic_Tarski.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma cong_stability : forall A B C D, ~ ~ Cong A B C D -> Cong A B C D.
Proof.
intros.
elim (cong_dec A B C D); intro HCong.

  apply HCong.

  contradiction.
Qed.

Definition BetH A B C : Prop := Bet A B C /\ A <> B /\ B <> C.

Lemma bet_stability : forall A B C, ~ ~ BetH A B C -> BetH A B C.
Proof.
intros A B C HNNBet.
unfold BetH in *.
elim (bet_dec A B C); intro HBet; elim (eq_dec_points A B); intro HAB; elim (eq_dec_points B C); intro HBC.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  subst.
  exfalso.
  apply HNNBet.
  intro.
  spliter.
  intuition.

  repeat split; assumption.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.

  exfalso.
  apply HNNBet.
  intro.
  spliter.
  contradiction.
Qed.

Definition T A B C : Prop := ~ (A<>B /\ B<>C /\ ~ BetH A B C).

Definition ColB A B C := ~ (~ T C A B /\ ~ T A C B /\ ~ T A B C).

Lemma between_identity_B : forall A B, ~ BetH A B A.
Proof.
intros A B HNBet.
unfold BetH in *.
destruct HNBet as [HBet [HAB HBA]].
apply between_identity in HBet.
subst.
intuition.
Qed.

Lemma Bet_T : forall A B C, Bet A B C -> T A B C.
Proof.
intros A B C HBet.
unfold T.
intro HT.
destruct HT as [HAB [HBC HNBet]].
apply HNBet.
unfold BetH.
intuition.
Qed.

Lemma BetH_Bet : forall A B C, BetH A B C -> Bet A B C.
Proof.
unfold BetH.
intuition.
Qed.

Lemma T_Bet : forall A B C, T A B C -> Bet A B C.
Proof.
intros A B C HT.
unfold T in HT.
elim (bet_dec A B C); intro HBet.

  assumption.

  exfalso.
  apply HT.
  split.

    intro; subst; apply HBet; apply between_trivial2.

    split.

      intro; subst; apply HBet; apply between_trivial.

      intro HBetH; apply HBet; apply BetH_Bet in HBetH; assumption.
Qed.

Lemma NT_NBet : forall A B C, ~ T A B C -> ~ Bet A B C.
Proof.
intros A B C HNT.
intro HNBet.
apply HNT.
apply Bet_T.
assumption.
Qed.

Lemma T_dec : forall A B C, T A B C \/ ~ T A B C.
Proof.
intros A B C.
elim (bet_dec A B C); intro HBet.

  left; apply Bet_T; assumption.

  right; intro HT; apply HBet; apply T_Bet in HT; assumption.
Qed.

Lemma between_inner_transitivity_B : forall A B C D : Tpoint, BetH A B D -> BetH B C D -> BetH A B C.
Proof.
intros A B C D HBet1 HBet2.
unfold BetH.
repeat split.

  apply BetH_Bet in HBet1.
  apply BetH_Bet in HBet2.
  apply between_inner_transitivity with D; assumption.

  unfold BetH in HBet1.
  spliter; assumption.

  unfold BetH in HBet2.
  spliter; assumption.
Qed.

Lemma ColB_Col : forall A B C, ColB A B C -> Col A B C.
Proof.
intros A B C HCol.
unfold ColB in HCol.
unfold Col.
elim (T_dec A B C); intro HT1;
elim (T_dec A C B); intro HT2;
elim (T_dec C A B); intro HT3.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT1; intuition.

  apply T_Bet in HT2; intuition.

  apply T_Bet in HT2; intuition.

  apply T_Bet in HT3; intuition.

  exfalso; apply HCol; intuition.
Qed.

Lemma Diff_Col_ColB : forall A B C, Col A B C -> ColB A B C.
Proof.
intros A B C H.
unfold Col in H.
unfold ColB.
intro HColB.
destruct HColB as [HNT1 [HNT2 HNT3]].
apply NT_NBet in HNT1.
apply NT_NBet in HNT2.
apply NT_NBet in HNT3.
elim H.

  intro HBet; contradiction.

  intro HColAux; elim HColAux; intro HBet; clear HColAux.

    apply between_symmetry in HBet.
    contradiction.

    contradiction.
Qed.

Lemma NColB_NDiffCol : forall A B C, ~ ColB A B C -> ~ Col A B C.
Proof.
intros A B C HNCB.
intro HNC.
apply HNCB.
apply Diff_Col_ColB.
assumption.
Qed.

Lemma NColB_NColOrEq : forall A B C, ~ ColB A B C -> ~ Col A B C.
Proof.
intros A B C HNCB.
apply NColB_NDiffCol in HNCB.
assumption.
Qed.

Lemma inner_pasch_B : forall A B C P Q,
  BetH A P C -> BetH B Q C -> ~ ColB A B C ->
  exists x, BetH P x B /\ BetH Q x A.
Proof.
intros A B C P Q HBetH1 HBetH2 HNC.
unfold BetH in HBetH1.
destruct HBetH1 as [HBet1 [HAP HPC]].
unfold BetH in HBetH2.
destruct HBetH2 as [HBet2 [HBQ HQC]].
apply NColB_NColOrEq in HNC.
assert (HIP := inner_pasch A B C P Q HBet1 HBet2).
destruct HIP as [x [HBet3 HBet4]].
exists x.
split.

  split; try assumption.
  split.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

  split; try assumption.
  split.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.

    intro.
    subst.
    apply HNC.
    assert_cols.
    ColR.
Qed.

Lemma between_symmetry_B : forall A B C, BetH A B C -> BetH C B A.
Proof.
unfold BetH.
intros A B C HBet.
repeat split; intuition.
Qed.

Lemma five_segment_B : forall A A' B B' C C' D D' : Tpoint,
    Cong A B A' B' ->
    Cong B C B' C' ->
    Cong A D A' D' ->
    Cong B D B' D' ->
    ~ (A <> B /\ B <> C /\ ~ BetH A B C) ->
    ~ (A' <> B' /\ B' <> C' /\ ~ BetH A' B' C') ->
    A <> B -> Cong C D C' D'.
Proof.
intros.
assert (HBet1 : T A B C) by (unfold T; assumption).
assert (HBet2 : T A' B' C') by (unfold T; assumption).
apply T_Bet in H3.
apply T_Bet in H4.
apply five_segment with A A' B B'; assumption.
Qed.

Lemma segment_construction_B : forall A B C D, A<>B -> exists E, T A B E /\ Cong B E C D.
Proof.
intros A B C D HDiff.
assert (T := segment_construction A B C D).
destruct T as [E [HBet HCong]].
apply Bet_T in HBet.
exists E; intuition.
Qed.

Lemma lower_dim_B : ~ T PC PA PB /\ ~ T PA PC PB /\ ~ T PA PB PC.
Proof.
assert (HNBet := lower_dim).
elim (T_dec PC PA PB); intro HT1; elim (T_dec PA PC PB); intro HT2; elim (T_dec PA PB PC); intro HT3.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; right; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; right; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  exfalso; apply HNBet; right; left; apply between_symmetry; apply T_Bet; assumption.

  exfalso; apply HNBet; left; apply T_Bet; assumption.

  tauto.
Qed.

Instance Beeson_follows_from_Tarski : intuitionistic_Tarski_neutral_dimensionless.
Proof.
exact (Build_intuitionistic_Tarski_neutral_dimensionless
 Tpoint BetH Cong
 cong_stability
 bet_stability
 cong_identity
 cong_inner_transitivity
 cong_pseudo_reflexivity
 segment_construction_B
 five_segment_B
 between_identity_B
 between_symmetry_B
 between_inner_transitivity_B
 inner_pasch_B
 PA PB PC
 lower_dim_B).
Qed.

End Tarski_to_intuitionistic_Tarski.