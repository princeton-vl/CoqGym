Set Implicit Arguments.

Require Import sums_and_averages.
Require Import Reals.
Require Import nat_seqs.
Require Import arith_lems.
Require Import List.
Require Import util.
Require Import Fourier.
Require Import list_utils.
Require Import nat_below.

Require Import indices.

Definition ijs (n: nat): list (nat * nat) :=
  concat (map (fun j => map (fun i => (i, j)) (nats 0 j)) (nats 0 n)).

Lemma In_ijs n i j: lt i j -> lt j n -> List.In (i, j) (ijs n).
Proof with auto with arith.
  unfold ijs.
  intros.
  apply In_concat with (map (fun x: nat => (x, j)) (nats 0 j)).
    apply (in_map (fun i: nat => (i, j))).
    apply In_nats...
  apply (in_map (fun j0: nat => map (fun i0: nat => (i0, j0)) (nats 0 j0))).
  apply In_nats...
Qed.

Lemma In_ijs_inv n i j: List.In (i, j) (ijs n) -> (i < j < n)%nat.
Proof with auto.
  unfold ijs.
  simpl.
  intros.
  destruct (In_concat_inv _ _ H). clear H.
  destruct H0.
  destruct (In_map_inv H0). clear H0.
  destruct H1.
  subst.
  destruct (In_map_inv H). clear H.
  destruct H0.
  inversion H.
  subst.
  split.
    destruct (In_nats_inv _ _ _ H0)...
  destruct (In_nats_inv _ _ _ H1)...
Qed.

Lemma expand_sumOver_ijs n (f: nat * nat -> R):
  RsumOver (ijs n) f =
  RsumOver (nats 0 n) (fun j => RsumOver (nats 0 j) (fun i => f (i, j))).
Proof with auto with real.
  unfold ijs.
  intros.
  rewrite RsumOver_concat_map.
  unfold RsumOver.
  rewrite (map_ext (fun j => RsumOver (map (fun i => (i, j)) (nats 0 j)) f) (fun j => RsumOver (nats 0 j) (fun i => f (i, j))))...
  intro.
  unfold RsumOver.
  rewrite map_map...
Qed.

Require harmonic.

Lemma sumOver_ijs_bound n:
  RsumOver (ijs n) (fun ij => 2 / INR (S (snd ij - fst ij))) <= 2 * INR n * INR (S (log2ceil n)).
Proof with auto with real.
  rewrite expand_sumOver_ijs.
  simpl snd.
  simpl @fst.
  apply Rle_trans with (RsumOver (nats 0 n) (fun _ => 2 * INR (S (log2ceil n)))).
    apply RsumOver_le.
    intros.
    change (fun i => _) with (compose (fun i => 2 / INR (S i)) (minus x)).
    rewrite RsumOver_minus...
    rewrite plus_0_r.
    rewrite <- minus_n_n...
    apply Rle_trans with (RsumOver (nats 1 x) (fun i => 2 / INR i)).
      apply RsumOver_le.
      intros.
      unfold Rdiv.
      apply Rmult_le_compat_l...
      destruct (In_nats_inv _ _ _ H0).
      apply RIneq.Rle_Rinv...
    rewrite <- (RsumOver_mult_constant (fun i => / INR i) 2).
    apply Rmult_le_compat_l...
    apply Rle_trans with (RsumOver (nats 1 n) (Rinv ∘ INR)).
      apply RsumOver_nats_le.
        destruct (In_nats_inv _ _ _ H)...
      intros.
      unfold Rdiv.
      destruct q.
        inversion H0.
      unfold compose.
      apply O_le_inv_INR_S.
    apply harmonic.upper_bound.
  fold (compose (Rmult 2) (fun _: nat => INR (S (log2ceil n)))).
  rewrite <- RsumOver_mult_constant.
  rewrite Rmult_assoc.
  unfold RsumOver.
  rewrite Rsum_constant with (INR (S (log2ceil n))) (map (fun _ => INR (S (log2ceil n))) (nats 0 n)).
    rewrite map_length.
    rewrite nats_length...
  intros.
  destruct (In_map_inv H).
  destruct H0...
Qed.

Require U.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import monads.
Require Import monoid_monad_trans.
Require Import expec.
Require Import monoid_expec.
Require list_length_expec.
Require qs_definitions.
Require qs_parts.
Require qs_sound_cmps.
Require Import Rbase.
Require qs_cmp_prob.
Require qs_CM_U_expec_cost_eq.
Require Import sort_order.

Import qs_definitions.mon_nondet.

Arguments length {A}.

Section contents.

  Variables (ee: E) (ol: list ee).

  Theorem Umonoid_expec_qs_bounded_by_sumOver_ijs l: IndexSeq 0 l ->
    @monoid_expec U.monoid length _ (qs (@U.cmp ee ol) U.pick l) <=
      RsumOver (ijs (length l)) (fun ij => 2 / INR (S (snd ij - fst ij))).
  Proof with auto with real.
    unfold RsumOver.
    intros.
    assert (NoDup l).
      apply IndexSeq_NoDup with 0%nat...
    unfold monoid_expec.
    rewrite <- (expec_map (@fst U.monoid (list (Index ee ol))) length).
    apply (list_length_expec.exp_list_sum_le U.UcmpDec).
      intros.
      rewrite expec_map.
      destruct i.
      simpl expec.
      simpl snd.
      simpl @fst.
      cset qs_cmp_prob.qs_comp_prob.
      unfold monoid_expec in H2.
      unfold U.ijcount in H2.
      unfold list_length_expec.beq_X.
      unfold U.UcmpCmp in H2.
      destruct (In_ijs_inv _ _ _ H1).
      assert (lt n (length l)).
        apply lt_trans with n0...
      destruct (In_map_inv (H _ (le_O_n _) H5)).
      destruct (In_map_inv (H _ (le_O_n _) H4)).
      destruct H6. destruct H7.
      unfold compose in H2.
      unfold compose.
      unfold U.monoid in H2.
      simpl monoid_type in H2.
      assert (lt x x0).
        rewrite H6.
        rewrite H7...
      cset (H2 ee ol x x0 H10 l 0%nat H).
      rewrite H6 in H11.
      rewrite H7 in H11...
    intros.
    rewrite expec_map.
    replace 0 with (INR 0)...
    apply expec_constant.
    intros.
    unfold compose.
    apply count_0.
    intros.
    destruct x0.
    destruct (qs_sound_cmps.qs_sound_cmps_2 l H2 n n0 H3).
    cset (qs_sound_cmps.qs_sound_cmps H2 H0 n n0 H3).
    unfold list_length_expec.beq_X.
    destruct (U.UcmpDec i (n, n0))...
    elimtype False.
    apply H1. clear H1.
    subst.
    apply In_ijs...
    destruct (In_map_inv H5).
    destruct H1.
    destruct (IndexSeq_inv H x0 H7).
    subst...
  Qed.

  Require NDP.

  Theorem qs_expec_cost:
    expec cost (NDP.qs ee ol) <= 2 * INR (length ol) * INR (S (log2ceil (length ol))).
  Proof with auto.
    intros.
    apply Rle_trans with (RsumOver (ijs (length ol)) (fun ij => 2 / INR (S (snd ij - fst ij)))).
      destruct (indices ee ol).
      destruct H.
      rewrite H.
      cset (@qs_CM_U_expec_cost_eq.qs_CM_U_expec_cost_eq ee ol x).
      simpl monoid_type in H1.
      rewrite H1.
      rewrite map_length.
      apply Umonoid_expec_qs_bounded_by_sumOver_ijs...
    apply sumOver_ijs_bound.
  Qed.

End contents.

Theorem qs_avg_complexity (ee: E):
  over (@length (_:Set)), expec cost ∘ @NDP.qs ee =O(fun n => INR (n * log2ceil n)).
Proof with auto with real.
  unfold NDP.qs.
  unfold measured_bigO.
  exists 3.
  exists 3%nat.
  intros.
  rewrite mult_INR.
  rewrite <- Rmult_assoc.
  apply Rle_trans with (2 * INR (length x) * INR (S (log2ceil (length x)))).
    unfold compose.
    apply qs_expec_cost.
  intros.
  rewrite S_INR.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite (Rmult_assoc 3).
  replace 3 with (2+1) by ring.
  rewrite (Rmult_plus_distr_r 2 1).
  rewrite Rmult_1_l.
  rewrite Rmult_assoc.
  apply Rplus_le_compat_l.
  rewrite Rmult_comm.
  apply Rmult_le_compat_l...
  replace 2 with (INR 2)...
  apply le_INR.
  apply le_trans with (log2ceil 3)...
  apply log2ceil_preserves_le...
Qed.

Print Assumptions qs_avg_complexity.
