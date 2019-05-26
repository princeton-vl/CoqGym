Set Implicit Arguments.

Require Import
  Reals Fourier Omega
  sums_and_averages nat_seqs arith_lems util list_utils nat_below.

Lemma upper_bound n: RsumOver (nats 1 n) (Rinv ∘ INR) <= INR (S (log2ceil n)).
Proof with auto with real.
  intros.
  rewrite S_INR.
  rewrite Rplus_comm.
  apply Rle_trans with (RsumOver (nats 1 (pow 2 (log2ceil n))) (Rinv ∘ INR)).
    apply RsumOver_nats_le.
      destruct n...
      unfold log2ceil.
      apply pow2_ceil_log2.
    intros.
    destruct q.
      inversion H.
    unfold compose...
  rewrite split_pow2_range.
  rewrite RsumOver_cons.
  rewrite RsumOver_concat_map.
  unfold compose.
  simpl INR.
  rewrite Rinv_1...
  apply Rplus_le_compat_l.
  replace (INR (log2ceil n)) with (INR (length (nats 0 (log2ceil n))) * 1).
    Focus 2.
    rewrite nats_length.
    apply Rmult_1_r.
  apply RsumOver_constant_le.
  intros.
  rewrite RsumOver_nats.
  apply Rle_eq_trans with (RsumOver (nats 0 (pow 2 x)) (fun _ => / INR (pow 2 x))).
    apply RsumOver_le.
    intros.
    unfold compose. simpl.
    rewrite <- plus_assoc.
    rewrite plus_comm.
    simpl plus.
    apply Rle_Rinv...
      apply lt_INR_0.
      apply pow_min...
    apply le_INR.
    omega.
  unfold RsumOver.
  rewrite Rsum_constant with (/ INR (pow 2 x)) (map (fun _ => / INR (pow 2 x)) (nats 0 (pow 2 x))).
    rewrite map_length.
    rewrite nats_length.
    apply Rinv_r.
    apply not_O_INR.
    intro.
    assert ((2 <> 0)%nat)...
    cset (pow_min H1 x).
    rewrite H0 in H2.
    apply (lt_irrefl _ H2).
  intros.
  destruct (In_map_inv H0).
  destruct H1...
Qed.
