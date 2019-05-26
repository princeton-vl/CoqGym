Set Implicit Arguments.
Unset Standard Proposition Elimination Names.

Require Import util.
Require Import Le.
Require Import Plus.
Require Import Minus.
Require Import Lt.
Require Import Arith.
Require Import Omega.
Require Import Recdef.
Require Import Bool_nat.
Require Import arith_lems.
Require Import nat_below.
Require Import List.
Require Import monads.
Require Import Bool.
Require Import Compare_dec.
Require Import EqNat.
Require Import Relation_Definitions.
Require Import monoid_monad_trans.
Require Import expec.
Require Import monoid_expec.
Require Import nat_seqs.
Require Import list_utils.
Require Import sums_and_averages.
Require qs_definitions.
Require qs_parts.
Require U.
Require Import indices.
Require Import qs_sound_cmps.
Require qs_case_split.
Require Import qs_cases.
Require Import Fourier.
Require Import Rbase.
Require Import sort_order.
Import qs_definitions.mon_nondet.

Section contents.

  Variables (ee: E) (ol: list ee).

  Lemma arith_part n (b i j: nat):
    (b <= i)%nat -> (i < j)%nat -> (j < b + S n)%nat ->
    (2 * / INR (S (j - i)) * INR (i - b) + (1 + (0 + (1 + 2 * / INR (S (j - i)) * INR (b + n - j))))) / INR (S n) = 2 / INR (S (j - i)).
  Proof with auto with real.
    intros.
    repeat rewrite <- Rplus_assoc.
    rewrite Rplus_0_r.
    rewrite plus_comm.
    replace
    (2 * / INR (S (j - i)) * INR (i - b) + 1 + 1 + 2 * / INR (S (j - i)) * INR (n + b - j)) with
    (2 * / INR (S (j - i)) * (INR (i - b) + INR (n + b - j)) + 2).
      rewrite <- plus_INR.
      replace ((i - b + (n + b - j))%nat) with ((S n - S (j - i))%nat) by omega.
      rewrite minus_INR.
        field.
        split...
      omega.
    field...
  Qed.

  Lemma Index_In_dec (i: Index ee ol) l: { In i l } + { ~ In i l }.
  Proof.
    intros. apply In_dec.
    unfold Index. intros.
    apply natBelow_eq_dec.
  Qed.

  Theorem qs_comp_prob: forall i j: Index ee ol, lt i j -> forall l b, IndexSeq b l ->
    monoid_expec (U.ijcount i j) (U.qs (e:=ee) (ol:=ol) l) <= 2 / INR (S (j - i)).
  Proof with auto with real.
    do 4 intro.
    cset (sound_cmp_expec_0 i j l).
    unfold U.qs in *.
    revert H0.
    pattern l, (qs (U.cmp (e:=ee) (ol:=ol)) U.pick l).
    apply U.qs_ind.
      Focus 1.
      intros.
      apply Rle_trans with 0.
        compute...
      apply zero_le_2_div_Sn.
    intros.
    clear l.
    destruct (Index_In_dec i v).
      Focus 2. rewrite H1... apply zero_le_2_div_Sn.
    destruct (Index_In_dec j v).
      Focus 2. rewrite H1... apply zero_le_2_div_Sn.
    clear H1.
    rename H2 into H1.
    rename i0 into H2.
    rename i1 into H3.
    destruct (IndexSeq_inv H1 i H2).
    destruct (IndexSeq_inv H1 j H3).
    rewrite vec.length in *.
    cset (@monoid_expec_Node_map U.monoid (U.ijcount i j) (natBelow (S n))).
    simpl in H8. rewrite H8. clear H8.
    unfold monoid_expec_sum.
    rewrite ne_list.from_vec_to_plain at 2.
    rewrite vec.length.
    rewrite <- arith_part with n b i j...
    unfold Rdiv.
    apply Rmult_le_compat_r...
    cset (monoid_expec_map_fst_monoid_mult (U.hom_ijcount i j)).
    simpl monoid_mult in H8.
    unfold monoid_expec in H8.
    apply (@qs_case_split.case_split ee ol b i j (list (Index ee ol)) (U.ijcount i j ∘ fst) n v); intros; try rewrite H8...
            apply case_A with b...
            intros. apply H0 with b0... apply sound_cmp_expec_0...
          apply case_BD with b...
            intros. apply H0 with b0... apply sound_cmp_expec_0...
          left...
          unfold Index in *.
          apply natBelow_unique...
        apply case_C...
      apply case_BD with b...
        intros. apply H0 with b0... apply sound_cmp_expec_0...
      right...
      unfold Index in *.
      apply natBelow_unique...
    apply case_E with b...
    intros. apply H0 with b0... apply sound_cmp_expec_0.
  Qed.

End contents.
