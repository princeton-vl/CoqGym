Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section thales_postulate_thales_converse_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(** This comes from the proof of Martin's Theorem 23.7 (N -> O) *)

Lemma thales_postulate__thales_converse_postulate : thales_postulate -> thales_converse_postulate.
Proof.
  intros thales A B C M HNCol HM HPer.
  assert_diffs.
  assert(M <> C) by (intro; subst; apply HNCol; Col).
  destruct (segment_construction_3 M C M A) as [C' [HC' HCong]]; auto.
  apply cong_symmetry in HCong.
  elim(eq_dec_points C C').
    intro; subst; assumption.
  intro.
  exfalso.
  assert_diffs.
  assert(~ Col A B C') by (intro; apply HNCol; ColR).
  assert(~ Col A C C') by (intro; apply HNCol; ColR).
  assert(~ Col B C C') by (intro; apply HNCol; ColR).
  assert_diffs.
  assert(CongA A C B A C' B).
    apply l11_16; auto; apply (thales _ _ _ M); assumption.
  assert(OS A B C C') by (apply (out_one_side_1 _ _ _ _ M); Col).
  destruct HC' as [_ [_ [HMCC'|HMC'C]]].
  - assert(Hlta : LtA A C' B A C B).
    2: destruct Hlta; CongA.
    apply os3__lta; Side;
    apply (one_side_transitivity _ _ _ M).
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.

  - assert(Hlta : LtA A C B A C' B).
    2: destruct Hlta; CongA.
    apply os3__lta; Side;
    apply (one_side_transitivity _ _ _ M).
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply invert_one_side; apply out_one_side; Col; apply l6_6; apply bet_out; Between.
      apply out_one_side; Col; apply l6_6; apply bet_out; Between.
Qed.

End thales_postulate_thales_converse_postulate.