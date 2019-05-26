Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section playfair_alternate_interior_angles.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair__alternate_interior :  playfair_s_postulate -> alternate_interior_angles_postulate.
Proof.
intros playfair A B C D Hts HPar.
assert(~ Col B A C) by (destruct Hts; auto).
assert(HD' := ex_conga_ts B A C A C B).
destruct HD' as [D' []]; Col.
apply (conga_trans _ _ _ D' C A).
CongA.
assert_diffs.
apply (out_conga D C A D C A); try (apply out_trivial); CongA.
apply (col_one_side_out _ A).
assert (HP := playfair A B C D C D' C).
destruct HP; Col.
apply l12_21_b; CongA; Side.
apply invert_one_side; exists B; split; Side.
Qed.

End playfair_alternate_interior_angles.