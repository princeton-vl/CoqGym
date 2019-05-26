Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section playfair_midpoints.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair_s_postulate_implies_midpoint_converse_postulate :
  playfair_s_postulate ->
  midpoint_converse_postulate.
Proof.
intros HP A; intros.
destruct (midpoint_existence A C) as [X HAC].
assert (X = Q).
 assert (Par_strict A B X P).
  apply triangle_mid_par with C; assumption.
 assert_diffs.
 assert_cols.
 apply l6_21 with A C P Q.
  intro.
  assert (Col A B C) by ColR.
  contradiction.
  assert (Par A B Q P /\ A <> B /\ Q <> P) by (apply par_distincts; finish).
  spliter; intuition.
  Col.
  Col.
  destruct (HP A B Q P X P P) as [HCol1 HCol2]; Col; apply par_strict_par; Par.
  Col.
treat_equalities; assumption.
Qed.

End playfair_midpoints.