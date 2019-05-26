Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section par_trans_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma par_trans_implies_playfair :
  postulate_of_transitivity_of_parallelism -> playfair_s_postulate.
Proof.
intros HPT A1; intros.
assert (Par C1 C2 B1 B2) by (apply HPT with A1 A2; Par).
induction H3.
exfalso; apply H3; exists P; Col.
spliter; split; Col.
Qed.

End par_trans_playfair.