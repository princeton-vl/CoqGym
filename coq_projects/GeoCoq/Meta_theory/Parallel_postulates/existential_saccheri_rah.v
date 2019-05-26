Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section existential_saccheri_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma existential_saccheri__rah : postulate_of_existence_of_a_right_saccheri_quadrilateral -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro HABCD.
  destruct HABCD as [A [B [C [D [HSac HPer]]]]].
  apply (per_sac__rah A B C D HSac HPer).
Qed.

End existential_saccheri_rah.
