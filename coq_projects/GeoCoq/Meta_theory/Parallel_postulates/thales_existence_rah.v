Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section thales_existence_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.


Lemma thales_existence__rah : existential_thales_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro thales.
  destruct thales as [A [B [C [M]]]].
  spliter.
  apply (t22_17__rah A B C M); assumption.
Qed.

End thales_existence_rah.