Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_existential_saccheri.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__existential_saccheri : postulate_of_right_saccheri_quadrilaterals -> postulate_of_existence_of_a_right_saccheri_quadrilateral.
Proof.
  intro rah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  exists A; exists B; exists C; exists D.
  split.
    assumption.
    apply (rah A B C D HSac).
Qed.

End rah_existential_saccheri.