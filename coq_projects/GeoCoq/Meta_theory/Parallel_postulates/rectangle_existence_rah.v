Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rectangle_existence_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rectangle_existence__rah : postulate_of_existence_of_a_right_lambert_quadrilateral -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros HABCD.
  destruct HABCD as [A [B [C [D []]]]].
  apply (lam_per__rah A B C D); assumption.
Qed.

End rectangle_existence_rah.