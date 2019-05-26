Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_rectangle_principle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__rectangle_principle : postulate_of_right_saccheri_quadrilaterals -> postulate_of_right_lambert_quadrilaterals.
Proof.
  intros rah A B C D HLam.
  apply (lam_per__rah A); assumption.
Qed.

End rah_rectangle_principle.