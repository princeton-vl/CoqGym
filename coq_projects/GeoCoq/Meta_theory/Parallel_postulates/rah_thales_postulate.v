Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_thales_postulate.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__thales_postulate : postulate_of_right_saccheri_quadrilaterals -> thales_postulate.
Proof.
  intros rah A B C M HNCol HM HCong.
  apply (t22_17__rah _ _ _ M); assumption.
Qed.

End rah_thales_postulate.