Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.

Section rah_triangle.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma rah__triangle : postulate_of_right_saccheri_quadrilaterals -> triangle_postulate.
Proof.
  intros rah A B C D E F.
  apply (t22_14__bet rah).
Qed.

End rah_triangle.