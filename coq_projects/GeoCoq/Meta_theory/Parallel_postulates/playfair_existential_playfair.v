Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Definitions.

Section playfair_existential_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair__existential_playfair :
  playfair_s_postulate ->
  existential_playfair_s_postulate.
Proof.
intro HF.
exists PA, PB, PC.
split; [apply lower_dim|]; intros; apply HF with PA PB PC; assumption.
Qed.

End playfair_existential_playfair.