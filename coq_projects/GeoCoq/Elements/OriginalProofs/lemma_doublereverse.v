Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_doublereverse : 
   forall A B C D, 
   Cong A B C D ->
   Cong D C B A /\ Cong B A D C.
Proof.
intros.
assert (Cong C D D C) by (conclude cn_equalityreverse).
assert (Cong A B D C) by (conclude lemma_congruencetransitive).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Cong B A D C) by (conclude lemma_congruencetransitive).
assert (Cong D C B A) by (conclude lemma_congruencesymmetric).
close.
Qed.

End Euclid.


