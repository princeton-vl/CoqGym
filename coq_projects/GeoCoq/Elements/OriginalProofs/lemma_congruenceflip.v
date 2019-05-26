Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_congruenceflip : 
   forall A B C D, 
   Cong A B C D ->
   Cong B A D C /\ Cong B A C D /\ Cong A B D C.
Proof.
intros.
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Cong C D D C) by (conclude cn_equalityreverse).
assert (Cong B A C D) by (conclude lemma_congruencetransitive).
assert (Cong A B D C) by (conclude lemma_congruencetransitive).
assert (Cong B A D C) by (conclude lemma_congruencetransitive).
close.
Qed.

End Euclid.


