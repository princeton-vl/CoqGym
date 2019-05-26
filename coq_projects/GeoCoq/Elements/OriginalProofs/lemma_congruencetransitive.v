Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_congruencetransitive : 
   forall A B C D E F, 
   Cong A B C D -> Cong C D E F ->
   Cong A B E F.
Proof.
intros.
assert (Cong C D A B) by (conclude lemma_congruencesymmetric).
assert (Cong A B E F) by (conclude cn_congruencetransitive).
close.
Qed.

End Euclid.


