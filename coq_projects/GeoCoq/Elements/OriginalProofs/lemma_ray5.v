Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ray5 : 
   forall A B C, 
   Out A B C ->
   Out A C B.
Proof.
intros.
assert ((BetS A C B \/ eq B C \/ BetS A B C)) by (conclude lemma_ray1).
assert (neq A C) by (conclude lemma_raystrict).
assert (Out A C B) by (conclude lemma_ray4).
close.
Qed.

End Euclid.


