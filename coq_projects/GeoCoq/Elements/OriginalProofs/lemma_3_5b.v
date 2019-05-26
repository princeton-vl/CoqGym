Require Export GeoCoq.Elements.OriginalProofs.lemma_3_7a.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_3_5b : 
   forall A B C D, 
   BetS A B D -> BetS B C D ->
   BetS A C D.
Proof.
intros.
assert (BetS A B C) by (conclude axiom_innertransitivity).
assert (BetS A C D) by (conclude lemma_3_7a).
close.
Qed.

End Euclid.


