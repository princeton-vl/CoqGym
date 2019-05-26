Require Export GeoCoq.Elements.OriginalProofs.lemma_3_7a.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_3_7b : 
   forall A B C D, 
   BetS A B C -> BetS B C D ->
   BetS A B D.
Proof.
intros.
assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
assert (BetS D C B) by (conclude axiom_betweennesssymmetry).
assert (BetS D B A) by (conclude lemma_3_7a).
assert (BetS A B D) by (conclude axiom_betweennesssymmetry).
close.
Qed.

End Euclid.


