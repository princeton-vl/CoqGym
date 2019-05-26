Require Export GeoCoq.Elements.OriginalProofs.lemma_3_5b.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_3_6b : 
   forall A B C D, 
   BetS A B C -> BetS A C D ->
   BetS A B D.
Proof.
intros.
assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
assert (BetS D C A) by (conclude axiom_betweennesssymmetry).
assert (BetS D B A) by (conclude lemma_3_5b).
assert (BetS A B D) by (conclude axiom_betweennesssymmetry).
close.
Qed.

End Euclid.


