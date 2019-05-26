Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_3_6a : 
   forall A B C D, 
   BetS A B C -> BetS A C D ->
   BetS B C D.
Proof.
intros.
assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
assert (BetS D C A) by (conclude axiom_betweennesssymmetry).
assert (BetS D C B) by (conclude axiom_innertransitivity).
assert (BetS B C D) by (conclude axiom_betweennesssymmetry).
close.
Qed.

End Euclid.

