Require Export GeoCoq.Elements.OriginalProofs.lemma_ray5.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_supplementsymmetric : 
   forall A B C D E, 
   Supp A B C E D ->
   Supp D B E C A.
Proof.
intros.
assert ((Out B C E /\ BetS A B D)) by (conclude_def Supp ).
assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
assert (Out B E C) by (conclude lemma_ray5).
assert (Supp D B E C A) by (conclude_def Supp ).
close.
Qed.

End Euclid.


