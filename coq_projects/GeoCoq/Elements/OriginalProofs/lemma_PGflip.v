Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_PGflip : 
   forall A B C D, 
   PG A B C D ->
   PG B A D C.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert (Par B A D C) by (forward_using lemma_parallelflip).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (PG B A D C) by (conclude_def PG ).
close.
Qed.

End Euclid.


