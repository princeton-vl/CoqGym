Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_PGrotate : 
   forall A B C D, 
   PG A B C D ->
   PG B C D A.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par B C D A) by (forward_using lemma_parallelflip).
assert (Par B A C D) by (forward_using lemma_parallelflip).
assert (PG B C D A) by (conclude_def PG ).
close.
Qed.

End Euclid.


