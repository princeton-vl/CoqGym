Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_PGsymmetric : 
   forall A B C D, 
   PG A B C D ->
   PG C D A B.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert (Par C D A B) by (conclude lemma_parallelsymmetric).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par C B D A) by (forward_using lemma_parallelflip).
assert (PG C D A B) by (conclude_def PG ).
close.
Qed.

End Euclid.


