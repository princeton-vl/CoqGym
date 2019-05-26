Require Export GeoCoq.Elements.OriginalProofs.lemma_squareparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrectangle.

Section Euclid.

Context `{Ax1:euclidean_euclidean}.

Lemma lemma_squarerectangle : 
   forall A B C D, 
   SQ A B C D ->
   RE A B C D.
Proof.
intros.
assert (PG A B C D) by (conclude lemma_squareparallelogram).
assert (Per D A B) by (conclude_def SQ ).
assert (RE A B C D) by (conclude lemma_PGrectangle).
close.
Qed.

End Euclid.


