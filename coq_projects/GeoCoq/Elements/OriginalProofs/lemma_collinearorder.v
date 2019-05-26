Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear1.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_collinearorder : 
   forall A B C, 
   Col A B C ->
   Col B A C /\ Col B C A /\ Col C A B /\ Col A C B /\ Col C B A.
Proof.
intros.
assert (Col B C A) by (conclude lemma_collinear2).
assert (Col C A B) by (conclude lemma_collinear2).
assert (Col B A C) by (conclude lemma_collinear1).
assert (Col A C B) by (conclude lemma_collinear2).
assert (Col C B A) by (conclude lemma_collinear2).
close.
Qed.

End Euclid.


