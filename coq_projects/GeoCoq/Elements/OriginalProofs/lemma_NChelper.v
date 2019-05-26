Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear5.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_NChelper : 
   forall A B C P Q, 
   nCol A B C -> Col A B P -> Col A B Q -> neq P Q ->
   nCol P Q C.
Proof.
intros.
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (Col B P Q) by (conclude lemma_collinear4).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Col B A P) by (forward_using lemma_collinearorder).
assert (Col B A Q) by (forward_using lemma_collinearorder).
assert (Col A P Q) by (conclude lemma_collinear4).
assert (Col P Q A) by (forward_using lemma_collinearorder).
assert (Col P Q B) by (forward_using lemma_collinearorder).
assert (~ Col P Q C).
 {
 intro.
 assert (Col A B C) by (conclude lemma_collinear5).
 contradict.
 }
close.
Qed.

End Euclid.


