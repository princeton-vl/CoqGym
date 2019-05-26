Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesreflexive : 
   forall A B C, 
   nCol A B C ->
   CongA A B C A B C.
Proof.
intros.
assert (CongA A B C C B A) by (conclude lemma_ABCequalsCBA).
assert (nCol C B A) by (conclude lemma_equalanglesNC).
assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C A B C) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


