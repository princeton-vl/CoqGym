Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesflip : 
   forall A B C D E F, 
   CongA A B C D E F ->
   CongA C B A F E D.
Proof.
intros.
assert (nCol D E F) by (conclude lemma_equalanglesNC).
assert (CongA D E F A B C) by (conclude lemma_equalanglessymmetric).
assert (nCol A B C) by (conclude lemma_equalanglesNC).
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (CongA C B A D E F) by (conclude lemma_equalanglestransitive).
assert (CongA D E F F E D) by (conclude lemma_ABCequalsCBA).
assert (CongA C B A F E D) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


