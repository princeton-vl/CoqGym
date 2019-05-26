Require Export GeoCoq.Elements.OriginalProofs.proposition_06a.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy1.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_06 : 
   forall A B C, 
   Triangle A B C -> CongA A B C A C B ->
   Cong A B A C.
Proof.
intros.
assert (~ Lt A C A B) by (conclude proposition_06a).
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle A C B) by (conclude_def Triangle ).
assert (CongA A C B A B C) by (conclude lemma_equalanglessymmetric).
assert (~ Lt A B A C) by (conclude proposition_06a).
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq A C) by (forward_using lemma_angledistinct).
assert (Cong A B A C) by (conclude lemma_trichotomy1).
close.
Qed.

End Euclid.


