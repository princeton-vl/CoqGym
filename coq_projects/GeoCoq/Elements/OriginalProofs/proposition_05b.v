Require Export GeoCoq.Elements.OriginalProofs.proposition_05.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_05b : 
   forall A B C F G, 
   isosceles A B C -> BetS A B F -> BetS A C G ->
   CongA C B F B C G.
Proof.
intros.
assert (CongA A B C A C B) by (conclude proposition_05).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (nCol A C B) by (conclude lemma_equalanglesNC).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (Col A C B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Out B C C) by (conclude lemma_ray4).
assert (Supp A B C C F) by (conclude_def Supp ).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Out C B B) by (conclude lemma_ray4).
assert (Supp A C B B G) by (conclude_def Supp ).
assert (CongA C B F B C G) by (conclude lemma_supplements).
close.
Qed.

End Euclid.


