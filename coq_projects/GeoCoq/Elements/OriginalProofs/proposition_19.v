Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy.
Require Export GeoCoq.Elements.OriginalProofs.proposition_18.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy1.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_19 : 
   forall A B C, 
   Triangle A B C -> LtA B C A A B C ->
   Lt A B A C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (~ Cong A C A B).
 {
 intro.
 assert (Cong A B A C) by (conclude lemma_congruencesymmetric).
 assert (isosceles A B C) by (conclude_def isosceles ).
 assert (CongA A B C A C B) by (conclude proposition_05).
 assert (CongA A C B A B C) by (conclude lemma_equalanglessymmetric).
 assert (CongA B C A A C B) by (conclude lemma_ABCequalsCBA).
 assert (CongA B C A A B C) by (conclude lemma_equalanglestransitive).
 assert (LtA B C A B C A) by (conclude lemma_angleorderrespectscongruence).
 assert (~ LtA B C A B C A) by (conclude lemma_angletrichotomy).
 contradict.
 }
assert (~ Lt A C A B).
 {
 intro.
 assert (Triangle A C B) by (conclude_def Triangle ).
 assert (LtA C B A A C B) by (conclude proposition_18).
 assert (CongA A B C C B A) by (conclude lemma_ABCequalsCBA).
 assert (LtA A B C A C B) by (conclude lemma_angleorderrespectscongruence2).
 assert (CongA B C A A C B) by (conclude lemma_ABCequalsCBA).
 assert (LtA A B C B C A) by (conclude lemma_angleorderrespectscongruence).
 assert (~ LtA A B C B C A) by (conclude lemma_angletrichotomy).
 contradict.
 }
assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq A C) by (forward_using lemma_angledistinct).
assert (~ ~ Lt A B A C).
 {
 intro.
 assert (Cong A B A C) by (conclude lemma_trichotomy1).
 assert (Cong A C A B) by (conclude lemma_congruencesymmetric).
 contradict.
 }
close.
Qed.

End Euclid.


