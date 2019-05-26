Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_08 : 
   forall A B C D E F, 
   Triangle A B C -> Triangle D E F -> Cong A B D E -> Cong A C D F -> Cong B C E F ->
   CongA B A C E D F /\ CongA C B A F E D /\ CongA A C B D F E.
Proof.
intros.
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (nCol A B C) by (conclude_def Triangle ).
assert (nCol D E F) by (conclude_def Triangle ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ eq D E).
 {
 intro.
 assert (Col D E F) by (conclude_def Col ).
 contradict.
 }
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ eq D F).
 {
 intro.
 assert (Col D E F) by (conclude_def Col ).
 contradict.
 }
assert (neq F D) by (conclude lemma_inequalitysymmetric).
assert (~ eq E F).
 {
 intro.
 assert (Col D E F) by (conclude_def Col ).
 contradict.
 }
assert (neq F E) by (conclude lemma_inequalitysymmetric).
assert (Out D E E) by (conclude lemma_ray4).
assert (Out D F F) by (conclude lemma_ray4).
assert (Out A B B) by (conclude lemma_ray4).
assert (Out A C C) by (conclude lemma_ray4).
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B A C E D F) by (conclude_def CongA ).
assert (Cong B A E D) by (forward_using lemma_congruenceflip).
assert (Cong C A F D) by (forward_using lemma_congruenceflip).
assert (Out E F F) by (conclude lemma_ray4).
assert (Out E D D) by (conclude lemma_ray4).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA C B A F E D) by (conclude_def CongA ).
assert (Cong C A F D) by (forward_using lemma_congruenceflip).
assert (Cong C B F E) by (forward_using lemma_congruenceflip).
assert (Out F D D) by (conclude lemma_ray4).
assert (Out F E E) by (conclude lemma_ray4).
assert (Out C A A) by (conclude lemma_ray4).
assert (Out C B B) by (conclude lemma_ray4).
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A C B D F E) by (conclude_def CongA ).
close.
Qed.

End Euclid.


