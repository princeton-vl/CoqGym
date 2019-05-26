Require Export GeoCoq.Elements.OriginalProofs.proposition_19.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_legsmallerhypotenuse : 
   forall A B C, 
   Per A B C ->
   Lt A B A C /\ Lt B C A C.
Proof.
intros.
assert (Per C B A) by (conclude lemma_8_2).
let Tf:=fresh in
assert (Tf:exists D, (BetS C B D /\ Cong C B D B /\ Cong C A D A /\ neq B A)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (Triangle A B C) by (conclude_def Triangle ).
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle A C B) by (conclude_def Triangle ).
assert ((LtA C A B A B D /\ LtA B C A A B D)) by (conclude proposition_16).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out B D D) by (conclude lemma_ray4).
assert (Cong B A B A) by (conclude cn_congruencereflexive).
assert (Cong B D B C) by (forward_using lemma_doublereverse).
assert (Cong A D A C) by (forward_using lemma_doublereverse).
assert (~ Col A B D).
 {
 intro.
 assert (Col C B D) by (conclude_def Col ).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (Col D B A) by (forward_using lemma_collinearorder).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B C A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A B D A B C) by (conclude_def CongA ).
assert (CongA A B C A B D) by (conclude lemma_equalanglessymmetric).
assert (LtA B C A A B C) by (conclude lemma_angleorderrespectscongruence).
assert (Lt A B A C) by (conclude proposition_19).
assert (LtA C A B A B C) by (conclude lemma_angleorderrespectscongruence).
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B A C C A B) by (conclude lemma_ABCequalsCBA).
assert (LtA B A C A B C) by (conclude lemma_angleorderrespectscongruence2).
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle C B A) by (conclude_def Triangle ).
assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (LtA B A C C B A) by (conclude lemma_angleorderrespectscongruence).
assert (Lt C B C A) by (conclude proposition_19).
assert (Cong C B B C) by (conclude cn_equalityreverse).
assert (Lt B C C A) by (conclude lemma_lessthancongruence2).
assert (Cong C A A C) by (conclude cn_equalityreverse).
assert (Lt B C A C) by (conclude lemma_lessthancongruence).
close.
Qed.

End Euclid.


