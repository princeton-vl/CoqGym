Require Export GeoCoq.Elements.OriginalProofs.proposition_16.
Require Export GeoCoq.Elements.OriginalProofs.proposition_05.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleordertransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_18 : 
   forall A B C, 
   Triangle A B C -> Lt A B A C ->
   LtA B C A A B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (Cong A C A C) by (conclude cn_congruencereflexive).
let Tf:=fresh in
assert (Tf:exists D, (BetS A D C /\ Cong A D A B)) by (conclude proposition_03);destruct Tf as [D];spliter.
assert (~ Col B C D).
 {
 intro.
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (Col A D C) by (conclude_def Col ).
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (neq D C) by (forward_using lemma_betweennotequal).
 assert (Col C B A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle B C D) by (conclude_def Triangle ).
assert (BetS C D A) by (conclude axiom_betweennesssymmetry).
assert (LtA D C B B D A) by (conclude proposition_16).
assert (~ eq B C).
 {
 intro.
 assert (Col B C D) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ Col A D B).
 {
 intro.
 assert (Col A D C) by (conclude_def Col ).
 assert (Col D A C) by (forward_using lemma_collinearorder).
 assert (Col D A B) by (forward_using lemma_collinearorder).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (neq D A) by (conclude lemma_inequalitysymmetric).
 assert (Col A C B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle A D B) by (conclude_def Triangle ).
assert (isosceles A D B) by (conclude_def isosceles ).
assert (CongA A D B A B D) by (conclude proposition_05).
assert (Out C A D) by (conclude lemma_ray4).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Out C B B) by (conclude lemma_ray4).
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A C B A C B) by (conclude lemma_equalanglesreflexive).
assert (CongA A C B D C B) by (conclude lemma_equalangleshelper).
assert (LtA A C B B D A) by (conclude lemma_angleorderrespectscongruence2).
assert (CongA A D B B D A) by (conclude lemma_ABCequalsCBA).
assert (LtA A C B A D B) by (conclude lemma_angleorderrespectscongruence).
assert (CongA A B D A D B) by (conclude lemma_equalanglessymmetric).
assert (LtA A C B A B D) by (conclude lemma_angleorderrespectscongruence).
assert (~ Col B C A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B C A A C B) by (conclude lemma_ABCequalsCBA).
assert (LtA B C A A B D) by (conclude lemma_angleorderrespectscongruence2).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (~ Col A B D).
 {
 intro.
 assert (Col A D B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A B D A B D) by (conclude lemma_equalanglesreflexive).
assert (LtA A B D A B C) by (conclude_def LtA ).
assert (LtA B C A A B C) by (conclude lemma_angleordertransitive).
close.
Qed.

End Euclid.


