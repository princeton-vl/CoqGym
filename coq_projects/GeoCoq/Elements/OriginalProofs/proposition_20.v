Require Export GeoCoq.Elements.OriginalProofs.proposition_19.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_20 : 
   forall A B C, 
   Triangle A B C ->
   TG B A A C B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq B A).
 {
 intro.
 assert (Col B A C) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ eq C A).
 {
 intro.
 assert (Col B C A) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists D, (BetS B A D /\ Cong A D C A)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (neq D B) by (conclude lemma_inequalitysymmetric).
assert (Cong A D A C) by (forward_using lemma_congruenceflip).
assert (~ Col A D C).
 {
 intro.
 assert (Col B A D) by (conclude_def Col ).
 assert (Col D A B) by (forward_using lemma_collinearorder).
 assert (Col D A C) by (forward_using lemma_collinearorder).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (neq D A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 contradict.
 }
assert (~ eq D C).
 {
 intro.
 assert (Col A D C) by (conclude_def Col ).
 contradict.
 }
assert (Triangle A D C) by (conclude_def Triangle ).
assert (isosceles A D C) by (conclude_def isosceles ).
assert (CongA A D C A C D) by (conclude proposition_05).
assert (~ Col A C D).
 {
 intro.
 assert (Col A D C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A C D D C A) by (conclude lemma_ABCequalsCBA).
assert (CongA A D C D C A) by (conclude lemma_equalanglestransitive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (~ eq C D).
 {
 intro.
 assert (Col A C D) by (conclude_def Col ).
 contradict.
 }
assert (Out C D D) by (conclude lemma_ray4).
assert (Out C B B) by (conclude lemma_ray4).
assert (BetS D A B) by (conclude axiom_betweennesssymmetry).
assert (LtA A D C D C B) by (conclude_def LtA ).
assert (Out D A B) by (conclude lemma_ray4).
assert (Out D C C) by (conclude lemma_ray4).
assert (Out D B B) by (conclude lemma_ray4).
assert (Cong D B D B) by (conclude cn_congruencereflexive).
assert (Cong D C D C) by (conclude cn_congruencereflexive).
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (CongA A D C B D C) by (conclude_def CongA ).
assert (CongA B D C A D C) by (conclude lemma_equalanglessymmetric).
assert (LtA B D C D C B) by (conclude lemma_angleorderrespectscongruence2).
assert (~ Col B C D).
 {
 intro.
 assert (Col B A D) by (conclude_def Col ).
 assert (Col D B A) by (forward_using lemma_collinearorder).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col C D B).
 {
 intro.
 assert (Col B C D) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA C D B B D C) by (conclude lemma_ABCequalsCBA).
assert (CongA B C D D C B) by (conclude lemma_ABCequalsCBA).
assert (LtA C D B D C B) by (conclude lemma_angleorderrespectscongruence2).
assert (LtA C D B B C D) by (conclude lemma_angleorderrespectscongruence).
assert (Triangle B C D) by (conclude_def Triangle ).
assert (Lt B C B D) by (conclude proposition_19).
assert (TG B A A C B C) by (conclude_def TG ).
close.
Qed.

End Euclid.


