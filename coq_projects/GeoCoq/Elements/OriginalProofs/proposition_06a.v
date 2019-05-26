Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_06a : 
   forall A B C, 
   Triangle A B C -> CongA A B C A C B ->
   ~ Lt A C A B.
Proof.
intros.
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq A C) by (forward_using lemma_angledistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (neq B C) by (forward_using lemma_angledistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ Lt A C A B).
 {
 intro.
 assert (Cong B A A B) by (conclude cn_equalityreverse).
 let Tf:=fresh in
 assert (Tf:exists D, (BetS B D A /\ Cong B D A C)) by (conclude proposition_03);destruct Tf as [D];spliter.
 assert (Cong D B A C) by (forward_using lemma_congruenceflip).
 assert (Cong B C B C) by (conclude cn_congruencereflexive).
 assert (Out B A D) by (conclude lemma_ray4).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Out B C C) by (conclude lemma_ray4).
 assert (nCol A B C) by (conclude_def Triangle ).
 assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
 assert (CongA A B C D B C) by (conclude lemma_equalangleshelper).
 assert (CongA D B C A B C) by (conclude lemma_equalanglessymmetric).
 assert (CongA D B C A C B) by (conclude lemma_equalanglestransitive).
 assert (Cong B D C A) by (forward_using lemma_congruenceflip).
 assert (Cong B C C B) by (conclude cn_equalityreverse).
 assert ((Cong D C A B /\ CongA B D C C A B /\ CongA B C D C B A)) by (conclude proposition_04).
 assert (~ Col C B A).
  {
  intro.
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
 assert (CongA B C D A B C) by (conclude lemma_equalanglestransitive).
 assert (CongA B C D A C B) by (conclude lemma_equalanglestransitive).
 assert (~ Col A C B).
  {
  intro.
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA A C B B C A) by (conclude lemma_ABCequalsCBA).
 assert (CongA B C D B C A) by (conclude lemma_equalanglestransitive).
 assert (CongA B C A B C D) by (conclude lemma_equalanglessymmetric).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Out C B B) by (conclude lemma_ray4).
 assert (Out C A A) by (conclude lemma_ray4).
 assert (~ Col B C D).
  {
  intro.
  assert (Col B D A) by (conclude_def Col ).
  assert (Col D B A) by (forward_using lemma_collinearorder).
  assert (Col D B C) by (forward_using lemma_collinearorder).
  assert (neq B D) by (forward_using lemma_betweennotequal).
  assert (neq D B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A C) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA B C D B C D) by (conclude lemma_equalanglesreflexive).
 assert (LtA B C D B C A) by (conclude_def LtA ).
 assert (LtA B C A B C A) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ LtA B C A B C A) by (conclude lemma_angletrichotomy).
 contradict.
 }
close.
Qed.

End Euclid.


