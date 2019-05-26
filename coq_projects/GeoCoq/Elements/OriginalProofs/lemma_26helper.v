Require Export GeoCoq.Elements.OriginalProofs.proposition_16.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_26helper : 
   forall A B C D E F, 
   Triangle A B C -> CongA A B C D E F -> CongA B C A E F D -> Cong A B D E ->
   ~ Lt E F B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq B C) by (forward_using lemma_angledistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (neq A C) by (forward_using lemma_angledistinct).
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ Lt E F B C).
 {
 intro.
 rename_H H;let Tf:=fresh in
 assert (Tf:exists H, (BetS B H C /\ Cong B H E F)) by (conclude_def Lt );destruct Tf as [H];spliter.
 assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Out B A A) by (conclude lemma_ray4).
 assert (Out B C H) by (conclude lemma_ray4).
 assert (CongA A B C A B H) by (conclude lemma_equalangleshelper).
 assert (CongA A B H A B C) by (conclude lemma_equalanglessymmetric).
 assert (CongA A B H D E F) by (conclude lemma_equalanglestransitive).
 assert (Cong B A E D) by (forward_using lemma_congruenceflip).
 assert ((Cong A H D F /\ CongA B A H E D F /\ CongA B H A E F D)) by (conclude proposition_04).
 assert (CongA E F D B C A) by (conclude lemma_equalanglessymmetric).
 assert (~ Col A C H).
  {
  intro.
  assert (Col H C A) by (forward_using lemma_collinearorder).
  assert (Col B H C) by (conclude_def Col ).
  assert (Col H C B) by (forward_using lemma_collinearorder).
  assert (neq H C) by (forward_using lemma_betweennotequal).
  assert (Col C A B) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Triangle A C H) by (conclude_def Triangle ).
 assert (BetS C H B) by (conclude axiom_betweennesssymmetry).
 assert (LtA H C A A H B) by (conclude proposition_16).
 assert (Out C B H) by (conclude lemma_ray4).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Out C A A) by (conclude lemma_ray4).
 assert (~ Col B C A).
  {
  intro.
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA B C A B C A) by (conclude lemma_equalanglesreflexive).
 assert (CongA B C A H C A) by (conclude lemma_equalangleshelper).
 assert (CongA H C A B C A) by (conclude lemma_equalanglessymmetric).
 assert (LtA B C A A H B) by (conclude lemma_angleorderrespectscongruence2).
 assert (LtA E F D A H B) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ Col A H B).
  {
  intro.
  assert (Col H B A) by (forward_using lemma_collinearorder).
  assert (Col B H C) by (conclude_def Col ).
  assert (Col H B C) by (forward_using lemma_collinearorder).
  assert (neq B H) by (forward_using lemma_betweennotequal).
  assert (neq H B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A C) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA A H B B H A) by (conclude lemma_ABCequalsCBA).
 assert (CongA A H B E F D) by (conclude lemma_equalanglestransitive).
 assert (LtA A H B A H B) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ LtA A H B A H B) by (conclude lemma_angletrichotomy).
 contradict.
 }
close.
Qed.

End Euclid.


