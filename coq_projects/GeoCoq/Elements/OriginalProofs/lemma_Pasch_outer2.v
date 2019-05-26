Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_Pasch_outer2 : 
   forall A B C P Q, 
   BetS A P C -> BetS B C Q -> nCol B P A ->
   exists X, BetS A X Q /\ BetS B P X.
Proof.
intros.
assert (~ Col B Q A).
 {
 intro.
 assert (Col A P C) by (conclude_def Col ).
 assert (Col B C Q) by (conclude_def Col ).
 assert (Col B Q C) by (forward_using lemma_collinearorder).
 assert (~ eq Q A).
  {
  intro.
  assert (Col B A C) by (conclude cn_equalitysub).
  assert (Col C A B) by (forward_using lemma_collinearorder).
  assert (Col C A P) by (forward_using lemma_collinearorder).
  assert (neq A C) by (forward_using lemma_betweennotequal).
  assert (neq C A) by (conclude lemma_inequalitysymmetric).
  assert (Col A B P) by (conclude lemma_collinear4).
  assert (Col B P A) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Col B Q C) by (forward_using lemma_collinearorder).
 assert (neq B Q) by (forward_using lemma_betweennotequal).
 assert (Col Q A C) by (conclude lemma_collinear4).
 assert (Col A C Q) by (forward_using lemma_collinearorder).
 assert (Col A C P) by (forward_using lemma_collinearorder).
 assert (neq A C) by (forward_using lemma_betweennotequal).
 assert (Col C Q P) by (conclude lemma_collinear4).
 assert (Col C Q B) by (forward_using lemma_collinearorder).
 assert (neq C Q) by (forward_using lemma_betweennotequal).
 assert (Col Q P B) by (conclude lemma_collinear4).
 assert (Col Q B P) by (forward_using lemma_collinearorder).
 assert (Col Q B A) by (forward_using lemma_collinearorder).
 assert (neq Q B) by (conclude lemma_inequalitysymmetric).
 assert (Col B P A) by (conclude lemma_collinear4).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS A E Q /\ BetS B P E)) by (conclude postulate_Pasch_outer);destruct Tf as [E];spliter.
close.
Qed.

End Euclid.


