Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_twolines2 : 
   forall A B C D P Q, 
   neq A B -> neq C D -> Col P A B -> Col P C D -> Col Q A B -> Col Q C D -> ~ (Col A C D /\ Col B C D) ->
   eq P Q.
Proof.
intros.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (~ neq P Q).
 {
 intro.
 assert (Col D C P) by (forward_using lemma_collinearorder).
 assert (Col D C Q) by (forward_using lemma_collinearorder).
 assert (Col C P Q) by (conclude lemma_collinear4).
 assert (Col A B P) by (forward_using lemma_collinearorder).
 assert (Col A B Q) by (forward_using lemma_collinearorder).
 assert (Col B P Q) by (conclude lemma_collinear4).
 assert (Col P Q B) by (forward_using lemma_collinearorder).
 assert (Col P Q C) by (forward_using lemma_collinearorder).
 assert (Col Q C B) by (conclude lemma_collinear4).
 assert (Col Q C D) by (forward_using lemma_collinearorder).
 assert (~ eq Q C).
  {
  intro.
  assert (Col C P D) by (forward_using lemma_collinearorder).
  assert (Col Q P B) by (forward_using lemma_collinearorder).
  assert (Col B A Q) by (forward_using lemma_collinearorder).
  assert (Col B A P) by (forward_using lemma_collinearorder).
  assert (Col A Q P) by (conclude lemma_collinear4).
  assert (Col Q P A) by (forward_using lemma_collinearorder).
  assert (Col C P B) by (conclude cn_equalitysub).
  assert (Col C P A) by (conclude cn_equalitysub).
  assert (Col P C A) by (forward_using lemma_collinearorder).
  assert (Col P C B) by (forward_using lemma_collinearorder).
  assert (Col P C D) by (forward_using lemma_collinearorder).
  assert (~ eq P C).
   {
   intro.
   assert (eq P Q) by (conclude cn_equalitysub).
   contradict.
   }
  assert (Col C D A) by (conclude lemma_collinear4).
  assert (Col C D B) by (conclude lemma_collinear4).
  assert (Col A C D) by (forward_using lemma_collinearorder).
  assert (Col B C D) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Col C B D) by (conclude lemma_collinear4).
 assert (Col B C D) by (forward_using lemma_collinearorder).
 assert (~ eq B A).
  {
  intro.
  assert (eq A B) by (conclude lemma_equalitysymmetric).
  contradict.
  }
 assert (Col B A P) by (forward_using lemma_collinearorder).
 assert (Col B A Q) by (forward_using lemma_collinearorder).
 assert (Col A P Q) by (conclude lemma_collinear4).
 assert (Col P Q A) by (forward_using lemma_collinearorder).
 assert (Col P Q C) by (forward_using lemma_collinearorder).
 assert (Col Q C A) by (conclude lemma_collinear4).
 assert (Col Q C D) by (forward_using lemma_collinearorder).
 assert (Col C A D) by (conclude lemma_collinear4).
 assert (Col A C D) by (forward_using lemma_collinearorder).
 contradict.
 }
close.
Qed.

End Euclid.


