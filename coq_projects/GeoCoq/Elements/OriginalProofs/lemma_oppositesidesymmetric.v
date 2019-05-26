Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_oppositesidesymmetric : 
   forall A B P Q, 
   TS P A B Q ->
   TS Q A B P.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists R, (BetS P R Q /\ Col A B R /\ nCol A B P)) by (conclude_def TS );destruct Tf as [R];spliter.
assert (~ eq A B).
 {
 intro.
 assert (Col A B P) by (conclude_def Col ).
 contradict.
 }
assert (BetS Q R P) by (conclude axiom_betweennesssymmetry).
assert (~ Col A B Q).
 {
 intro.
 assert (Col P R Q) by (conclude_def Col ).
 assert (Col B Q R) by (conclude lemma_collinear4).
 assert (Col Q R B) by (forward_using lemma_collinearorder).
 assert (Col Q R P) by (forward_using lemma_collinearorder).
 assert (neq Q R) by (forward_using lemma_betweennotequal).
 assert (Col R B P) by (conclude lemma_collinear4).
 assert (Col R B A) by (forward_using lemma_collinearorder).
 assert (Col A P B).
 by cases on (eq R B \/ neq R B).
 {
  assert (Col P B Q) by (conclude cn_equalitysub).
  assert (Col B Q P) by (forward_using lemma_collinearorder).
  assert (Col B Q A) by (forward_using lemma_collinearorder).
  assert (neq R Q) by (forward_using lemma_betweennotequal).
  assert (neq B Q) by (conclude cn_equalitysub).
  assert (Col Q P A) by (conclude lemma_collinear4).
  assert (Col Q P B) by (forward_using lemma_collinearorder).
  assert (neq P Q) by (forward_using lemma_betweennotequal).
  assert (neq Q P) by (conclude lemma_inequalitysymmetric).
  assert (Col P A B) by (conclude lemma_collinear4).
  assert (Col A P B) by (forward_using lemma_collinearorder).
  close.
  }
 {
  assert (Col B P A) by (conclude lemma_collinear4).
  assert (Col A P B) by (forward_using lemma_collinearorder).
  close.
  }
(** cases *)
 assert (Col A B P) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (TS Q A B P) by (conclude_def TS ).
close.
Qed.

End Euclid.


