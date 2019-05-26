Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_9_5a : 
   forall A B C P Q R, 
   TS P A B C -> BetS R P Q -> nCol R Q C -> Col A B R ->
   TS Q A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists S, (BetS P S C /\ Col A B S /\ nCol A B P)) by (conclude_def TS );destruct Tf as [S];spliter.
assert (BetS C S P) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists F, (BetS C F Q /\ BetS R S F)) by (conclude postulate_Pasch_outer);destruct Tf as [F];spliter.
assert (Col R S F) by (conclude_def Col ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B P) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Col B R S) by (conclude lemma_collinear4).
assert (Col R S B) by (forward_using lemma_collinearorder).
assert (neq R S) by (forward_using lemma_betweennotequal).
assert (Col S F B) by (conclude lemma_collinear4).
assert (Col S B A) by (forward_using lemma_collinearorder).
assert (Col S B F) by (forward_using lemma_collinearorder).
assert (Col A B F).
by cases on (eq S B \/ neq S B).
{
 assert (Col B A S) by (forward_using lemma_collinearorder).
 assert (Col R S F) by (conclude_def Col ).
 assert (Col R B F) by (conclude cn_equalitysub).
 assert (Col R B A) by (forward_using lemma_collinearorder).
 assert (~ eq R B).
  {
  intro.
  assert (eq R S) by (conclude cn_equalitysub).
  assert (neq R S) by (forward_using lemma_betweennotequal).
  assert (neq R B) by (conclude cn_equalitysub).
  contradict.
  }
 assert (Col B F A) by (conclude lemma_collinear4).
 assert (Col A B F) by (forward_using lemma_collinearorder).
 close.
 }
{
 assert (Col B A F) by (conclude lemma_collinear4).
 assert (Col A B F) by (forward_using lemma_collinearorder).
 close.
 }
(** cases *)
assert (~ Col A B Q).
 {
 intro.
 assert (Col B Q R) by (conclude lemma_collinear4).
 assert (Col B R Q) by (forward_using lemma_collinearorder).
 assert (Col B R F) by (conclude lemma_collinear4).
 assert (Col R Q F).
 by cases on (eq B R \/ neq B R).
 {
  assert (~ eq A R).
   {
   intro.
   assert (eq A B) by (conclude cn_equalitysub).
   contradict.
   }
  assert (Col B A R) by (forward_using lemma_collinearorder).
  assert (Col B A F) by (forward_using lemma_collinearorder).
  assert (Col A R F) by (conclude lemma_collinear4).
  assert (Col B A Q) by (forward_using lemma_collinearorder).
  assert (Col B A R) by (forward_using lemma_collinearorder).
  assert (Col A R Q) by (conclude lemma_collinear4).
  assert (Col R F Q) by (conclude lemma_collinear4).
  assert (Col R Q F) by (forward_using lemma_collinearorder).
  close.
  }
 {
  assert (Col R Q F) by (conclude lemma_collinear4).
  close.
  }
(** cases *)
 assert (Col F Q R) by (forward_using lemma_collinearorder).
 assert (Col C F Q) by (conclude_def Col ).
 assert (Col F Q C) by (forward_using lemma_collinearorder).
 assert (neq F Q) by (forward_using lemma_betweennotequal).
 assert (Col Q R C) by (conclude lemma_collinear4).
 assert (Col R Q C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (BetS Q F C) by (conclude axiom_betweennesssymmetry).
assert (TS Q A B C) by (conclude_def TS ).
close.
Qed.

End Euclid.


