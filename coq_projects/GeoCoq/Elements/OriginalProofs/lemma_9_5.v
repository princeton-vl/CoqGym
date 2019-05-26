Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5a.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5b.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_9_5 : 
   forall A B C P Q R, 
   TS P A B C -> Out R Q P -> Col A B R ->
   TS Q A B C.
Proof.
intros.
assert ((BetS R P Q \/ eq Q P \/ BetS R Q P)) by (conclude lemma_ray1).
assert (TS Q A B C).
by cases on (nCol C P R \/ Col C P R).
{
 assert (TS Q A B C).
 by cases on (BetS R P Q \/ eq Q P \/ BetS R Q P).
 {
  assert (~ Col R Q C).
   {
   intro.
   assert (Col Q R C) by (forward_using lemma_collinearorder).
   assert (Col R Q P) by (conclude lemma_rayimpliescollinear).
   assert (Col Q R P) by (forward_using lemma_collinearorder).
   assert (neq R Q) by (forward_using lemma_betweennotequal).
   assert (neq Q R) by (conclude lemma_inequalitysymmetric).
   assert (Col R C P) by (conclude lemma_collinear4).
   assert (Col C P R) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (TS Q A B C) by (conclude lemma_9_5a).
  close.
  }
 {
  assert (TS Q A B C) by (conclude cn_equalitysub).
  close.
  }
 {
  assert (TS Q A B C) by (conclude lemma_9_5b).
  close.
  }
(** cases *)
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists L, (BetS P L C /\ Col A B L /\ nCol A B P)) by (conclude_def TS );destruct Tf as [L];spliter.
 assert (Col R Q P) by (conclude lemma_rayimpliescollinear).
 assert (Col P C L) by (conclude_def Col ).
 assert (Col C P L) by (forward_using lemma_collinearorder).
 assert (neq P C) by (forward_using lemma_betweennotequal).
 assert (neq C P) by (conclude lemma_inequalitysymmetric).
 assert (Col P L R) by (conclude lemma_collinear4).
 assert (~ eq A B).
  {
  intro.
  assert (Col A B P) by (conclude_def Col ).
  contradict.
  }
 assert (Col B L R) by (conclude lemma_collinear4).
 assert (Col L R P) by (forward_using lemma_collinearorder).
 assert (Col L R B) by (forward_using lemma_collinearorder).
 assert (~ neq L R).
  {
  intro.
  assert (Col R P B) by (conclude lemma_collinear4).
  assert (Col R B P) by (forward_using lemma_collinearorder).
  assert (Col R B A) by (forward_using lemma_collinearorder).
  assert (~ neq R B).
   {
   intro.
   assert (Col B P A) by (conclude lemma_collinear4).
   assert (Col A B P) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (neq R A) by (conclude cn_equalitysub).
  assert (Col B A R) by (forward_using lemma_collinearorder).
  assert (Col B A L) by (forward_using lemma_collinearorder).
  assert (Col A L R) by (conclude lemma_collinear4).
  assert (Col L R A) by (forward_using lemma_collinearorder).
  assert (Col R P A) by (conclude lemma_collinear4).
  assert (Col R A P) by (forward_using lemma_collinearorder).
  assert (Col R A B) by (forward_using lemma_collinearorder).
  assert (Col A P B) by (conclude lemma_collinear4).
  assert (Col A B P) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (BetS P R C) by (conclude cn_equalitysub).
 assert (BetS C R P) by (conclude axiom_betweennesssymmetry).
 assert (BetS C R Q).
 by cases on (BetS R P Q \/ eq Q P \/ BetS R Q P).
 {
  assert (BetS C R Q) by (conclude lemma_3_7b).
  close.
  }
 {
  assert (BetS C R Q) by (conclude cn_equalitysub).
  close.
  }
 {
  assert (BetS C R Q) by (conclude axiom_innertransitivity).
  close.
  }
(** cases *)
 assert (BetS Q R C) by (conclude axiom_betweennesssymmetry).
 assert (~ Col A B Q).
  {
  intro.
  assert (Col Q R C) by (conclude_def Col ).
  assert (Col B Q R) by (conclude lemma_collinear4).
  assert (Col R B Q) by (forward_using lemma_collinearorder).
  assert (Col R Q P) by (conclude lemma_rayimpliescollinear).
  assert (Col Q R B) by (forward_using lemma_collinearorder).
  assert (Col Q R P) by (forward_using lemma_collinearorder).
  assert (neq Q R) by (forward_using lemma_betweennotequal).
  assert (Col R B P) by (conclude lemma_collinear4).
  assert (Col R B A) by (forward_using lemma_collinearorder).
  assert (~ neq R B).
   {
   intro.
   assert (Col B P A) by (conclude lemma_collinear4).
   assert (Col A B P) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (neq R A) by (conclude cn_equalitysub).
  assert (Col B A R) by (forward_using lemma_collinearorder).
  assert (Col B A Q) by (forward_using lemma_collinearorder).
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (Col A Q R) by (conclude lemma_collinear4).
  assert (Col R A Q) by (forward_using lemma_collinearorder).
  assert (Col Q R A) by (forward_using lemma_collinearorder).
  assert (Col R A P) by (conclude lemma_collinear4).
  assert (Col R A B) by (forward_using lemma_collinearorder).
  assert (Col A P B) by (conclude lemma_collinear4).
  assert (Col A B P) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (TS Q A B C) by (conclude_def TS ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


