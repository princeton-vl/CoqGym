Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelbetween : 
   forall B H K L M, 
   BetS H B K -> Par M B H L -> Col L M K ->
   BetS L M K.
Proof.
intros.
assert (~ Meet M B H L) by (conclude_def Par ).
assert (nCol M B H) by (forward_using lemma_parallelNC).
assert (nCol M H L) by (forward_using lemma_parallelNC).
assert (neq M B) by (forward_using lemma_NCdistinct).
assert (neq H L) by (forward_using lemma_NCdistinct).
assert (nCol M L H) by (forward_using lemma_NCorder).
assert (Col M L K) by (forward_using lemma_collinearorder).
assert (Col H B K) by (conclude_def Col ).
assert (eq M M) by (conclude cn_equalityreflexive).
assert (eq L L) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (~ eq M K).
 {
 intro.
 assert (Col H B M) by (conclude cn_equalitysub).
 assert (Col M B H) by (forward_using lemma_collinearorder).
 assert (Col H L H) by (conclude_def Col ).
 assert (Meet M B H L) by (conclude_def Meet ).
 contradict.
 }
assert (nCol M L H) by (forward_using lemma_NCorder).
assert (Col M L M) by (conclude_def Col ).
assert (nCol M K H) by (conclude lemma_NChelper).
assert (nCol H M K) by (forward_using lemma_NCorder).
assert ((eq L M \/ eq L K \/ eq M K \/ BetS M L K \/ BetS L M K \/ BetS L K M)) by (conclude_def Col ).
assert (BetS L M K).
by cases on (eq L M \/ eq L K \/ eq M K \/ BetS M L K \/ BetS L M K \/ BetS L K M).
{
 assert (~ ~ BetS L M K).
  {
  intro.
  assert (Col M B M) by (conclude_def Col ).
  assert (Col H L L) by (conclude_def Col ).
  assert (Col H L M) by (conclude cn_equalitysub).
  assert (Meet M B H L) by (conclude_def Meet ).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS L M K).
  {
  intro.
  assert (Col H B L) by (conclude cn_equalitysub).
  assert (Col H L B) by (forward_using lemma_collinearorder).
  assert (Col M B B) by (conclude_def Col ).
  assert (Meet M B H L) by (conclude_def Meet ).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS L M K).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS L M K).
  {
  intro.
  assert (nCol H K M) by (forward_using lemma_NCorder).
  let Tf:=fresh in
  assert (Tf:exists E, (BetS H E L /\ BetS M E B)) by (conclude postulate_Pasch_inner);destruct Tf as [E];spliter.
  assert (Col H E L) by (conclude_def Col ).
  assert (Col M E B) by (conclude_def Col ).
  assert (Col H L E) by (forward_using lemma_collinearorder).
  assert (Col M B E) by (forward_using lemma_collinearorder).
  assert (Meet M B H L) by (conclude_def Meet ).
  contradict.
  }
 close.
 }
{
 close.
 }
{
 assert (~ ~ BetS L M K).
  {
  intro.
  assert (BetS M K L) by (conclude axiom_betweennesssymmetry).
  let Tf:=fresh in
  assert (Tf:exists E, (BetS H E L /\ BetS M B E)) by (conclude postulate_Pasch_outer);destruct Tf as [E];spliter.
  assert (Col H E L) by (conclude_def Col ).
  assert (Col M B E) by (conclude_def Col ).
  assert (Col H L E) by (forward_using lemma_collinearorder).
  assert (Meet M B H L) by (conclude_def Meet ).
  contradict.
  }
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


