Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearbetween : 
   forall A B C D E F H, 
   Col A E B -> Col C F D -> neq A B -> neq C D -> neq A E -> neq F D -> ~ Meet A B C D -> BetS A H D -> Col E F H ->
   BetS E H F.
Proof.
intros.
assert (~ eq H E).
 {
 intro.
 assert (Col A H B) by (conclude cn_equalitysub).
 assert (Col H A B) by (forward_using lemma_collinearorder).
 assert (Col A H D) by (conclude_def Col ).
 assert (Col H A D) by (forward_using lemma_collinearorder).
 assert (neq A H) by (forward_using lemma_betweennotequal).
 assert (neq H A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B D) by (conclude lemma_collinear4).
 assert (eq D D) by (conclude cn_equalityreflexive).
 assert (Col C D D) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ eq H F).
 {
 intro.
 assert (Col A H D) by (conclude_def Col ).
 assert (Col A F D) by (conclude cn_equalitysub).
 assert (Col F D A) by (forward_using lemma_collinearorder).
 assert (Col F D C) by (forward_using lemma_collinearorder).
 assert (Col D A C) by (conclude lemma_collinear4).
 assert (Col C D A) by (forward_using lemma_collinearorder).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ BetS E F H).
 {
 intro.
 assert (BetS D H A) by (conclude axiom_betweennesssymmetry).
 assert (~ Col D A E).
  {
  intro.
  assert (Col E A B) by (forward_using lemma_collinearorder).
  assert (Col E A D) by (forward_using lemma_collinearorder).
  assert (neq E A) by (conclude lemma_inequalitysymmetric).
  assert (Col A B D) by (conclude lemma_collinear4).
  assert (eq D D) by (conclude cn_equalityreflexive).
  assert (Col C D D) by (conclude_def Col ).
  assert (Meet A B C D) by (conclude_def Meet ).
  contradict.
  }
 let Tf:=fresh in
 assert (Tf:exists Q, (BetS E Q A /\ BetS D F Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
 assert (Col E Q A) by (conclude_def Col ).
 assert (Col D F Q) by (conclude_def Col ).
 assert (Col E A Q) by (forward_using lemma_collinearorder).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A Q B) by (conclude lemma_collinear4).
 assert (Col A B Q) by (forward_using lemma_collinearorder).
 assert (Col F D Q) by (forward_using lemma_collinearorder).
 assert (Col F D C) by (forward_using lemma_collinearorder).
 assert (Col D Q C) by (conclude lemma_collinear4).
 assert (Col C D Q) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ BetS F E H).
 {
 intro.
 assert (~ Col A D F).
  {
  intro.
  assert (Col F D C) by (forward_using lemma_collinearorder).
  assert (Col F D A) by (forward_using lemma_collinearorder).
  assert (Col D C A) by (conclude lemma_collinear4).
  assert (Col C D A) by (forward_using lemma_collinearorder).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (Col A B A) by (conclude_def Col ).
  assert (Meet A B C D) by (conclude_def Meet ).
  contradict.
  }
 let Tf:=fresh in
 assert (Tf:exists R, (BetS F R D /\ BetS A E R)) by (conclude postulate_Pasch_outer);destruct Tf as [R];spliter.
 assert (Col F R D) by (conclude_def Col ).
 assert (Col A E R) by (conclude_def Col ).
 assert (Col F D R) by (forward_using lemma_collinearorder).
 assert (Col F D C) by (forward_using lemma_collinearorder).
 assert (Col D R C) by (conclude lemma_collinear4).
 assert (Col C D R) by (forward_using lemma_collinearorder).
 assert (Col E A R) by (forward_using lemma_collinearorder).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A R B) by (conclude lemma_collinear4).
 assert (Col A B R) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ eq E F).
 {
 intro.
 assert (Col C D F) by (forward_using lemma_collinearorder).
 assert (Col A B E) by (forward_using lemma_collinearorder).
 assert (Col A B F) by (conclude cn_equalitysub).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert ((eq E F \/ eq E H \/ eq F H \/ BetS F E H \/ BetS E F H \/ BetS E H F)) by (conclude_def Col ).
assert (BetS E H F).
by cases on (eq E F \/ eq E H \/ eq F H \/ BetS F E H \/ BetS E F H \/ BetS E H F).
{
 assert (~ ~ BetS E H F).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS E H F).
  {
  intro.
  assert (neq E H) by (conclude lemma_inequalitysymmetric).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS E H F).
  {
  intro.
  assert (neq F H) by (conclude lemma_inequalitysymmetric).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS E H F).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS E H F).
  {
  intro.
  contradict.
  }
 close.
 }
{
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


