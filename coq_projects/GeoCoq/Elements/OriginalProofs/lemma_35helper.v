Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.

Section Euclid.

Context `{Ax1:euclidean_euclidean}.

Lemma lemma_35helper : 
   forall A B C D E F, 
   PG A B C D -> PG E B C F -> BetS A D F -> Col A E F ->
   BetS A E F.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E B C F /\ Par E F B C)) by (conclude_def PG ).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (Par E B F C) by (forward_using lemma_parallelflip).
assert (Cong A D B C) by (forward_using proposition_34).
assert (Cong E F B C) by (forward_using proposition_34).
assert (Cong B C E F) by (conclude lemma_congruencesymmetric).
assert (Cong A D E F) by (conclude lemma_congruencetransitive).
assert (Col A D F) by (conclude_def Col ).
assert (Col F A E) by (forward_using lemma_collinearorder).
assert (Col F A D) by (forward_using lemma_collinearorder).
assert (neq A F) by (forward_using lemma_betweennotequal).
assert (neq F A) by (conclude lemma_inequalitysymmetric).
assert (Col A E D) by (conclude lemma_collinear4).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
assert (BetS D M B) by (conclude axiom_betweennesssymmetry).
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (BetS B M D) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists m, (BetS E m C /\ BetS B m F)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
assert (BetS F m B) by (conclude axiom_betweennesssymmetry).
assert (BetS B m F) by (conclude axiom_betweennesssymmetry).
assert (nCol A D B) by (forward_using lemma_parallelNC).
assert (Col A D F) by (conclude_def Col ).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A D A) by (conclude_def Col ).
assert (nCol A F B) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists Q, (BetS B Q F /\ BetS A M Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
assert (Col A M Q) by (conclude_def Col ).
assert (Col A M C) by (conclude_def Col ).
assert (Col M A Q) by (forward_using lemma_collinearorder).
assert (Col M A C) by (forward_using lemma_collinearorder).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (neq M A) by (conclude lemma_inequalitysymmetric).
assert (Col A Q C) by (conclude lemma_collinear4).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col F A A) by (conclude_def Col ).
assert (Col C C B) by (conclude_def Col ).
assert (neq A F) by (forward_using lemma_betweennotequal).
assert (neq F A) by (conclude lemma_inequalitysymmetric).
assert (neq B C) by (conclude_def Par ).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ Meet F A C B).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists p, (neq F A /\ neq C B /\ Col F A p /\ Col C B p)) by (conclude_def Meet );destruct Tf as [p];spliter.
 assert (Col A D F) by (conclude_def Col ).
 assert (Col F A D) by (forward_using lemma_collinearorder).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (Col A D p) by (conclude lemma_collinear4).
 assert (Col B C p) by (forward_using lemma_collinearorder).
 assert (Meet A D B C) by (conclude_def Meet ).
 assert (~ Meet A D B C) by (conclude_def Par ).
 contradict.
 }
assert (BetS F Q B) by (conclude axiom_betweennesssymmetry).
assert (~ Meet A D B C) by (conclude_def Par ).
assert (Col A C Q) by (forward_using lemma_collinearorder).
assert (BetS A Q C) by (conclude lemma_collinearbetween).
assert (BetS C Q A) by (conclude axiom_betweennesssymmetry).
assert (~ eq A E).
 {
 intro.
 assert (Cong A F A F) by (conclude cn_congruencereflexive).
 assert (Cong A F E F) by (conclude cn_equalitysub).
 assert (Cong E F A D) by (conclude lemma_congruencesymmetric).
 assert (Cong A F A D) by (conclude lemma_congruencetransitive).
 assert (Cong A D A F) by (conclude lemma_congruencesymmetric).
 assert (Cong A D A D) by (conclude cn_congruencereflexive).
 assert (Lt A D A F) by (conclude_def Lt ).
 assert (Lt A F A F) by (conclude lemma_lessthancongruence2).
 assert (~ Lt A F A F) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (~ BetS A F E).
 {
 intro.
 assert (BetS E F A) by (conclude axiom_betweennesssymmetry).
 assert (nCol A D C) by (forward_using lemma_parallelNC).
 assert (Col A D E) by (forward_using lemma_collinearorder).
 assert (nCol A E C) by (conclude lemma_NChelper).
 assert (nCol C A E) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists r, (BetS C r F /\ BetS E r Q)) by (conclude postulate_Pasch_inner);destruct Tf as [r];spliter.
 assert (BetS Q r E) by (conclude axiom_betweennesssymmetry).
 assert (nCol E B F) by (forward_using lemma_parallelNC).
 assert (nCol F B E) by (forward_using lemma_NCorder).
 rename_H H;let Tf:=fresh in
 assert (Tf:exists H, (BetS E H B /\ BetS F r H)) by (conclude postulate_Pasch_outer);destruct Tf as [H];spliter.
 assert (Col E H B) by (conclude_def Col ).
 assert (Col F r H) by (conclude_def Col ).
 assert (Col E B H) by (forward_using lemma_collinearorder).
 assert (Col C r F) by (conclude_def Col ).
 assert (Col r F C) by (forward_using lemma_collinearorder).
 assert (Col r F H) by (forward_using lemma_collinearorder).
 assert (neq r F) by (forward_using lemma_betweennotequal).
 assert (Col F C H) by (conclude lemma_collinear4).
 assert (neq B E) by (forward_using lemma_NCdistinct).
 assert (neq E B) by (conclude lemma_inequalitysymmetric).
 assert (neq F C) by (conclude_def Par ).
 assert (Meet E B F C) by (conclude_def Meet ).
 assert (~ Meet E B F C) by (conclude_def Par ).
 contradict.
 }
assert (Col A F E) by (forward_using lemma_collinearorder).
assert ((eq A F \/ eq A E \/ eq F E \/ BetS F A E \/ BetS A F E \/ BetS A E F)) by (conclude_def Col ).
assert (BetS A E F).
by cases on (eq A F \/ eq A E \/ eq F E \/ BetS F A E \/ BetS A F E \/ BetS A E F).
{
 assert (~ ~ BetS A E F).
  {
  intro.
  assert (BetS A D A) by (conclude cn_equalitysub).
  assert (~ BetS A D A) by (conclude axiom_betweennessidentity).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS A E F).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS A E F).
  {
  intro.
  assert (eq E F) by (conclude lemma_equalitysymmetric).
  assert (Col B E F) by (conclude_def Col ).
  assert (Col E B F) by (forward_using lemma_collinearorder).
  assert (eq F F) by (conclude cn_equalityreflexive).
  assert (Col F C F) by (conclude_def Col ).
  assert (neq E B) by (conclude_def Par ).
  assert (neq F C) by (conclude_def Par ).
  assert (Meet E B F C) by (conclude_def Meet ).
  assert (~ Meet E B F C) by (conclude_def Par ).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS A E F).
  {
  intro.
  assert (BetS F D A) by (conclude axiom_betweennesssymmetry).
  assert (BetS D A E) by (conclude lemma_3_6a).
  assert (Cong D A D A) by (conclude cn_congruencereflexive).
  assert (Lt D A D E) by (conclude_def Lt ).
  assert (Cong D A A D) by (conclude cn_equalityreverse).
  assert (Lt A D D E) by (conclude lemma_lessthancongruence2).
  assert (Cong D E E D) by (conclude cn_equalityreverse).
  assert (Lt A D E D) by (conclude lemma_lessthancongruence).
  assert (Cong A D A D) by (conclude cn_congruencereflexive).
  assert (Lt A D A F) by (conclude_def Lt ).
  assert (Cong A D D A) by (conclude cn_equalityreverse).
  assert (Lt D A A F) by (conclude lemma_lessthancongruence2).
  assert (Cong A F F A) by (conclude cn_equalityreverse).
  assert (Lt D A F A) by (conclude lemma_lessthancongruence).
  assert (Cong F A F A) by (conclude cn_congruencereflexive).
  assert (Lt F A F E) by (conclude_def Lt ).
  assert (Lt D A F E) by (conclude lemma_lessthantransitive).
  assert (Cong D A F E) by (forward_using lemma_congruenceflip).
  assert (Lt F E F E) by (conclude lemma_lessthancongruence2).
  assert (~ Lt F E F E) by (conclude lemma_trichotomy2).
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS A E F).
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


