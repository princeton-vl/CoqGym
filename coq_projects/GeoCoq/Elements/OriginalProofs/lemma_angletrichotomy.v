Require Export GeoCoq.Elements.OriginalProofs.lemma_angleordertransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sameside2.
Require Export GeoCoq.Elements.OriginalProofs.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angletrichotomy : 
   forall A B C D E F, 
   LtA A B C D E F ->
   ~ LtA D E F A B C.
Proof.
intros.
assert (~ LtA D E F A B C).
 {
 intro.
 assert (LtA A B C A B C) by (conclude lemma_angleordertransitive).
 rename_H H;let Tf:=fresh in
 assert (Tf:exists G H J, (BetS G H J /\ Out B A G /\ Out B C J /\ CongA A B C A B H)) by (conclude_def LtA );destruct Tf as [G[H[J]]];spliter.
 let Tf:=fresh in
 assert (Tf:exists U V u v, (Out B A U /\ Out B C V /\ Out B A u /\ Out B H v /\ Cong B U B u /\ Cong B V B v /\ Cong U V u v /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
 assert (~ eq A B).
  {
  intro.
  assert (Col A B C) by (conclude_def Col ).
  contradict.
  }
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (eq U u) by (conclude lemma_layoffunique).
 assert (Cong U V U v) by (conclude cn_equalitysub).
 assert (Col B A U) by (conclude lemma_rayimpliescollinear).
 assert (Col B A G) by (conclude lemma_rayimpliescollinear).
 assert (neq G H) by (forward_using lemma_betweennotequal).
 assert (neq H G) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists P, (BetS H G P /\ Cong G P H G)) by (conclude lemma_extension);destruct Tf as [P];spliter.
 assert (BetS J H G) by (conclude axiom_betweennesssymmetry).
 assert (BetS J G P) by (conclude lemma_3_7a).
 assert (~ Col B A J).
  {
  intro.
  assert (Col B C J) by (conclude lemma_rayimpliescollinear).
  assert (Col J B A) by (forward_using lemma_collinearorder).
  assert (Col J B C) by (forward_using lemma_collinearorder).
  assert (neq B J) by (conclude lemma_raystrict).
  assert (neq J B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A C) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (TS J B A P) by (conclude_def TS ).
 assert (~ Col B U H).
  {
  intro.
  assert (Col B A U) by (conclude lemma_rayimpliescollinear).
  assert (Col U B A) by (forward_using lemma_collinearorder).
  assert (Col U B H) by (forward_using lemma_collinearorder).
  assert (neq B U) by (conclude lemma_raystrict).
  assert (neq U B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A H) by (conclude lemma_collinear4).
  assert (Col G H J) by (conclude_def Col ).
  assert (Col A B G) by (forward_using lemma_collinearorder).
  assert (Col A B H) by (forward_using lemma_collinearorder).
  assert (Col B G H) by (conclude lemma_collinear4).
  assert (Col G H B) by (forward_using lemma_collinearorder).
  assert (Col G H J) by (conclude_def Col ).
  assert (neq G H) by (forward_using lemma_betweennotequal).
  assert (Col H B J) by (conclude lemma_collinear4).
  assert (Col H B A) by (forward_using lemma_collinearorder).
  assert (~ neq H B).
   {
   intro.
   assert (Col B J A) by (conclude lemma_collinear4).
   assert (Col B A J) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS G B J) by (conclude cn_equalitysub).
  assert (Col G B J) by (conclude_def Col ).
  assert (Col B G J) by (forward_using lemma_collinearorder).
  assert (Col B G A) by (forward_using lemma_collinearorder).
  assert (neq B G) by (conclude lemma_raystrict).
  assert (Col G J A) by (conclude lemma_collinear4).
  assert (Col G J B) by (forward_using lemma_collinearorder).
  assert (neq G J) by (forward_using lemma_betweennotequal).
  assert (Col J A B) by (conclude lemma_collinear4).
  assert (Col B A J) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Out B G U) by (conclude lemma_ray3).
 assert (Col B G U) by (conclude lemma_rayimpliescollinear).
 assert (Col B U G) by (forward_using lemma_collinearorder).
 assert (TS H B U P) by (conclude_def TS ).
 assert (BetS J H G) by (conclude axiom_betweennesssymmetry).
 assert (BetS J G P) by (conclude lemma_3_7a).
 assert (~ Col B U J).
  {
  intro.
  assert (Col B C J) by (conclude lemma_rayimpliescollinear).
  assert (Col B J C) by (forward_using lemma_collinearorder).
  assert (Col B A U) by (conclude lemma_rayimpliescollinear).
  assert (Col U B A) by (forward_using lemma_collinearorder).
  assert (Col U B J) by (forward_using lemma_collinearorder).
  assert (neq B U) by (conclude lemma_raystrict).
  assert (neq U B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A J) by (conclude lemma_collinear4).
  assert (Col B C J) by (conclude lemma_rayimpliescollinear).
  assert (Col J B C) by (forward_using lemma_collinearorder).
  assert (Col J B A) by (forward_using lemma_collinearorder).
  assert (neq B J) by (conclude lemma_raystrict).
  assert (neq J B) by (conclude lemma_inequalitysymmetric).
  assert (Col B C A) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (OS J H B U) by (conclude_def OS ).
 assert (OS H J B U) by (forward_using lemma_samesidesymmetric).
 assert (Out B J V) by (conclude lemma_ray3).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (Col B B U) by (conclude_def Col ).
 assert (OS H V B U) by (conclude lemma_sameside2).
 assert (OS V H B U) by (forward_using lemma_samesidesymmetric).
 assert (OS V v B U) by (conclude lemma_sameside2).
 assert (neq B U) by (conclude lemma_raystrict).
 assert (Cong V B v B) by (forward_using lemma_congruenceflip).
 assert (Cong V U v U) by (forward_using lemma_congruenceflip).
 assert (eq V v) by (conclude proposition_07).
 assert (Out B H V) by (conclude cn_equalitysub).
 assert (Col B H V) by (conclude lemma_rayimpliescollinear).
 assert (Col B J V) by (conclude lemma_rayimpliescollinear).
 assert (Col V B J) by (forward_using lemma_collinearorder).
 assert (Col V B H) by (forward_using lemma_collinearorder).
 assert (neq B V) by (conclude lemma_raystrict).
 assert (neq V B) by (conclude lemma_inequalitysymmetric).
 assert (Col B J H) by (conclude lemma_collinear4).
 assert (Col G H J) by (conclude_def Col ).
 assert (Col H J B) by (forward_using lemma_collinearorder).
 assert (Col H J G) by (forward_using lemma_collinearorder).
 assert (neq J H) by (forward_using lemma_betweennotequal).
 assert (neq H J) by (conclude lemma_inequalitysymmetric).
 assert (Col J B G) by (conclude lemma_collinear4).
 assert (Col B C J) by (conclude lemma_rayimpliescollinear).
 assert (Col J B C) by (forward_using lemma_collinearorder).
 assert (neq B J) by (conclude lemma_raystrict).
 assert (neq J B) by (conclude lemma_inequalitysymmetric).
 assert (Col B G C) by (conclude lemma_collinear4).
 assert (Col G B C) by (forward_using lemma_collinearorder).
 assert (Col B A G) by (conclude lemma_rayimpliescollinear).
 assert (Col G B A) by (forward_using lemma_collinearorder).
 assert (neq B G) by (conclude lemma_raystrict).
 assert (neq G B) by (conclude lemma_inequalitysymmetric).
 assert (Col B C A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
close.
Qed.

End Euclid.


