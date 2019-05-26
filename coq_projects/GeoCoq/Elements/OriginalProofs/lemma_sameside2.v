Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5b.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5a.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_sameside2 : 
   forall A B C E F G, 
   OS E F A C -> Col A B C -> Out B F G ->
   OS E G A C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists Q U V, (Col A C U /\ Col A C V /\ BetS E U Q /\ BetS F V Q /\ nCol A C E /\ nCol A C F)) by (conclude_def OS );destruct Tf as [Q[U[V]]];spliter.
assert (TS F A C Q) by (conclude_def TS ).
assert (Col A C B) by (forward_using lemma_collinearorder).
assert (~ eq A C).
 {
 intro.
 assert (Col A C F) by (conclude_def Col ).
 contradict.
 }
assert (Col B F G) by (conclude lemma_rayimpliescollinear).
assert (Col B G F) by (forward_using lemma_collinearorder).
assert (Col A C B) by (forward_using lemma_collinearorder).
assert (~ ~ TS G A C Q).
 {
 intro.
 assert (~ eq F G).
  {
  intro.
  assert (TS G A C Q) by (conclude cn_equalitysub).
  contradict.
  }
 assert (~ eq B V).
  {
  intro.
  assert (BetS F B Q) by (conclude cn_equalitysub).
  assert ((BetS B G F \/ eq F G \/ BetS B F G)) by (conclude lemma_ray1).
  assert (BetS G B Q).
  by cases on (BetS B G F \/ eq F G \/ BetS B F G).
  {
   assert (BetS F G B) by (conclude axiom_betweennesssymmetry).
   assert (BetS G B Q) by (conclude lemma_3_6a).
   close.
   }
  {
   assert (~ ~ BetS G B Q).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (BetS G F B) by (conclude axiom_betweennesssymmetry).
   assert (BetS G B Q) by (conclude lemma_3_7a).
   close.
   }
(** cases *)
  assert (~ Col A C G).
   {
   intro.
   assert (Col A C B) by (forward_using lemma_collinearorder).
   assert (Col C G B) by (conclude lemma_collinear4).
   assert (Col G B C) by (forward_using lemma_collinearorder).
   assert (Col G B F) by (forward_using lemma_collinearorder).
   assert (neq B G) by (conclude lemma_raystrict).
   assert (neq G B) by (conclude lemma_inequalitysymmetric).
   assert (Col B C F) by (conclude lemma_collinear4).
   assert (~ neq B C).
    {
    intro.
    assert (Col B C A) by (forward_using lemma_collinearorder).
    assert (Col C F A) by (conclude lemma_collinear4).
    assert (Col A C F) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (Col A B G) by (conclude cn_equalitysub).
   assert (neq A B) by (conclude cn_equalitysub).
   assert (Col G B A) by (forward_using lemma_collinearorder).
   assert (Col B A F) by (conclude lemma_collinear4).
   assert (Col A B F) by (forward_using lemma_collinearorder).
   assert (Col A C F) by (conclude cn_equalitysub).
   contradict.
   }
  assert (TS G A C Q) by (conclude_def TS ).
  contradict.
  }
 assert (~ Col Q F B).
  {
  intro.
  assert (Col F V Q) by (conclude_def Col ).
  assert (Col Q F V) by (forward_using lemma_collinearorder).
  assert (neq F Q) by (forward_using lemma_betweennotequal).
  assert (neq Q F) by (conclude lemma_inequalitysymmetric).
  assert (Col F B V) by (conclude lemma_collinear4).
  assert (Col C B V) by (conclude lemma_collinear4).
  assert (Col B V F) by (forward_using lemma_collinearorder).
  assert (Col B V C) by (forward_using lemma_collinearorder).
  assert (Col V F C) by (conclude lemma_collinear4).
  assert (Col V C F) by (forward_using lemma_collinearorder).
  assert (Col V C A) by (forward_using lemma_collinearorder).
  assert (~ neq V C).
   {
   intro.
   assert (Col C F A) by (conclude lemma_collinear4).
   assert (Col A C F) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (neq A V) by (conclude cn_equalitysub).
  assert (neq V A) by (conclude lemma_inequalitysymmetric).
  assert (Col C A B) by (forward_using lemma_collinearorder).
  assert (Col C A V) by (forward_using lemma_collinearorder).
  assert (neq C A) by (conclude lemma_inequalitysymmetric).
  assert (Col A B V) by (conclude lemma_collinear4).
  assert (Col B V A) by (forward_using lemma_collinearorder).
  assert (Col V F A) by (conclude lemma_collinear4).
  assert (Col V A F) by (forward_using lemma_collinearorder).
  assert (Col V A C) by (forward_using lemma_collinearorder).
  assert (Col A F C) by (conclude lemma_collinear4).
  assert (Col A C F) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert ((BetS B G F \/ eq F G \/ BetS B F G)) by (conclude lemma_ray1).
 assert (TS G A C Q).
 by cases on (BetS B G F \/ eq F G \/ BetS B F G).
 {
  assert (TS G A C Q) by (conclude lemma_9_5b).
  close.
  }
 {
  assert (TS G A C Q) by (conclude cn_equalitysub).
  close.
  }
 {
  assert (~ Col B G Q).
   {
   intro.
   assert (Col G B F) by (forward_using lemma_collinearorder).
   assert (neq B G) by (forward_using lemma_betweennotequal).
   assert (neq G B) by (conclude lemma_inequalitysymmetric).
   assert (Col G B Q) by (forward_using lemma_collinearorder).
   assert (Col B F Q) by (conclude lemma_collinear4).
   assert (Col Q F B) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (TS G A C Q) by (conclude lemma_9_5a).
  close.
  }
(** cases *)
 contradict.
 }
rename_H H;
let Tf:=fresh in
assert (Tf:exists H, (BetS G H Q /\ Col A C H /\ nCol A C G)) by (conclude_def TS );destruct Tf as [H];spliter.
assert (OS E G A C) by (conclude_def OS ).
close.
Qed.

End Euclid.


