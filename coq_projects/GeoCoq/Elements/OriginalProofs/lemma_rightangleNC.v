Require Export GeoCoq.Elements.OriginalProofs.lemma_midpointunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_rightangleNC : 
   forall A B C, 
   Per A B C ->
   nCol A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (Cong A B B D) by (forward_using lemma_congruenceflip).
assert (Midpoint A B D) by (conclude_def Midpoint ).
assert (~ BetS A C D).
 {
 intro.
 assert (Cong A C C D) by (forward_using lemma_congruenceflip).
 assert (Midpoint A C D) by (conclude_def Midpoint ).
 assert (eq B C) by (conclude lemma_midpointunique).
 contradict.
 }
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (~ eq C A).
 {
 intro.
 assert (Cong C C D C) by (conclude cn_equalitysub).
 assert (Cong D C C C) by (conclude lemma_congruencesymmetric).
 assert (~ neq D C).
  {
  intro.
  assert (neq C C) by (conclude axiom_nocollapse).
  assert (eq C C) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (eq A C) by (conclude lemma_equalitysymmetric).
 assert (eq D A) by (conclude cn_equalitytransitive).
 assert (eq A D) by (conclude lemma_equalitysymmetric).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 contradict.
 }
assert (~ eq C D).
 {
 intro.
 assert (Cong A C D D) by (conclude cn_equalitysub).
 assert (~ neq A C).
  {
  intro.
  assert (neq D D) by (conclude axiom_nocollapse).
  assert (eq D D) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (eq C A) by (conclude lemma_equalitysymmetric).
 contradict.
 }
assert (~ BetS C A D).
 {
 intro.
 assert (Cong C A C D) by (forward_using lemma_congruenceflip).
 assert (~ Cong C A C D) by (conclude lemma_partnotequalwhole).
 contradict.
 }
assert (~ BetS A D C).
 {
 intro.
 assert (BetS C D A) by (conclude axiom_betweennesssymmetry).
 assert (Cong C D C A) by (forward_using lemma_doublereverse).
 assert (~ Cong C D C A) by (conclude lemma_partnotequalwhole).
 contradict.
 }
assert (~ Col A B C).
 {
 intro.
 assert (Col A B D) by (conclude_def Col ).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 assert (Col B A D) by (forward_using lemma_collinearorder).
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Col A C D) by (conclude lemma_collinear4).
 assert ((eq A C \/ eq A D \/ eq C D \/ BetS C A D \/ BetS A C D \/ BetS A D C)) by (conclude_def Col ).
 assert (nCol A B C).
 by cases on (eq A C \/ eq A D \/ eq C D \/ BetS C A D \/ BetS A C D \/ BetS A D C).
 {
  assert (~ Col A B C).
   {
   intro.
   assert (neq A C) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  close.
  }
 {
  assert (~ Col A B C).
   {
   intro.
   assert (neq A D) by (forward_using lemma_betweennotequal).
   contradict.
   }
  close.
  }
 {
  assert (~ Col A B C).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ Col A B C).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ Col A B C).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ Col A B C).
   {
   intro.
   contradict.
   }
  close.
  }
(* cases *)
 contradict.
 }
close.
Qed.

End Euclid.
