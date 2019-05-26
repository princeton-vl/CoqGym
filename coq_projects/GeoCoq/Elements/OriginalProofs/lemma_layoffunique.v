Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_differenceofparts.
Require Export GeoCoq.Elements.OriginalProofs.lemma_interior5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_partnotequalwhole.
Require Export GeoCoq.Elements.OriginalProofs.lemma_3_6b.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_layoffunique : 
   forall A B C D, 
   Out A B C -> Out A B D -> Cong A C A D ->
   eq C D.
Proof.
intros.
assert (Cong A D A C) by (conclude lemma_congruencesymmetric).
assert ((BetS A C B \/ eq B C \/ BetS A B C)) by (conclude lemma_ray1).
assert ((BetS A D B \/ eq B D \/ BetS A B D)) by (conclude lemma_ray1).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (Cong C B C B) by (conclude cn_congruencereflexive).
assert (Cong A C A C) by (conclude cn_congruencereflexive).
assert (eq C D).
by cases on (BetS A C B \/ eq B C \/ BetS A B C).
{
 assert (eq C D).
 by cases on (BetS A D B \/ eq B D \/ BetS A B D).
 {
  assert (Cong C B D B) by (conclude lemma_differenceofparts).
  assert (Cong B C B D) by (forward_using lemma_congruenceflip).
  assert (Cong C C C D) by (conclude lemma_interior5).
  assert (Cong C D C C) by (conclude lemma_congruencesymmetric).
  assert (~ neq C D).
   {
   intro.
   assert (neq C C) by (conclude axiom_nocollapse).
   assert (eq C C) by (conclude cn_equalityreflexive).
   contradict.
   }
  close.
  }
 {
  assert (BetS A C D) by (conclude cn_equalitysub).
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A C A D) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
 {
  assert (BetS A C D) by (conclude lemma_3_6b).
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A C A D) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
(** cases *)
 close.
 }
{
 assert (Cong A B A D) by (conclude cn_equalitysub).
 assert (Cong A D A B) by (conclude lemma_congruencesymmetric).
 assert (eq C D).
 by cases on (BetS A D B \/ eq B D \/ BetS A B D).
 {
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A D A B) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
 {
  assert (eq C B) by (conclude lemma_equalitysymmetric).
  assert (eq D B) by (conclude lemma_equalitysymmetric).
  assert (eq C D) by (conclude cn_equalitytransitive).
  close.
  }
 {
  assert (BetS A C D) by (conclude cn_equalitysub).
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A C A D) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
(** cases *)
 close.
 }
{
 assert (eq C D).
 by cases on (BetS A D B \/ eq B D \/ BetS A B D).
 {
  assert (BetS A D C) by (conclude lemma_3_6b).
  assert (Cong A D A C) by (conclude lemma_congruencesymmetric).
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A D A C) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
 {
  assert (BetS A D C) by (conclude cn_equalitysub).
  assert (~ neq C D).
   {
   intro.
   assert (~ Cong A D A C) by (conclude lemma_partnotequalwhole).
   contradict.
   }
  close.
  }
 {
  assert (neq A B) by (forward_using lemma_betweennotequal).
  assert (Cong B C B D) by (conclude lemma_differenceofparts).
  assert (eq C D) by (conclude lemma_extensionunique).
  close.
  }
(** cases *)
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


