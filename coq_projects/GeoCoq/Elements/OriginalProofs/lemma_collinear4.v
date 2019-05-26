Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinear4 : 
   forall A B C D, 
   Col A B C -> Col A B D -> neq A B ->
   Col B C D.
Proof.
intros.
assert (Col B C D).
by cases on (eq B C \/ eq B D \/ eq C D \/ eq A C \/ eq A D \/ (neq B C /\ neq B D /\ neq C D /\ neq A C /\ neq A D)).
{
 assert (Col B C D) by (conclude_def Col ).
 close.
 }
{
 assert (Col B C D) by (conclude_def Col ).
 close.
 }
{
 assert (Col B C D) by (conclude_def Col ).
 close.
 }
{
 assert (Col C B D) by (conclude cn_equalitysub).
 assert (Col B C D) by (forward_using lemma_collinearorder).
 close.
 }
{
 assert (Col D B C) by (conclude cn_equalitysub).
 assert (Col B C D) by (forward_using lemma_collinearorder).
 close.
 }
{
 assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
 assert (Col B C D).
 by cases on (BetS B A C \/ BetS A B C \/ BetS A C B).
 {
  assert ((eq A B \/ eq A D \/ eq B D \/ BetS B A D \/ BetS A B D \/ BetS A D B)) by (conclude_def Col ).
  assert (Col B C D).
  by cases on (BetS B A D \/ BetS A B D \/ BetS A D B).
  {
   assert (~ nCol B C D).
    {
    intro.
    assert (~ BetS B C D).
     {
     intro.
     assert (Col B C D) by (conclude_def Col ).
     contradict.
     }
    assert (~ BetS A C D).
     {
     intro.
     assert (BetS B C D) by (conclude lemma_3_5b).
     contradict.
     }
    assert (~ nCol B D C).
     {
     intro.
     assert (~ BetS C D C) by (conclude axiom_betweennessidentity).
     assert (~ BetS A D C).
      {
      intro.
      assert (BetS B D C) by (conclude lemma_3_5b).
      assert (Col B D C) by (conclude_def Col ).
      contradict.
      }
     assert (eq C D) by (conclude lemma_outerconnectivity).
     assert (Col B C D) by (conclude_def Col ).
     assert (Col B D C) by (forward_using lemma_collinearorder).
     contradict.
     }
    assert (Col B C D) by (forward_using lemma_collinearorder).
    contradict.
    }
   close.
   }
  {
   assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
   assert (BetS D B C) by (conclude lemma_3_7b).
   assert (Col D B C) by (conclude_def Col ).
   assert (Col B C D) by (forward_using lemma_collinearorder).
   close.
   }
  {
   assert (BetS B D A) by (conclude axiom_betweennesssymmetry).
   assert (BetS B D C) by (conclude lemma_3_6b).
   assert (Col B D C) by (conclude_def Col ).
   assert (Col B C D) by (forward_using lemma_collinearorder).
   close.
   }
(** cases *)
  close.
  }
 {
  assert ((eq A B \/ eq A D \/ eq B D \/ BetS B A D \/ BetS A B D \/ BetS A D B)) by (conclude_def Col ).
  assert (Col B C D).
  by cases on (BetS B A D \/ BetS A B D \/ BetS A D B).
  {
   assert (BetS D A B) by (conclude axiom_betweennesssymmetry).
   assert (BetS D B C) by (conclude lemma_3_7a).
   assert (Col D B C) by (conclude_def Col ).
   assert (Col B C D) by (forward_using lemma_collinearorder).
   close.
   }
  {
   assert (~ nCol B C D).
    {
    intro.
    assert (~ BetS B C D).
     {
     intro.
     assert (Col B C D) by (conclude_def Col ).
     contradict.
     }
    assert (~ BetS B D C).
     {
     intro.
     assert (Col B D C) by (conclude_def Col ).
     assert (Col B C D) by (forward_using lemma_collinearorder).
     contradict.
     }
    assert (eq C D) by (conclude lemma_outerconnectivity).
    assert (Col B C D) by (conclude_def Col ).
    contradict.
    }
   close.
   }
  {
   assert (BetS D B C) by (conclude lemma_3_6a).
   assert (Col D B C) by (conclude_def Col ).
   assert (Col B C D) by (forward_using lemma_collinearorder).
   close.
   }
(** cases *)
  close.
  }
 {
  assert ((eq A B \/ eq A D \/ eq B D \/ BetS B A D \/ BetS A B D \/ BetS A D B)) by (conclude_def Col ).
  assert (Col B C D).
  by cases on (BetS B A D \/ BetS A B D \/ BetS A D B).
  {
   assert (BetS D A B) by (conclude axiom_betweennesssymmetry).
   assert (BetS D C B) by (conclude lemma_3_5b).
   assert (BetS B C D) by (conclude axiom_betweennesssymmetry).
   assert (Col B C D) by (conclude_def Col ).
   close.
   }
  {
   assert (BetS C B D) by (conclude lemma_3_6a).
   assert (Col B C D) by (conclude_def Col ).
   close.
   }
  {
   assert (~ nCol B C D).
    {
    intro.
    assert (~ ~ BetS B D C).
     {
     intro.
     assert (~ ~ BetS B C D).
      {
      intro.
      assert (BetS B C A) by (conclude axiom_betweennesssymmetry).
      assert (BetS B D A) by (conclude axiom_betweennesssymmetry).
      assert (eq C D) by (conclude axiom_connectivity).
      contradict.
      }
     assert (Col B C D) by (conclude_def Col ).
     contradict.
     }
    assert (Col B D C) by (conclude_def Col ).
    assert (Col B C D) by (forward_using lemma_collinearorder).
    contradict.
    }
   close.
   }
(** cases *)
  close.
  }
(** cases *)
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


