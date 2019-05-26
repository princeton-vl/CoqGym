Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_tworays : 
   forall A B C, 
   Out A B C -> Out B A C ->
   BetS A C B.
Proof.
intros.
assert ((BetS A C B \/ eq B C \/ BetS A B C)) by (conclude lemma_ray1).
assert ((BetS B C A \/ eq A C \/ BetS B A C)) by (conclude lemma_ray1).
assert (BetS A C B).
by cases on (BetS A C B \/ eq B C \/ BetS A B C).
{
 close.
 }
{
 assert (~ ~ BetS A C B).
  {
  intro.
  assert (neq B C) by (conclude lemma_raystrict).
  contradict.
  }
 close.
 }
{
 assert (BetS A C B).
 by cases on (BetS B C A \/ eq A C \/ BetS B A C).
 {
  assert (BetS A C B) by (conclude axiom_betweennesssymmetry).
  close.
  }
 {
  assert (~ ~ BetS A C B).
   {
   intro.
   assert (neq A C) by (conclude lemma_raystrict).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A C B).
   {
   intro.
   assert (BetS A B A) by (conclude axiom_innertransitivity).
   assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
   contradict.
   }
  close.
  }
(** cases *)
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


