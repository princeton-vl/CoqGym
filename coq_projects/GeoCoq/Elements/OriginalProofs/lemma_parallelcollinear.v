Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelcollinear1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_tarskiparallelflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelcollinear2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelcollinear : 
   forall A B C c d, 
   TP A B c d -> Col c d C -> neq C d ->
   TP A B C d.
Proof.
intros.
assert ((neq A B /\ neq c d /\ ~ Meet A B c d /\ OS c d A B)) by (conclude_def TP ).
assert ((eq c d \/ eq c C \/ eq d C \/ BetS d c C \/ BetS c d C \/ BetS c C d)) by (conclude_def Col ).
assert (TP A B C d).
by cases on (eq c d \/ eq c C \/ eq d C \/ BetS d c C \/ BetS c d C \/ BetS c C d).
{
 assert (~ ~ TP A B C d).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (TP A B C d) by (conclude cn_equalitysub).
 close.
 }
{
 assert (~ ~ TP A B C d).
  {
  intro.
  assert (eq C d) by (conclude lemma_equalitysymmetric).
  contradict.
  }
 close.
 }
{
 assert (BetS C c d) by (conclude axiom_betweennesssymmetry).
 assert (TP A B C d) by (conclude lemma_parallelcollinear1).
 close.
 }
{
 assert (BetS C d c) by (conclude axiom_betweennesssymmetry).
 assert (TP A B d c) by (forward_using lemma_tarskiparallelflip).
 assert (TP A B C c) by (conclude lemma_parallelcollinear1).
 assert (TP A B c C) by (forward_using lemma_tarskiparallelflip).
 assert (TP A B d C) by (conclude lemma_parallelcollinear2).
 assert (TP A B C d) by (forward_using lemma_tarskiparallelflip).
 close.
 }
{
 assert (TP A B C d) by (conclude lemma_parallelcollinear2).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


