Require Export GeoCoq.Elements.OriginalProofs.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_collinear2 : 
   forall A B C, 
   Col A B C ->
   Col B C A.
Proof.
intros.
assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
assert (Col B C A).
by cases on (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B).
{
 assert (eq B A) by (conclude lemma_equalitysymmetric).
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
{
 assert (eq C A) by (conclude lemma_equalitysymmetric).
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
{
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
{
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
{
 assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
{
 assert (BetS B C A) by (conclude axiom_betweennesssymmetry).
 assert (Col B C A) by (conclude_def Col ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


