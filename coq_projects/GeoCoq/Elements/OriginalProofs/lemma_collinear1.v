Require Export GeoCoq.Elements.OriginalProofs.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.


Lemma lemma_collinear1 : 
   forall A B C, 
   Col A B C ->
   Col B A C.
Proof.
intros.
assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
assert (Col B A C).
by cases on (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B).
{
 assert (eq B A) by (conclude lemma_equalitysymmetric).
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
{
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
{
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
{
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
{
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
{
 assert (BetS B C A) by (conclude axiom_betweennesssymmetry).
 assert (Col B A C) by (conclude_def Col ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


