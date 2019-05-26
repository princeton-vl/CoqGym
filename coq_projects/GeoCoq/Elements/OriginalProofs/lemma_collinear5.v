Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinear5 : 
   forall A B C D E, 
   neq A B -> Col A B C -> Col A B D -> Col A B E ->
   Col C D E.
Proof.
intros.
assert (Col B C D) by (conclude lemma_collinear4).
assert (Col B C E) by (conclude lemma_collinear4).
assert (Col C D E).
by cases on (neq B C \/ eq B C).
{
 assert (Col C D E) by (conclude lemma_collinear4).
 close.
 }
{
 assert (Col B D E) by (conclude lemma_collinear4).
 assert (Col C D E) by (conclude cn_equalitysub).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


