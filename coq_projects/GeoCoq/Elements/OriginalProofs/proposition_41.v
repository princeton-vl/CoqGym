Require Export GeoCoq.Elements.OriginalProofs.proposition_37.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_41 : 
   forall A B C D E, 
   PG A B C D -> Col A D E ->
   ET A B C E B C.
Proof.
intros.
assert (Par A B C D) by (conclude_def PG ).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (Triangle A B C) by (conclude_def Triangle ).
assert (ET A B C E B C).
by cases on (eq A E \/ neq A E).
{
 assert (ET A B C A B C) by (conclude lemma_ETreflexive).
 assert (ET A B C E B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Par A D B C) by (conclude_def PG ).
 assert (Col D A E) by (forward_using lemma_collinearorder).
 assert (Par B C A D) by (conclude lemma_parallelsymmetric).
 assert (Par B C D A) by (forward_using lemma_parallelflip).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Par B C E A) by (conclude lemma_collinearparallel).
 assert (Par B C A E) by (forward_using lemma_parallelflip).
 assert (Par A E B C) by (conclude lemma_parallelsymmetric).
 assert (ET A B C E B C) by (conclude proposition_37).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


