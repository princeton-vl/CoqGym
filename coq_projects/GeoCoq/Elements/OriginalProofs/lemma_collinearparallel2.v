Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearparallel2 : 
   forall A B C D E F, 
   Par A B C D -> Col C D E -> Col C D F -> neq E F ->
   Par A B E F.
Proof.
intros.
assert (neq F E) by (conclude lemma_inequalitysymmetric).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (Col D C E) by (forward_using lemma_collinearorder).
assert (Col D C F) by (forward_using lemma_collinearorder).
assert (Col C E F) by (conclude lemma_collinear4).
assert (Col C F E) by (forward_using lemma_collinearorder).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (Par A B E F).
by cases on (eq E D \/ neq E D).
{
 assert (neq D F) by (conclude cn_equalitysub).
 assert (neq F D) by (conclude lemma_inequalitysymmetric).
 assert (Par A B F D) by (conclude lemma_collinearparallel).
 assert (Par A B D F) by (forward_using lemma_parallelflip).
 assert (Col C F D) by (forward_using lemma_collinearorder).
 assert (Col C F E) by (forward_using lemma_collinearorder).
 assert (Col F D E).
 by cases on (eq C F \/ neq C F).
 {
  assert (Col C D E) by (forward_using lemma_collinearorder).
  assert (Col F D E) by (conclude cn_equalitysub).
  close.
  }
 {
  assert (Col F D E) by (conclude lemma_collinear4).
  close.
  }
(** cases *)
 assert (Col D F E) by (forward_using lemma_collinearorder).
 assert (Par A B E F) by (conclude lemma_collinearparallel).
 close.
 }
{
 assert (Par A B E D) by (conclude lemma_collinearparallel).
 assert (Par A B D E) by (forward_using lemma_parallelflip).
 assert (Col D E F) by (conclude lemma_collinear4).
 assert (Par A B F E) by (conclude lemma_collinearparallel).
 assert (Par A B E F) by (forward_using lemma_parallelflip).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


