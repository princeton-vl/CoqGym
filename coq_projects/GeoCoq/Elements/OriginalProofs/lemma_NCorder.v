Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_NCorder : 
   forall A B C, 
   nCol A B C ->
   nCol B A C /\ nCol B C A /\ nCol C A B /\ nCol A C B /\ nCol C B A.
Proof.
intros.
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col B C A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col C A B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
close.
Qed.

End Euclid.


