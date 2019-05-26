Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_NCdistinct : 
   forall A B C, 
   nCol A B C ->
   neq A B /\ neq B C /\ neq A C /\ neq B A /\ neq C B /\ neq C A.
Proof.
intros.
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
close.
Qed.

End Euclid.


