Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglessymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_angledistinct : 
   forall A B C a b c, 
   CongA A B C a b c ->
   neq A B /\ neq B C /\ neq A C /\ neq a b /\ neq b c /\ neq a c.
Proof.
intros.
assert (nCol A B C) by (conclude_def CongA ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (CongA a b c A B C) by (conclude lemma_equalanglessymmetric).
assert (nCol a b c) by (conclude_def CongA ).
assert (~ eq a b).
 {
 intro.
 assert (Col a b c) by (conclude_def Col ).
 contradict.
 }
assert (~ eq b c).
 {
 intro.
 assert (Col a b c) by (conclude_def Col ).
 contradict.
 }
assert (~ eq a c).
 {
 intro.
 assert (Col a b c) by (conclude_def Col ).
 contradict.
 }
close.
Qed.

End Euclid.


