Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TCreflexive.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_EFreflexive : 
   forall a b c d p, 
   BetS a p c -> BetS b p d -> nCol a b c ->
   EF a b c d a b c d.
Proof.
intros.
assert (nCol a c b) by (forward_using lemma_NCorder).
assert (~ Col a c d).
 {
 intro.
 assert (Col b p d) by (conclude_def Col ).
 assert (Col a p c) by (conclude_def Col ).
 assert (Col a c p) by (forward_using lemma_collinearorder).
 assert (neq a c) by (forward_using lemma_betweennotequal).
 assert (Col c d p) by (conclude lemma_collinear4).
 assert (Col d p c) by (forward_using lemma_collinearorder).
 assert (Col d p b) by (forward_using lemma_collinearorder).
 assert (neq p d) by (forward_using lemma_betweennotequal).
 assert (neq d p) by (conclude lemma_inequalitysymmetric).
 assert (Col p c b) by (conclude lemma_collinear4).
 assert (Col a p c) by (conclude_def Col ).
 assert (Col p c a) by (forward_using lemma_collinearorder).
 assert (neq p c) by (forward_using lemma_betweennotequal).
 assert (Col c b a) by (conclude lemma_collinear4).
 assert (Col a b c) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle a c d) by (conclude_def Triangle ).
assert (Triangle a c b) by (conclude_def Triangle ).
assert (Cong_3 a c d a c d) by (conclude lemma_TCreflexive).
assert (Cong_3 a c b a c b) by (conclude lemma_TCreflexive).
assert (ET a c d a c d) by (conclude axiom_congruentequal).
assert (ET a c b a c b) by (conclude axiom_congruentequal).
assert (Col a c p) by (conclude_def Col ).
assert (nCol a c b) by (forward_using lemma_NCorder).
assert (TS b a c d) by (conclude_def TS ).
assert (EF a b c d a b c d) by (conclude axiom_paste3).
close.
Qed.

End Euclid.
