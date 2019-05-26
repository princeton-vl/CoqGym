Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_twolines : 
   forall A B C D E F, 
   Cut A B C D E -> Cut A B C D F -> nCol B C D ->
   eq E F.
Proof.
intros.
assert ((BetS A E B /\ BetS C E D /\ nCol A B C /\ nCol A B D)) by (conclude_def Cut ).
assert ((BetS A F B /\ BetS C F D /\ nCol A B C /\ nCol A B D)) by (conclude_def Cut ).
assert (Col A E B) by (conclude_def Col ).
assert (Col A B E) by (forward_using lemma_collinearorder).
assert (Col A F B) by (conclude_def Col ).
assert (Col A B F) by (forward_using lemma_collinearorder).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (Col B E F) by (conclude lemma_collinear4).
assert (Col E F B) by (forward_using lemma_collinearorder).
assert (Col C E D) by (conclude_def Col ).
assert (Col C F D) by (conclude_def Col ).
assert (Col C D F) by (forward_using lemma_collinearorder).
assert (Col C D E) by (forward_using lemma_collinearorder).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (Col D E F) by (conclude lemma_collinear4).
assert (Col E F D) by (forward_using lemma_collinearorder).
assert (Col D C E) by (conclude lemma_collinear1).
assert (Col D C F) by (conclude lemma_collinear1).
assert (BetS D E C) by (conclude axiom_betweennesssymmetry).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (Col C E F) by (conclude lemma_collinear4).
assert (Col E F C) by (forward_using lemma_collinearorder).
assert (~ neq E F).
 {
 intro.
 assert (Col F B C) by (conclude lemma_collinear4).
 assert (Col F B D) by (conclude lemma_collinear4).
 assert (~ eq F B).
  {
  intro.
  assert (Col F C D) by (conclude_def Col ).
  assert (Col B C D) by (conclude cn_equalitysub).
  contradict.
  }
 assert (Col B C D) by (conclude lemma_collinear4).
 contradict.
 }
close.
Qed.

End Euclid.


