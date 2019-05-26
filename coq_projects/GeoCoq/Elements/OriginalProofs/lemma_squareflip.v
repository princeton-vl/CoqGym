Require Export GeoCoq.Elements.OriginalProofs.lemma_8_2.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_squareflip : 
   forall A B C D, 
   SQ A B C D ->
   SQ B A D C.
Proof.
intros.
assert ((Cong A B C D /\ Cong A B B C /\ Cong A B D A /\ Per D A B /\ Per A B C /\ Per B C D /\ Per C D A)) by (conclude_def SQ ).
assert (Cong B A D C) by (forward_using lemma_congruenceflip).
assert (Cong B A A D) by (forward_using lemma_congruenceflip).
assert (Cong B A C B) by (forward_using lemma_congruenceflip).
assert (Per C B A) by (conclude lemma_8_2).
assert (Per B A D) by (conclude lemma_8_2).
assert (Per A D C) by (conclude lemma_8_2).
assert (Per D C B) by (conclude lemma_8_2).
assert (SQ B A D C) by (conclude_def SQ ).
close.
Qed.

End Euclid.


