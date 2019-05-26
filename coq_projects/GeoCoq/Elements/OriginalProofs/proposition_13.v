Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_13 : 
   forall A B C D, 
   BetS D B C -> nCol A B C ->
   RT C B A A B D.
Proof.
intros.
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Out B A A) by (conclude lemma_ray4).
assert (BetS C B D) by (conclude axiom_betweennesssymmetry).
assert (Supp C B A A D) by (conclude_def Supp ).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (Col D B C) by (conclude_def Col ).
assert (Col C B D) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col C B B) by (conclude_def Col ).
assert (neq D B) by (forward_using lemma_betweennotequal).
assert (nCol D B A) by (conclude lemma_NChelper).
assert (nCol A B D) by (forward_using lemma_NCorder).
assert (CongA A B D A B D) by (conclude lemma_equalanglesreflexive).
assert (CongA C B A C B A) by (conclude lemma_equalanglesreflexive).
assert (RT C B A A B D) by (conclude_def RT ).
close.
Qed.

End Euclid.