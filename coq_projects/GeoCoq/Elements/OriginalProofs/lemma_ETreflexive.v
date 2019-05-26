Require Export GeoCoq.Elements.OriginalProofs.lemma_TCreflexive.

Section Euclid.

Context `{Ax:area}.

Lemma lemma_ETreflexive : 
   forall A B C, 
   Triangle A B C ->
   ET A B C A B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (Cong_3 A B C A B C) by (conclude lemma_TCreflexive).
assert (ET A B C A B C) by (conclude axiom_congruentequal).
close.
Qed.

End Euclid.


