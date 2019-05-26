Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossimpliesopposite : 
   forall A B C D, 
   CR A B C D -> nCol A C D ->
   TS A C D B /\ TS A D C B /\ TS B C D A /\ TS B D C A.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M, (BetS A M B /\ BetS C M D)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (Col C M D) by (conclude_def Col ).
assert (Col C D M) by (forward_using lemma_collinearorder).
assert (nCol C D A) by (forward_using lemma_NCorder).
assert (nCol D C A) by (forward_using lemma_NCorder).
assert (TS A C D B) by (conclude_def TS ).
assert (Col D C M) by (forward_using lemma_collinearorder).
assert (TS A D C B) by (conclude_def TS ).
assert (TS B C D A) by (conclude lemma_oppositesidesymmetric).
assert (TS B D C A) by (conclude lemma_oppositesidesymmetric).
close.
Qed.

End Euclid.


