Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_oppositesideflip : 
   forall A B P Q, 
   TS P A B Q ->
   TS P B A Q.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists r, (BetS P r Q /\ Col A B r /\ nCol A B P)) by (conclude_def TS );destruct Tf as [r];spliter.
assert (nCol B A P) by (forward_using lemma_NCorder).
assert (Col B A r) by (forward_using lemma_collinearorder).
assert (TS P B A Q) by (conclude_def TS ).
close.
Qed.

End Euclid.


