Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_samesideflip : 
   forall A B P Q, 
   OS P Q A B ->
   OS P Q B A.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists p q r, (Col A B p /\ Col A B q /\ BetS P p r /\ BetS Q q r /\ nCol A B P /\ nCol A B Q)) by (conclude_def OS );destruct Tf as [p[q[r]]];spliter.
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col B A q) by (forward_using lemma_collinearorder).
assert (nCol B A P) by (forward_using lemma_NCorder).
assert (nCol B A Q) by (forward_using lemma_NCorder).
assert (OS P Q B A) by (conclude_def OS ).
close.
Qed.

End Euclid.


