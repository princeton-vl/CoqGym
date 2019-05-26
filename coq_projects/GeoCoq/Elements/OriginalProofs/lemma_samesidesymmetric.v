Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_samesidesymmetric : 
   forall A B P Q, 
   OS P Q A B ->
   OS Q P A B /\ OS P Q B A /\ OS Q P B A.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E F G, (Col A B E /\ Col A B F /\ BetS P E G /\ BetS Q F G /\ nCol A B P /\ nCol A B Q)) by (conclude_def OS );destruct Tf as [E[F[G]]];spliter.
assert (OS Q P A B) by (conclude_def OS ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (Col B A F) by (forward_using lemma_collinearorder).
assert (nCol B A P) by (forward_using lemma_NCorder).
assert (nCol B A Q) by (forward_using lemma_NCorder).
assert (OS P Q B A) by (conclude_def OS ).
assert (OS Q P B A) by (conclude_def OS ).
close.
Qed.

End Euclid.


