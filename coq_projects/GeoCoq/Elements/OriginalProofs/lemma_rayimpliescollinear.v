Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_rayimpliescollinear : 
   forall A B C, 
   Out A B C ->
   Col A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS J A C /\ BetS J A B)) by (conclude_def Out );destruct Tf as [J];spliter.
assert (neq J A) by (forward_using lemma_betweennotequal).
assert (Col J A B) by (conclude_def Col ).
assert (Col J A C) by (conclude_def Col ).
assert (Col A B C) by (conclude lemma_collinear4).
close.
Qed.

End Euclid.


