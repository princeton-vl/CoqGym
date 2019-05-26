Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_raystrict : 
   forall A B C, 
   Out A B C ->
   neq A C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS J A C /\ BetS J A B)) by (conclude_def Out );destruct Tf as [J];spliter.
assert (neq A C) by (forward_using lemma_betweennotequal).
close.
Qed.

End Euclid.


