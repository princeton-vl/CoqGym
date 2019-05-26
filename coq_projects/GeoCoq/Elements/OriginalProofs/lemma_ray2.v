Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_ray2 : 
   forall A B C, 
   Out A B C ->
   neq A B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS E A C /\ BetS E A B)) by (conclude_def Out );destruct Tf as [E];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
close.
Qed.

End Euclid.


