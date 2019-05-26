Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_lessthannotequal : 
   forall A B C D, 
   Lt A B C D ->
   neq A B /\ neq C D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS C E D /\ Cong C E A B)) by (conclude_def Lt );destruct Tf as [E];spliter.
assert (neq C E) by (forward_using lemma_betweennotequal).
assert (neq A B) by (conclude axiom_nocollapse).
assert (neq C D) by (forward_using lemma_betweennotequal).
close.
Qed.

End Euclid.


