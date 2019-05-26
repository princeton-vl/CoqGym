Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_extensionunique.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_rightreverse : 
   forall A B C D, 
   Per A B C -> BetS A B D -> Cong A B B D ->
   Cong A C D C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS A B E /\ Cong A B E B /\ Cong A C E C /\ neq B C)) by (conclude_def Per );destruct Tf as [E];spliter.
assert (Cong B D A B) by (conclude lemma_congruencesymmetric).
assert (Cong B D E B) by (conclude lemma_congruencetransitive).
assert (Cong B D B E) by (forward_using lemma_congruenceflip).
assert (eq D E) by (conclude lemma_extensionunique).
assert (Cong A C D C) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


