Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_localextension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_extensionunique.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_3_7a : 
   forall A B C D, 
   BetS A B C -> BetS B C D ->
   BetS A C D.
Proof.
intros.
assert (neq A C) by (forward_using lemma_betweennotequal).
assert (neq C D) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists E, (BetS A C E /\ Cong C E C D)) by (conclude lemma_localextension);destruct Tf as [E];spliter.
assert (Cong C D C E) by (conclude lemma_congruencesymmetric).
assert (BetS B C E) by (conclude lemma_3_6a).
assert (eq D E) by (conclude lemma_extensionunique).
assert (BetS A C D) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.

