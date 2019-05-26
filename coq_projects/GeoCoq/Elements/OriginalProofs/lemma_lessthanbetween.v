Require Export GeoCoq.Elements.OriginalProofs.lemma_ray5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_layoffunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthanbetween : 
   forall A B C, 
   Lt A B A C -> Out A B C ->
   BetS A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ Cong A M A B)) by (conclude_def Lt );destruct Tf as [M];spliter.
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (Out A M C) by (conclude lemma_ray4).
assert (Out A C M) by (conclude lemma_ray5).
assert (Out A C B) by (conclude lemma_ray5).
assert (eq M B) by (conclude lemma_layoffunique).
assert (BetS A B C) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


