Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_localextension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencesymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_betweennesspreserved : 
   forall A B C a b c, 
   Cong A B a b -> Cong A C a c -> Cong B C b c -> BetS A B C ->
   BetS a b c.
Proof.
intros.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq a b) by (conclude axiom_nocollapse).
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (neq b c) by (conclude axiom_nocollapse).
let Tf:=fresh in
assert (Tf:exists d, (BetS a b d /\ Cong b d b c)) by (conclude lemma_localextension);destruct Tf as [d];spliter.
assert (Cong b c b d) by (conclude lemma_congruencesymmetric).
assert (Cong b c B C) by (conclude lemma_congruencesymmetric).
assert (Cong b d B C) by (conclude cn_congruencetransitive).
assert (Cong B C b d) by (conclude lemma_congruencesymmetric).
assert (Cong C C c d) by (conclude axiom_5_line).
assert (Cong c d C C) by (conclude lemma_congruencesymmetric).
assert (~ neq c d).
 {
 intro.
 assert (neq C C) by (conclude axiom_nocollapse).
 assert (eq C C) by (conclude cn_equalityreflexive).
 contradict.
 }
assert (BetS a b c) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


