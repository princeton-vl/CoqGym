Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_3_6b.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_outerconnectivity : 
   forall A B C D, 
   BetS A B C -> BetS A B D -> ~ BetS B C D -> ~ BetS B D C ->
   eq C D.
Proof.
intros.
assert (~ eq A C).
 {
 intro.
 assert (BetS A B A) by (conclude cn_equalitysub).
 assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (neq A D) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists E, (BetS A C E /\ Cong C E A D)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (BetS A B E) by (conclude lemma_3_6b).
assert (~ eq A D).
 {
 intro.
 assert (BetS A B A) by (conclude cn_equalitysub).
 assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (neq A C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists F, (BetS A D F /\ Cong D F A C)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (BetS F D A) by (conclude axiom_betweennesssymmetry).
assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
assert (BetS F B A) by (conclude lemma_3_5b).
assert (BetS A B F) by (conclude axiom_betweennesssymmetry).
assert (Cong F D D F) by (conclude cn_equalityreverse).
assert (Cong F D A C) by (conclude lemma_congruencetransitive).
assert (Cong A D C E) by (conclude lemma_congruencesymmetric).
assert (Cong D A A D) by (conclude cn_equalityreverse).
assert (Cong D A C E) by (conclude lemma_congruencetransitive).
assert (Cong F A A E) by (conclude cn_sumofparts).
assert (Cong A E F A) by (conclude lemma_congruencesymmetric).
assert (Cong F A A F) by (conclude cn_equalityreverse).
assert (Cong A E A F) by (conclude lemma_congruencetransitive).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong B E B F) by (conclude lemma_differenceofparts).
assert (eq E F) by (conclude lemma_extensionunique).
assert (BetS A D E) by (conclude cn_equalitysub).
assert (BetS B C E) by (conclude lemma_3_6a).
assert (BetS B D E) by (conclude lemma_3_6a).
assert (eq C D) by (conclude axiom_connectivity).
close.
Qed.

End Euclid.


