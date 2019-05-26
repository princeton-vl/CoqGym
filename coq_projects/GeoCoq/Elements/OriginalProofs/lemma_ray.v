Require Export GeoCoq.Elements.OriginalProofs.lemma_ray2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_3_7b.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ray : 
   forall A B P, 
   Out A B P -> neq P B -> ~ BetS A P B ->
   BetS A B P.
Proof.
intros.
assert (neq A B) by (conclude lemma_ray2).
let Tf:=fresh in
assert (Tf:exists E, (BetS E A P /\ BetS E A B)) by (conclude_def Out );destruct Tf as [E];spliter.
assert (neq A P) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong B D A P)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert (Cong D B B D) by (conclude cn_equalityreverse).
assert (Cong D B A P) by (conclude lemma_congruencetransitive).
assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
assert (Lt A P D A) by (conclude_def Lt ).
assert (Cong D A A D) by (conclude cn_equalityreverse).
assert (Lt A P A D) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists F, (BetS A F D /\ Cong A F A P)) by (conclude_def Lt );destruct Tf as [F];spliter.
assert (BetS E A D) by (conclude lemma_3_7b).
assert (BetS E A F) by (conclude axiom_innertransitivity).
assert (Cong A P A F) by (conclude lemma_congruencesymmetric).
assert (eq P F) by (conclude lemma_extensionunique).
assert (BetS A P D) by (conclude cn_equalitysub).
assert (~ ~ BetS A B P).
 {
 intro.
 assert (eq B P) by (conclude axiom_connectivity).
 assert (neq B P) by (conclude lemma_inequalitysymmetric).
 contradict.
 }
close.
Qed.

End Euclid.


