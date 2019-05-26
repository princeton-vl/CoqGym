Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_layoffunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthanadditive : 
   forall A B C D E F, 
   Lt A B C D -> BetS A B E -> BetS C D F -> Cong B E D F ->
   Lt A E C F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists b, (BetS C b D /\ Cong C b A B)) by (conclude_def Lt );destruct Tf as [b];spliter.
assert (Cong A B C b) by (conclude lemma_congruencesymmetric).
assert (neq C b) by (forward_using lemma_betweennotequal).
assert (neq b C) by (conclude lemma_inequalitysymmetric).
assert (neq B E) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists e, (BetS C b e /\ Cong b e B E)) by (conclude lemma_extension);destruct Tf as [e];spliter.
assert (Cong B E b e) by (conclude lemma_congruencesymmetric).
assert (Cong A E C e) by (conclude cn_sumofparts).
assert (Cong e D e D) by (conclude cn_congruencereflexive).
assert (BetS e b C) by (conclude axiom_betweennesssymmetry).
assert (BetS C b F) by (conclude lemma_3_6b).
assert (~ BetS b F e).
 {
 intro.
 assert (Cong b F b F) by (conclude cn_congruencereflexive).
 assert (Lt b F b e) by (conclude_def Lt ).
 assert (Cong F D F D) by (conclude cn_congruencereflexive).
 assert (BetS b D F) by (conclude lemma_3_6a).
 assert (BetS F D b) by (conclude axiom_betweennesssymmetry).
 assert (Lt F D F b) by (conclude_def Lt ).
 assert (Cong F b b F) by (conclude cn_equalityreverse).
 assert (Lt F D b F) by (conclude lemma_lessthancongruence).
 assert (Cong F D D F) by (conclude cn_equalityreverse).
 assert (Lt D F b F) by (conclude lemma_lessthancongruence2).
 assert (Cong b e D F) by (conclude lemma_congruencetransitive).
 assert (Cong D F b e) by (conclude lemma_congruencesymmetric).
 assert (Lt b e b F) by (conclude lemma_lessthancongruence2).
 let Tf:=fresh in
 assert (Tf:exists q, (BetS b q F /\ Cong b q b e)) by (conclude_def Lt );destruct Tf as [q];spliter.
 assert (neq b q) by (forward_using lemma_betweennotequal).
 assert (neq b F) by (forward_using lemma_betweennotequal).
 assert (Out b F q) by (conclude lemma_ray4).
 assert (Out b F e) by (conclude lemma_ray4).
 assert (eq q e) by (conclude lemma_layoffunique).
 assert (BetS b e F) by (conclude cn_equalitysub).
 assert (BetS F e F) by (conclude lemma_3_6a).
 assert (~ BetS F e F) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (~ eq F e).
 {
 intro.
 assert (Cong b F B E) by (conclude cn_equalitysub).
 assert (BetS b D F) by (conclude lemma_3_6a).
 assert (BetS F D b) by (conclude axiom_betweennesssymmetry).
 assert (Cong F D F D) by (conclude cn_congruencereflexive).
 assert (Lt F D F b) by (conclude_def Lt ).
 assert (Cong F b b F) by (conclude cn_equalityreverse).
 assert (Lt F D b F) by (conclude lemma_lessthancongruence).
 assert (Cong D F B E) by (conclude lemma_congruencesymmetric).
 assert (Cong F D B E) by (forward_using lemma_congruenceflip).
 assert (Lt B E b F) by (conclude lemma_lessthancongruence2).
 assert (Cong b F b e) by (conclude lemma_congruencetransitive).
 assert (Lt B E b e) by (conclude lemma_lessthancongruence).
 assert (Lt B E B E) by (conclude lemma_lessthancongruence).
 assert (~ Lt B E B E) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (~ ~ BetS b e F).
 {
 intro.
 assert (eq F e) by (conclude lemma_outerconnectivity).
 contradict.
 }
assert (BetS C e F) by (conclude lemma_3_7a).
assert (Cong A E C e) by (conclude cn_sumofparts).
assert (Cong C e A E) by (conclude lemma_congruencesymmetric).
assert (Lt A E C F) by (conclude_def Lt ).
close.
Qed.

End Euclid.


