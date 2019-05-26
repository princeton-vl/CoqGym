Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthantransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy2.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_subtractequals : 
   forall A B C D E, 
   BetS A B C -> BetS A D E -> Cong B C D E -> BetS A C E ->
   BetS A B D.
Proof.
intros.
assert (~ BetS A D B).
 {
 intro.
 assert (BetS A D C) by (conclude lemma_3_6b).
 assert (BetS A D C) by (conclude lemma_3_6b).
 assert (BetS B C E) by (conclude lemma_3_6a).
 assert (Cong B C B C) by (conclude cn_congruencereflexive).
 assert (Lt B C B E) by (conclude_def Lt ).
 assert (Cong B E E B) by (conclude cn_equalityreverse).
 assert (Lt B C E B) by (conclude lemma_lessthancongruence).
 assert (BetS D C E) by (conclude lemma_3_6a).
 assert (BetS D B C) by (conclude lemma_3_6a).
 assert (BetS D B E) by (conclude lemma_3_6b).
 assert (BetS E B D) by (conclude axiom_betweennesssymmetry).
 assert (Cong E B E B) by (conclude cn_congruencereflexive).
 assert (Lt E B E D) by (conclude_def Lt ).
 assert (Cong E D D E) by (conclude cn_equalityreverse).
 assert (Lt E B D E) by (conclude lemma_lessthancongruence).
 assert (Lt B C D E) by (conclude lemma_lessthantransitive).
 assert (Cong D E B C) by (conclude lemma_congruencesymmetric).
 assert (Lt B C B C) by (conclude lemma_lessthancongruence).
 assert (~ Lt B C B C) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (~ ~ BetS A B D).
 {
 intro.
 assert (BetS A B E) by (conclude lemma_3_6b).
 assert (eq B D) by (conclude axiom_connectivity).
 assert (Cong A B A B) by (conclude cn_congruencereflexive).
 assert (Cong A B A D) by (conclude cn_equalitysub).
 assert (Cong A C A E) by (conclude cn_sumofparts).
 assert (BetS A B E) by (conclude cn_equalitysub).
 assert (neq A B) by (forward_using lemma_betweennotequal).
 assert (Out A B E) by (conclude lemma_ray4).
 assert (Out A B C) by (conclude lemma_ray4).
 assert (eq C E) by (conclude lemma_layoffunique).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 contradict.
 }
close.
Qed.

End Euclid.


