Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthantransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_midpointunique : 
   forall A B C D, 
   Midpoint A B C -> Midpoint A D C ->
   eq B D.
Proof.
intros.
assert ((BetS A B C /\ Cong A B B C)) by (conclude_def Midpoint ).
assert ((BetS A D C /\ Cong A D D C)) by (conclude_def Midpoint ).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (~ BetS C D B).
 {
 intro.
 assert (BetS B D C) by (conclude axiom_betweennesssymmetry).
 assert (BetS A B D) by (conclude axiom_innertransitivity).
 assert (Lt A B A D) by (conclude_def Lt ).
 assert (Cong A D C D) by (forward_using lemma_congruenceflip).
 assert (Lt A B C D) by (conclude lemma_lessthancongruence).
 assert (BetS C D B) by (conclude axiom_betweennesssymmetry).
 assert (Cong C D C D) by (conclude cn_congruencereflexive).
 assert (Lt C D C B) by (conclude_def Lt ).
 assert (Lt A B C B) by (conclude lemma_lessthantransitive).
 assert (Cong C B B C) by (conclude cn_equalityreverse).
 assert (Lt A B B C) by (conclude lemma_lessthancongruence).
 assert (Cong B C A B) by (conclude lemma_congruencesymmetric).
 assert (Lt A B A B) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists E, (BetS A E B /\ Cong A E A B)) by (conclude_def Lt );destruct Tf as [E];spliter.
 assert (~ Cong A E A B) by (conclude lemma_partnotequalwhole).
 contradict.
 }
assert (~ BetS C B D).
 {
 intro.
 assert (BetS D B C) by (conclude axiom_betweennesssymmetry).
 assert (BetS A D B) by (conclude axiom_innertransitivity).
 assert (Cong A D A D) by (conclude cn_congruencereflexive).
 assert (Lt A D A B) by (conclude_def Lt ).
 assert (Cong A B C B) by (forward_using lemma_congruenceflip).
 assert (Lt A D C B) by (conclude lemma_lessthancongruence).
 assert (BetS C B D) by (conclude axiom_betweennesssymmetry).
 assert (Cong C B C B) by (conclude cn_congruencereflexive).
 assert (Lt C B C D) by (conclude_def Lt ).
 assert (Lt A D C D) by (conclude lemma_lessthantransitive).
 assert (Cong C D D C) by (conclude cn_equalityreverse).
 assert (Lt A D D C) by (conclude lemma_lessthancongruence).
 assert (Cong D C C D) by (conclude lemma_congruencesymmetric).
 assert (Lt A D C D) by (conclude lemma_lessthancongruence).
 assert (Cong D C A D) by (conclude lemma_congruencesymmetric).
 assert (Cong C D A D) by (forward_using lemma_congruenceflip).
 assert (Lt A D A D) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS A F D /\ Cong A F A D)) by (conclude_def Lt );destruct Tf as [F];spliter.
 assert (~ Cong A F A D) by (conclude lemma_partnotequalwhole).
 contradict.
 }
assert (BetS C D A) by (conclude axiom_betweennesssymmetry).
assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
assert (eq B D) by (conclude axiom_connectivity).
close.
Qed.

End Euclid.


