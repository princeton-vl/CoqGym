Require Export GeoCoq.Elements.OriginalProofs.lemma_sameside2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_10_12.
Require Export GeoCoq.Elements.OriginalProofs.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_erectedperpendicularunique : 
   forall A B C E, 
   Per A B C -> Per A B E -> OS C E A B ->
   Out B C E.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (neq B E) by (conclude_def Per ).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (Out B E H /\ Cong B H B C)) by (conclude lemma_layoff);destruct Tf as [H];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (OS C H A B) by (conclude lemma_sameside2).
assert (Per A B H) by (conclude lemma_8_3).
assert (Cong B C B H) by (conclude lemma_congruencesymmetric).
assert (Cong A C A H) by (conclude lemma_10_12).
assert (Cong C A H A) by (forward_using lemma_congruenceflip).
assert (Cong C B H B) by (forward_using lemma_congruenceflip).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (nCol A B C) by (conclude lemma_rightangleNC).
 contradict.
 }
assert (eq C H) by (conclude proposition_07).
assert (Out B E C) by (conclude cn_equalitysub).
assert (Out B C E) by (conclude lemma_ray5).
close.
Qed.

End Euclid.


