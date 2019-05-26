Require Export GeoCoq.Elements.OriginalProofs.lemma_8_2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_3.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_altitudebisectsbase : 
   forall A B M P, 
   BetS A M B -> Cong A P B P -> Per A M P ->
   Midpoint A M B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists C, (BetS A M C /\ Cong A M C M /\ Cong A P C P /\ neq M P)) by (conclude_def Per );destruct Tf as [C];spliter.
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (Cong C M A M) by (conclude lemma_congruencesymmetric).
assert (Cong C P A P) by (conclude lemma_congruencesymmetric).
assert (Per C M P) by (conclude_def Per ).
assert (Per P M A) by (conclude lemma_8_2).
let Tf:=fresh in
assert (Tf:exists Q, (BetS P M Q /\ Cong P M Q M /\ Cong P A Q A /\ neq M A)) by (conclude_def Per );destruct Tf as [Q];spliter.
assert (Cong Q M P M) by (conclude lemma_congruencesymmetric).
assert (Per P M C) by (conclude lemma_8_2).
assert (Out M C B) by (conclude_def Out ).
assert (Per P M B) by (conclude lemma_8_3).
let Tf:=fresh in
assert (Tf:exists E, (BetS P M E /\ Cong P M E M /\ Cong P B E B /\ neq M B)) by (conclude_def Per );destruct Tf as [E];spliter.
assert (Cong P A P B) by (forward_using lemma_congruenceflip).
assert (Cong M Q P M) by (forward_using lemma_congruenceflip).
assert (Cong P M M Q) by (conclude lemma_congruencesymmetric).
assert (Cong E M P M) by (conclude lemma_congruencesymmetric).
assert (Cong E M M Q) by (conclude lemma_congruencetransitive).
assert (Cong M E M Q) by (forward_using lemma_congruenceflip).
assert (Cong M Q M E) by (conclude lemma_congruencesymmetric).
assert (neq P M) by (forward_using lemma_betweennotequal).
assert (eq Q E) by (conclude lemma_extensionunique).
assert (Cong P B Q B) by (conclude cn_equalitysub).
assert (Cong A P P B) by (forward_using lemma_congruenceflip).
assert (Cong A P Q B) by (conclude lemma_congruencetransitive).
assert (Cong A Q A P) by (forward_using lemma_doublereverse).
assert (Cong A Q Q B) by (conclude lemma_congruencetransitive).
assert (Cong A Q B Q) by (forward_using lemma_congruenceflip).
assert (Cong P Q P Q) by (conclude cn_congruencereflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (nCol A M P) by (conclude lemma_rightangleNC).
assert (~ Col A P M).
 {
 intro.
 assert (Col A M P) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq A P).
 {
 intro.
 assert (Col A P M) by (conclude_def Col ).
 contradict.
 }
assert (neq P A) by (conclude lemma_inequalitysymmetric).
assert (Out P A A) by (conclude lemma_ray4).
assert (~ eq P B).
 {
 intro.
 assert (Cong A P B B) by (conclude cn_equalitysub).
 assert (~ neq A P).
  {
  intro.
  assert (neq B B) by (conclude axiom_nocollapse).
  assert (eq B B) by (conclude cn_equalityreflexive).
  contradict.
  }
 contradict.
 }
assert (Out P B B) by (conclude lemma_ray4).
assert (Out P M Q) by (conclude lemma_ray4).
assert (CongA A P M B P M) by (conclude_def CongA ).
assert (Cong P M P M) by (conclude cn_congruencereflexive).
assert ((Cong A M B M /\ CongA P A M P B M /\ CongA P M A P M B)) by (conclude proposition_04).
assert (Cong A M M B) by (forward_using lemma_congruenceflip).
assert (Midpoint A M B) by (conclude_def Midpoint ).
close.
Qed.

End Euclid.
