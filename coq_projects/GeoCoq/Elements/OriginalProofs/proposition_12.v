Require Export GeoCoq.Elements.OriginalProofs.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_12 : 
   forall A B C, 
   nCol A B C ->
   exists X, Perp_at C X A B X.
Proof.
intros.
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS C B E /\ Cong B E C B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (neq C E) by (forward_using lemma_betweennotequal).
assert (neq E C) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS E C F /\ Cong C F E C)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (Cong E C C E) by (conclude cn_equalityreverse).
assert (Cong C E C E) by (conclude cn_congruencereflexive).
assert (Cong C F C E) by (conclude lemma_congruencetransitive).
assert (BetS E B C) by (conclude axiom_betweennesssymmetry).
assert (BetS E B F) by (conclude lemma_3_6b).
let Tf:=fresh in
assert (Tf:exists K, CI K C C E) by (conclude postulate_Euclid3);destruct Tf as [K];spliter.
assert (Cong C E C E) by (conclude cn_congruencereflexive).
assert (Cong C B C B) by (conclude cn_congruencereflexive).
assert (InCirc B K) by (conclude_def InCirc ).
let Tf:=fresh in
assert (Tf:exists P Q, (Col A B P /\ BetS A B Q /\ OnCirc P K /\ OnCirc Q K /\ BetS P B Q)) by (conclude postulate_line_circle);destruct Tf as [P[Q]];spliter.
assert (Col A B Q) by (conclude_def Col ).
assert (Cong C P C E) by (conclude axiom_circle_center_radius).
assert (Cong C Q C E) by (conclude axiom_circle_center_radius).
assert (Cong C E C Q) by (conclude lemma_congruencesymmetric).
assert (Cong C P C Q) by (conclude lemma_congruencetransitive).
assert (Cong P C Q C) by (forward_using lemma_congruenceflip).
assert (neq P Q) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists M, (BetS P M Q /\ Cong M P M Q)) by (conclude proposition_10);destruct Tf as [M];spliter.
assert (Cong P M Q M) by (forward_using lemma_congruenceflip).
assert (Col P M Q) by (conclude_def Col ).
assert (Col P B Q) by (conclude_def Col ).
assert (Col P Q B) by (forward_using lemma_collinearorder).
assert (Col P Q M) by (forward_using lemma_collinearorder).
assert (Col Q B M) by (conclude lemma_collinear4).
assert (Col Q B A) by (forward_using lemma_collinearorder).
assert (neq B Q) by (forward_using lemma_betweennotequal).
assert (neq Q B) by (conclude lemma_inequalitysymmetric).
assert (Col B M A) by (conclude lemma_collinear4).
assert (Col A B M) by (forward_using lemma_collinearorder).
assert (~ eq M C).
 {
 intro.
 assert (Col A B C) by (conclude cn_equalitysub).
 contradict.
 }
assert (Per P M C) by (conclude_def Per ).
assert (eq M M) by (conclude cn_equalityreflexive).
assert (Col C M M) by (conclude_def Col ).
assert (Perp_at C M A B M) by (conclude_def Perp_at ).
close.
Qed.

End Euclid.


