Require Export GeoCoq.Elements.OriginalProofs.lemma_notperp.
Require Export GeoCoq.Elements.OriginalProofs.lemma_pointreflectionisometry.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_11B : 
   forall A B C P, 
   BetS A C B -> nCol A B P ->
   exists X, Per A C X /\ TS X A B P.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M, (nCol A B M /\ OS M P A B /\ ~ Per A C M)) by (conclude lemma_notperp);destruct Tf as [M];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists Q, Perp_at M Q A B Q) by (conclude proposition_12);destruct Tf as [Q];spliter.
let Tf:=fresh in
assert (Tf:exists E, (Col M Q Q /\ Col A B Q /\ Col A B E /\ Per E Q M)) by (conclude_def Perp_at );destruct Tf as [E];spliter.
assert (~ eq M Q).
 {
 intro.
 assert (Col A B M) by (conclude cn_equalitysub).
 contradict.
 }
assert (neq Q M) by (conclude lemma_inequalitysymmetric).
assert (Col A B C) by (conclude_def Col ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (Col B A C) by (forward_using lemma_collinearorder).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (~ eq C Q).
 {
 intro.
 assert (Per E C M) by (conclude cn_equalitysub).
 assert (Col A E C) by (conclude lemma_collinear4).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (neq A C) by (forward_using lemma_betweennotequal).
 assert (Per A C M) by (conclude lemma_collinearright).
 contradict.
 }
assert (Col C Q E) by (conclude lemma_collinear5).
assert (Col E Q C) by (forward_using lemma_collinearorder).
assert (Per C Q M) by (conclude lemma_collinearright).
assert (neq Q C) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists G, (BetS Q G C /\ Cong G Q G C)) by (conclude proposition_10);destruct Tf as [G];spliter.
assert (~ eq M G).
 {
 intro.
 assert (BetS Q M C) by (conclude cn_equalitysub).
 assert (Col Q M C) by (conclude_def Col ).
 assert (Col B Q C) by (conclude lemma_collinear4).
 assert (Col Q C M) by (forward_using lemma_collinearorder).
 assert (Col Q C B) by (forward_using lemma_collinearorder).
 assert (neq Q C) by (forward_using lemma_betweennotequal).
 assert (Col C M B) by (conclude lemma_collinear4).
 assert (Col C B M) by (forward_using lemma_collinearorder).
 assert (Col C B A) by (forward_using lemma_collinearorder).
 assert (neq C B) by (forward_using lemma_betweennotequal).
 assert (Col B M A) by (conclude lemma_collinear4).
 assert (Col A B M) by (forward_using lemma_collinearorder).
 contradict.
 }
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS M G H /\ Cong G H M G)) by (conclude lemma_extension);destruct Tf as [H];spliter.
assert (Cong M G G H) by (conclude lemma_congruencesymmetric).
assert (Midpoint M G H) by (conclude_def Midpoint ).
assert (Cong Q G G C) by (forward_using lemma_congruenceflip).
assert (Midpoint Q G C) by (conclude_def Midpoint ).
assert (Col Q G C) by (conclude_def Col ).
assert (Col C Q G) by (forward_using lemma_collinearorder).
assert (neq Q G) by (forward_using lemma_betweennotequal).
assert (neq G Q) by (conclude lemma_inequalitysymmetric).
assert (Per G Q M) by (conclude lemma_collinearright).
let Tf:=fresh in
assert (Tf:exists J, (BetS M Q J /\ Cong Q J M Q)) by (conclude lemma_extension);destruct Tf as [J];spliter.
assert (Cong M Q Q J) by (conclude lemma_congruencesymmetric).
assert (Per M Q G) by (conclude lemma_8_2).
assert (Cong M G J G) by (conclude lemma_rightreverse).
assert (BetS J Q M) by (conclude axiom_betweennesssymmetry).
assert (Cong J Q M Q) by (forward_using lemma_congruenceflip).
assert (Cong J G M G) by (conclude lemma_congruencesymmetric).
assert (Per J Q G) by (conclude_def Per ).
assert (~ eq J G).
 {
 intro.
 assert (Col J Q G) by (conclude_def Col ).
 assert (nCol J Q G) by (conclude lemma_rightangleNC).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists K, (BetS J G K /\ Cong G K J G)) by (conclude lemma_extension);destruct Tf as [K];spliter.
assert (Cong J G G K) by (conclude lemma_congruencesymmetric).
assert (Midpoint J G K) by (conclude_def Midpoint ).
assert (Cong M Q H C) by (conclude lemma_pointreflectionisometry).
assert (neq J Q) by (forward_using lemma_betweennotequal).
assert (neq Q J) by (conclude lemma_inequalitysymmetric).
assert (neq M J) by (forward_using lemma_betweennotequal).
assert (Cong Q J C K) by (conclude lemma_pointreflectionisometry).
assert (Cong M J H K) by (conclude lemma_pointreflectionisometry).
assert (BetS H C K) by (conclude lemma_betweennesspreserved).
assert (Cong H G G M) by (forward_using lemma_congruenceflip).
assert (Cong G M J G) by (forward_using lemma_congruenceflip).
assert (Cong H G J G) by (conclude lemma_congruencetransitive).
assert (Cong J G G K) by (conclude lemma_congruencesymmetric).
assert (Cong H G G K) by (conclude lemma_congruencetransitive).
assert (Cong H G K G) by (forward_using lemma_congruenceflip).
assert (neq G C) by (forward_using lemma_betweennotequal).
assert (Cong H C M Q) by (conclude lemma_congruencesymmetric).
assert (Cong M Q Q J) by (conclude lemma_congruencesymmetric).
assert (Cong H C Q J) by (conclude lemma_congruencetransitive).
assert (Cong H C C K) by (conclude lemma_congruencetransitive).
assert (Cong H C K C) by (forward_using lemma_congruenceflip).
assert (neq G C) by (forward_using lemma_betweennotequal).
assert (neq C G) by (conclude lemma_inequalitysymmetric).
assert (Per H C G) by (conclude_def Per ).
assert (Per G C H) by (conclude lemma_8_2).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (Col Q C A) by (conclude lemma_collinear5).
assert (Col Q C G) by (forward_using lemma_collinearorder).
assert (Col C A G) by (conclude lemma_collinear4).
assert (Col G C A) by (forward_using lemma_collinearorder).
assert (neq A C) by (forward_using lemma_betweennotequal).
assert (Per A C H) by (conclude lemma_collinearright).
assert (Col C A B) by (forward_using lemma_collinearorder).
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (Col A G B) by (conclude lemma_collinear4).
assert (Col A B G) by (forward_using lemma_collinearorder).
assert (OS P M A B) by (forward_using lemma_samesidesymmetric).
assert (TS M A B H) by (conclude_def TS ).
assert (TS P A B H) by (conclude lemma_planeseparation).
assert (TS H A B P) by (conclude lemma_oppositesidesymmetric).
close.
Qed.

End Euclid.
