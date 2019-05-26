Require Export GeoCoq.Elements.OriginalProofs.proposition_10.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_09 : 
   forall A B C, 
   nCol B A C ->
   exists X, CongA B A X X A C /\ InAngle B A C X.
Proof.
intros.
assert (~ eq A B).
 {
 intro.
 assert (eq B A) by (conclude lemma_equalitysymmetric).
 assert (Col B A C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (Col B A C) by (conclude_def Col ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (Out A C E /\ Cong A E A B)) by (conclude lemma_layoff);destruct Tf as [E];spliter.
assert (~ eq B E).
 {
 intro.
 assert (Col A B E) by (conclude_def Col ).
 assert (Col A C E) by (conclude lemma_rayimpliescollinear).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (Col E A C) by (forward_using lemma_collinearorder).
 assert (neq A E) by (conclude lemma_raystrict).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists F, (BetS B F E /\ Cong F B F E)) by (conclude proposition_10);destruct Tf as [F];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (Cong A F A F) by (conclude cn_congruencereflexive).
assert (Cong A B A E) by (conclude lemma_congruencesymmetric).
assert (Cong E F B F) by (forward_using lemma_doublereverse).
assert (Cong B F E F) by (conclude lemma_congruencesymmetric).
assert (~ Col B A F).
 {
 intro.
 assert (Col B F E) by (conclude_def Col ).
 assert (Col F B E) by (forward_using lemma_collinearorder).
 assert (Col F B A) by (forward_using lemma_collinearorder).
 assert (neq B F) by (forward_using lemma_betweennotequal).
 assert (neq F B) by (conclude lemma_inequalitysymmetric).
 assert (Col B E A) by (conclude lemma_collinear4).
 assert (Col A C E) by (conclude lemma_rayimpliescollinear).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (Col E A C) by (forward_using lemma_collinearorder).
 assert (neq A E) by (conclude lemma_raystrict).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out A B B) by (conclude lemma_ray4).
assert (~ eq A F).
 {
 intro.
 assert (Col B A F) by (conclude_def Col ).
 contradict.
 }
assert (Out A F F) by (conclude lemma_ray4).
assert (CongA B A F C A F) by (conclude_def CongA ).
assert (CongA C A F B A F) by (conclude lemma_equalanglessymmetric).
assert (nCol C A F) by (conclude_def CongA ).
assert (CongA C A F F A C) by (conclude lemma_ABCequalsCBA).
assert (CongA B A F F A C) by (conclude lemma_equalanglestransitive).
assert (InAngle B A C F) by (conclude_def InAngle ).
close.
Qed.

End Euclid.


