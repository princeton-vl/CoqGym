Require Export GeoCoq.Elements.OriginalProofs.lemma_rightangleNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_8_2 : 
   forall A B C, 
   Per A B C ->
   Per C B A.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS C B E /\ Cong B E B C)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out B C C) by (conclude lemma_ray4).
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (Supp A B C C D) by (conclude_def Supp ).
assert (Out B A A) by (conclude lemma_ray4).
assert (Supp C B A A E) by (conclude_def Supp ).
assert (CongA A B C C B A) by (conclude lemma_ABCequalsCBA).
assert (CongA C B D A B E) by (conclude lemma_supplements).
assert (Cong B C B E) by (conclude lemma_congruencesymmetric).
assert (Cong B D B A) by (forward_using lemma_doublereverse).
assert (~ Col E B A).
 {
 intro.
 assert (Col C B E) by (conclude_def Col ).
 assert (Col E B C) by (forward_using lemma_collinearorder).
 assert (neq B E) by (forward_using lemma_betweennotequal).
 assert (neq E B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col A B E).
 {
 intro.
 assert (Col E B A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A B E E B A) by (conclude lemma_ABCequalsCBA).
assert (CongA C B D E B A) by (conclude lemma_equalanglestransitive).
assert ((Cong C D E A /\ CongA B C D B E A /\ CongA B D C B A E)) by (conclude proposition_04).
assert (Cong A C C D) by (forward_using lemma_congruenceflip).
assert (Cong A C E A) by (conclude lemma_congruencetransitive).
assert (Cong C A E A) by (forward_using lemma_congruenceflip).
assert (Cong C B E B) by (forward_using lemma_congruenceflip).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Per C B A) by (conclude_def Per ).
close.
Qed.

End Euclid.


