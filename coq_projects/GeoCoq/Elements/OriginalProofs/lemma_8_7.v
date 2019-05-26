Require Export GeoCoq.Elements.OriginalProofs.lemma_droppedperpendicularunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_8_7 : 
   forall A B C, 
   Per C B A ->
   ~ Per A C B.
Proof.
intros.
assert (neq B A) by (conclude_def Per ).
assert (Per A B C) by (conclude lemma_8_2).
assert (neq B C) by (conclude_def Per ).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS B C E /\ Cong C E C B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (Col B C E) by (conclude_def Col ).
assert (Col E C B) by (forward_using lemma_collinearorder).
assert (Per A B C) by (conclude lemma_8_2).
assert (Out B C E) by (conclude lemma_ray4).
assert (Per A B E) by (conclude lemma_8_3).
assert (Per E B A) by (conclude lemma_8_2).
assert (~ Per A C B).
 {
 intro.
 assert (Per B C A) by (conclude lemma_8_2).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS B C F /\ Cong B C F C /\ Cong B A F A /\ neq C A)) by (conclude_def Per );destruct Tf as [F];spliter.
 assert (Cong F C B C) by (conclude lemma_congruencesymmetric).
 assert (Cong C F B C) by (forward_using lemma_congruenceflip).
 assert (Cong C E B C) by (forward_using lemma_congruenceflip).
 assert (Cong B C C E) by (conclude lemma_congruencesymmetric).
 assert (Cong C F C E) by (conclude lemma_congruencetransitive).
 assert (eq F E) by (conclude lemma_extensionunique).
 assert (BetS E C B) by (conclude axiom_betweennesssymmetry).
 assert (Cong F A B A) by (conclude lemma_congruencesymmetric).
 assert (Cong E A B A) by (conclude cn_equalitysub).
 assert (Cong E C B C) by (forward_using lemma_congruenceflip).
 assert (Per E C A) by (conclude_def Per ).
 assert (eq C B) by (conclude lemma_droppedperpendicularunique).
 contradict.
 }
close.
Qed.

End Euclid.


