Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_11 : 
   forall A B C, 
   BetS A C B ->
   exists X, Per A C X.
Proof.
intros.
assert (neq A C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists E, (BetS A C E /\ Cong C E A C)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (neq A E) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists F, (equilateral A E F /\ Triangle A E F)) by (conclude proposition_01);destruct Tf as [F];spliter.
assert (Cong E F F A) by (conclude_def equilateral ).
assert (Cong A F F E) by (forward_using lemma_doublereverse).
assert (Cong A F E F) by (forward_using lemma_congruenceflip).
assert (~ eq C F).
 {
 intro.
 assert (Col A C E) by (conclude_def Col ).
 assert (Col A F E) by (conclude cn_equalitysub).
 assert (Col A E F) by (forward_using lemma_collinearorder).
 assert (nCol A E F) by (conclude_def Triangle ).
 contradict.
 }
assert (Cong C A E C) by (forward_using lemma_doublereverse).
assert (Cong A C E C) by (forward_using lemma_congruenceflip).
assert (Per A C F) by (conclude_def Per ).
close.
Qed.

End Euclid.


