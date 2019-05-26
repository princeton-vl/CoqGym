Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray4.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_ABCequalsCBA : 
   forall A B C, 
   nCol A B C ->
   CongA A B C C B A.
Proof.
intros.
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq C B).
 {
 intro.
 assert (Col C B A) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS B A E /\ Cong A E C B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq A B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS B C F /\ Cong C F A B)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (Cong B A F C) by (forward_using lemma_doublereverse).
assert (BetS F C B) by (conclude axiom_betweennesssymmetry).
assert (Cong B E F B) by (conclude cn_sumofparts).
assert (Cong F B B F) by (conclude cn_equalityreverse).
assert (Cong B E B F) by (conclude lemma_congruencetransitive).
assert (Cong B F B E) by (conclude lemma_congruencesymmetric).
assert (Cong E F F E) by (conclude cn_equalityreverse).
assert (Out B A E) by (conclude lemma_ray4).
assert (Out B C F) by (conclude lemma_ray4).
assert (CongA A B C C B A) by (conclude_def CongA ).
close.
Qed.

End Euclid.


