Require Export GeoCoq.Elements.OriginalProofs.proposition_20.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TGsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TGflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_22.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23 : 
   forall A B C D E, 
   neq A B -> nCol D C E ->
   exists X Y, Out A B Y /\ CongA X A Y D C E.
Proof.
intros.
assert (~ Col E C D).
 {
 intro.
 assert (Col D C E) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col C E D).
 {
 intro.
 assert (Col D C E) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle D C E) by (conclude_def Triangle ).
assert (Triangle C E D) by (conclude_def Triangle ).
assert (Triangle E C D) by (conclude_def Triangle ).
assert (TG C D D E C E) by (conclude proposition_20).
assert (TG C E E D C D) by (conclude proposition_20).
assert (TG E C C D E D) by (conclude proposition_20).
assert (TG C D E C E D) by (conclude lemma_TGsymmetric).
assert (TG C D D E E C) by (forward_using lemma_TGflip).
assert (TG D E C D E C) by (conclude lemma_TGsymmetric).
assert (TG E D C D E C) by (forward_using lemma_TGflip).
assert (TG C D E D E C) by (conclude lemma_TGsymmetric).
assert (TG E C E D C D) by (forward_using lemma_TGflip).
let Tf:=fresh in
assert (Tf:exists G F, (Cong A G E C /\ Cong A F C D /\ Cong G F E D /\ Out A B G /\ Triangle A G F)) 
 by (conclude proposition_22);destruct Tf as [G[F]];spliter.
assert (Cong A G C E) by (forward_using lemma_congruenceflip).
assert (Cong F G D E) by (forward_using lemma_congruenceflip).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (~ eq C E).
 {
 intro.
 assert (Col D C E) by (conclude_def Col ).
 contradict.
 }
assert (~ eq C D).
 {
 intro.
 assert (Col C D E) by (conclude_def Col ).
 assert (Col D C E) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out C E E) by (conclude lemma_ray4).
assert (Out C D D) by (conclude lemma_ray4).
assert (~ Col F A G).
 {
 intro.
 assert (Col A G F) by (forward_using lemma_collinearorder).
 assert (nCol A G F) by (conclude_def Triangle ).
 contradict.
 }
assert (~ eq A F).
 {
 intro.
 assert (Col A F G) by (conclude_def Col ).
 assert (Col F A G) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out A F F) by (conclude lemma_ray4).
assert (~ eq A G).
 {
 intro.
 assert (Col A G F) by (conclude_def Col ).
 assert (Col F A G) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out A G G) by (conclude lemma_ray4).
assert (CongA F A G D C E) by (conclude_def CongA ).
close.
Qed.

End Euclid.


