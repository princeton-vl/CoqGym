Require Export GeoCoq.Elements.OriginalProofs.proposition_27.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27B : 
   forall A D E F, 
   CongA A E F E F D -> TS A E F D ->
   Par A E F D.
Proof.
intros.
assert (neq A E) by (forward_using lemma_angledistinct).
let Tf:=fresh in
assert (Tf:exists B, (BetS A E B /\ Cong E B A E)) by (conclude lemma_extension);destruct Tf as [B];spliter.
assert (neq F D) by (forward_using lemma_angledistinct).
assert (neq D F) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists C, (BetS D F C /\ Cong F C F D)) by (conclude lemma_extension);destruct Tf as [C];spliter.
assert (BetS C F D) by (conclude axiom_betweennesssymmetry).
assert (Par A B C D) by (conclude proposition_27).
assert (Col D F C) by (conclude_def Col ).
assert (Col C D F) by (forward_using lemma_collinearorder).
assert (Par A B F D) by (conclude lemma_collinearparallel).
assert (Par F D A B) by (conclude lemma_parallelsymmetric).
assert (Par F D B A) by (forward_using lemma_parallelflip).
assert (Col A E B) by (conclude_def Col ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq E A) by (conclude lemma_inequalitysymmetric).
assert (Par F D E A) by (conclude lemma_collinearparallel).
assert (Par F D A E) by (forward_using lemma_parallelflip).
assert (Par A E F D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.


