Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_27.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_28A : 
   forall A B C D E G H, 
   BetS A G B -> BetS C H D -> BetS E G H -> CongA E G B G H D -> OS B D G H ->
   Par A B C D.
Proof.
intros.
assert (OS D B G H) by (forward_using lemma_samesidesymmetric).
assert (nCol E G B) by (conclude_def CongA ).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G H G) by (conclude_def Col ).
assert (~ Col G H A).
 {
 intro.
 assert (Col H G A) by (forward_using lemma_collinearorder).
 assert (Col E G H) by (conclude_def Col ).
 assert (Col H G E) by (forward_using lemma_collinearorder).
 assert (neq G H) by (forward_using lemma_betweennotequal).
 assert (neq H G) by (conclude lemma_inequalitysymmetric).
 assert (Col G A E) by (conclude lemma_collinear4).
 assert (Col A G E) by (forward_using lemma_collinearorder).
 assert (Col A G B) by (conclude_def Col ).
 assert (neq A G) by (forward_using lemma_betweennotequal).
 assert (Col G E B) by (conclude lemma_collinear4).
 assert (Col E G B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (TS A G H B) by (conclude_def TS ).
assert (TS B G H A) by (conclude lemma_oppositesidesymmetric).
assert (BetS B G A) by (conclude axiom_betweennesssymmetry).
assert (CongA E G B A G H) by (conclude proposition_15a).
assert (CongA A G H E G B) by (conclude lemma_equalanglessymmetric).
assert (CongA A G H G H D) by (conclude lemma_equalanglestransitive).
assert (TS D G H A) by (conclude lemma_planeseparation).
assert (TS A G H D) by (conclude lemma_oppositesidesymmetric).
assert (Par A B C D) by (conclude proposition_27).
close.
Qed.

End Euclid.


