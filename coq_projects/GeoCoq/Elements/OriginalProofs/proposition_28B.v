Require Export GeoCoq.Elements.OriginalProofs.lemma_supplementsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_27.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_28B : 
   forall A B C D G H, 
   BetS A G B -> BetS C H D -> RT B G H G H D -> OS B D G H ->
   Par A B C D.
Proof.
intros.
assert (OS D B G H) by (forward_using lemma_samesidesymmetric).
let Tf:=fresh in
assert (Tf:exists a b c d e, (Supp a b c e d /\ CongA B G H a b c /\ CongA G H D e b d)) by (conclude_def RT );destruct Tf as [a[b[c[d[e]]]]];spliter.
assert (CongA a b c B G H) by (conclude lemma_equalanglessymmetric).
assert (neq G H) by (forward_using lemma_angledistinct).
assert (CongA e b d G H D) by (conclude lemma_equalanglessymmetric).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Out G H H) by (conclude lemma_ray4).
assert (Supp A G H H B) by (conclude_def Supp ).
assert (Supp B G H H A) by (conclude lemma_supplementsymmetric).
assert (CongA e b d H G A) by (conclude lemma_supplements).
assert (CongA G H D e b d) by (conclude lemma_equalanglessymmetric).
assert (CongA G H D H G A) by (conclude lemma_equalanglestransitive).
assert (nCol H G A) by (conclude lemma_equalanglesNC).
assert (CongA H G A A G H) by (conclude lemma_ABCequalsCBA).
assert (CongA G H D A G H) by (conclude lemma_equalanglestransitive).
assert (CongA A G H G H D) by (conclude lemma_equalanglessymmetric).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G H G) by (conclude_def Col ).
assert (nCol A G H) by (conclude lemma_equalanglesNC).
assert (~ Col G H A).
 {
 intro.
 assert (Col A G H) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (TS A G H B) by (conclude_def TS ).
assert (TS B G H A) by (conclude lemma_oppositesidesymmetric).
assert (TS D G H A) by (conclude lemma_planeseparation).
assert (TS A G H D) by (conclude lemma_oppositesidesymmetric).
assert (Par A B C D) by (conclude proposition_27).
close.
Qed.

End Euclid.
