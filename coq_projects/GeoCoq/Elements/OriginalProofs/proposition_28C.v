Require Export GeoCoq.Elements.OriginalProofs.proposition_28B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.


Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_28C : 
   forall B D G H, 
   RT B G H G H D -> OS B D G H ->
   Par G B H D.
Proof.
intros.
assert (nCol G H B) by (conclude_def OS ).
assert (nCol G H D) by (conclude_def OS ).
assert (neq H D) by (forward_using lemma_NCdistinct).
assert (neq D H) by (conclude lemma_inequalitysymmetric).
assert (neq G B) by (forward_using lemma_NCdistinct).
assert (neq B G) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists A, (BetS B G A /\ Cong G A G B)) by (conclude lemma_extension);destruct Tf as [A];spliter.
assert (BetS A G B) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists C, (BetS D H C /\ Cong H C H D)) by (conclude lemma_extension);destruct Tf as [C];spliter.
assert (BetS C H D) by (conclude axiom_betweennesssymmetry).
assert (Par A B C D) by (conclude proposition_28B).
assert (Col D H C) by (conclude_def Col ).
assert (Col C D H) by (forward_using lemma_collinearorder).
assert (neq H D) by (forward_using lemma_NCdistinct).
assert (Par A B H D) by (conclude lemma_collinearparallel).
assert (Par H D A B) by (conclude lemma_parallelsymmetric).
assert (Col B G A) by (conclude_def Col ).
assert (Col A B G) by (forward_using lemma_collinearorder).
assert (Par H D G B) by (conclude lemma_collinearparallel).
assert (Par G B H D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.
