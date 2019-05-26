Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.proposition_36.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_38 : 
   forall A B C D E F P Q, 
   Par P Q B C -> Col P Q A -> Col P Q D -> Cong B C E F -> Col B C E -> Col B C F ->
   ET A B C D E F.
Proof.
intros.
assert (Par B C P Q) by (conclude lemma_parallelsymmetric).
assert (Par C B P Q) by (forward_using lemma_parallelflip).
let Tf:=fresh in
assert (Tf:exists G, (PG A G B C /\ Col P Q G)) by (conclude lemma_triangletoparallelogram);destruct Tf as [G];spliter.
assert (PG G B C A) by (conclude lemma_PGrotate).
assert (nCol P B C) by (forward_using lemma_parallelNC).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq E F) by (conclude axiom_nocollapse).
assert (Par P Q E F) by (conclude lemma_collinearparallel2).
assert (Par E F P Q) by (conclude lemma_parallelsymmetric).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (PG D H F E /\ Col P Q H)) by (conclude lemma_triangletoparallelogram);destruct Tf as [H];spliter.
assert (PG H F E D) by (conclude lemma_PGrotate).
assert (Cong B C F E) by (forward_using lemma_congruenceflip).
assert (nCol P Q B) by (forward_using lemma_parallelNC).
assert (neq P Q) by (forward_using lemma_NCdistinct).
assert (Col G A H) by (conclude lemma_collinear5).
assert (Col G A D) by (conclude lemma_collinear5).
assert (EF G B C A H F E D) by (conclude proposition_36).
assert (EF G B C A E F H D) by (forward_using axiom_EFpermutation).
assert (EF E F H D G B C A) by (conclude axiom_EFsymmetric).
assert (EF E F H D C B G A) by (forward_using axiom_EFpermutation).
let Tf:=fresh in
assert (Tf:exists M, (BetS D M F /\ BetS H M E)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
assert (Col D M F) by (conclude_def Col ).
assert (Col F D M) by (forward_using lemma_collinearorder).
let Tf:=fresh in
assert (Tf:exists m, (BetS A m B /\ BetS G m C)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
assert (Col A m B) by (conclude_def Col ).
assert (Col B A m) by (forward_using lemma_collinearorder).
assert (Par A G B C) by (conclude_def PG ).
assert (nCol A G B) by (forward_using lemma_parallelNC).
assert (nCol B A G) by (forward_using lemma_NCorder).
assert (Par D H F E) by (conclude_def PG ).
assert (nCol D H F) by (forward_using lemma_parallelNC).
assert (nCol F D H) by (forward_using lemma_NCorder).
assert (TS G B A C) by (conclude_def TS ).
assert (TS C B A G) by (conclude lemma_oppositesidesymmetric).
assert (TS H F D E) by (conclude_def TS ).
assert (TS E F D H) by (conclude lemma_oppositesidesymmetric).
assert (Cong_3 F H D D E F) by (conclude proposition_34).
assert (ET F H D D E F) by (conclude axiom_congruentequal).
assert (ET F H D E F D) by (forward_using axiom_ETpermutation).
assert (ET E F D F H D) by (conclude axiom_ETsymmetric).
assert (ET E F D F D H) by (forward_using axiom_ETpermutation).
assert (PG G B C A) by (conclude lemma_PGrotate).
assert (Cong_3 B G A A C B) by (conclude proposition_34).
assert (ET B G A A C B) by (conclude axiom_congruentequal).
assert (ET B G A C B A) by (forward_using axiom_ETpermutation).
assert (ET C B A B G A) by (conclude axiom_ETsymmetric).
assert (ET C B A B A G) by (forward_using axiom_ETpermutation).
assert (ET E F D C B A) by (conclude axiom_halvesofequals).
assert (ET E F D A B C) by (forward_using axiom_ETpermutation).
assert (ET A B C E F D) by (conclude axiom_ETsymmetric).
assert (ET A B C D E F) by (forward_using axiom_ETpermutation).
close.
Qed.

End Euclid.


