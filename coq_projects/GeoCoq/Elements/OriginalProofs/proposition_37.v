Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_37 : 
   forall A B C D, 
   Par A D B C ->
   ET A B C D B C.
Proof.
intros.
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par C B A D) by (forward_using lemma_parallelflip).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col A D A) by (conclude_def Col ).
assert (Col A D D) by (conclude_def Col ).
let Tf:=fresh in
assert (Tf:exists E, (PG A E B C /\ Col A D E)) by (conclude lemma_triangletoparallelogram);destruct Tf as [E];spliter.
let Tf:=fresh in
assert (Tf:exists F, (PG D F B C /\ Col A D F)) by (conclude lemma_triangletoparallelogram);destruct Tf as [F];spliter.
assert (PG E B C A) by (conclude lemma_PGrotate).
assert (PG F B C D) by (conclude lemma_PGrotate).
assert (Col D A F) by (forward_using lemma_collinearorder).
assert (Col D A E) by (forward_using lemma_collinearorder).
assert (nCol C A D) by (forward_using lemma_parallelNC).
assert (neq A D) by (forward_using lemma_NCdistinct).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (Col A F E) by (conclude lemma_collinear4).
assert (Col E A D) by (forward_using lemma_collinearorder).
assert (Col E A F) by (forward_using lemma_collinearorder).
assert (EF E B C A F B C D) by (conclude proposition_35).
assert (Cong_3 B E A A C B) by (conclude proposition_34).
assert (Cong_3 B F D D C B) by (conclude proposition_34).
let Tf:=fresh in
assert (Tf:exists M, (BetS E M C /\ BetS B M A)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
let Tf:=fresh in
assert (Tf:exists m, (BetS F m C /\ BetS B m D)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
assert (Col B M A) by (conclude_def Col ).
assert (Col B m D) by (conclude_def Col ).
assert (Col B A M) by (forward_using lemma_collinearorder).
assert (Col B D m) by (forward_using lemma_collinearorder).
assert (Par E B C A) by (conclude_def PG ).
assert (nCol E B A) by (forward_using lemma_parallelNC).
assert (nCol B A E) by (forward_using lemma_NCorder).
assert (TS E B A C) by (conclude_def TS ).
assert (TS C B A E) by (conclude lemma_oppositesidesymmetric).
assert (Par D F B C) by (conclude_def PG ).
assert (nCol D F B) by (forward_using lemma_parallelNC).
assert (nCol B D F) by (forward_using lemma_NCorder).
assert (TS F B D C) by (conclude_def TS ).
assert (TS C B D F) by (conclude lemma_oppositesidesymmetric).
assert (ET B E A A C B) by (conclude axiom_congruentequal).
assert (ET B E A C B A) by (forward_using axiom_ETpermutation).
assert (ET C B A B E A) by (conclude axiom_ETsymmetric).
assert (ET C B A B A E) by (forward_using axiom_ETpermutation).
assert (ET B F D D C B) by (conclude axiom_congruentequal).
assert (ET B F D C B D) by (forward_using axiom_ETpermutation).
assert (ET C B D B F D) by (conclude axiom_ETsymmetric).
assert (ET C B D B D F) by (forward_using axiom_ETpermutation).
assert (EF E B C A C B F D) by (forward_using axiom_EFpermutation).
assert (EF C B F D E B C A) by (conclude axiom_EFsymmetric).
assert (EF C B F D C B E A) by (forward_using axiom_EFpermutation).
assert (EF C B E A C B F D) by (conclude axiom_EFsymmetric).
assert (ET C B A C B D) by (conclude axiom_halvesofequals).
assert (ET C B A D B C) by (forward_using axiom_ETpermutation).
assert (ET D B C C B A) by (conclude axiom_ETsymmetric).
assert (ET D B C A B C) by (forward_using axiom_ETpermutation).
assert (ET A B C D B C) by (conclude axiom_ETsymmetric).
close.
Qed.

End Euclid.


