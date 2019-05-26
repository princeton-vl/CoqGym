Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel2.
Require Export GeoCoq.Elements.OriginalProofs.proposition_33.
Require Export GeoCoq.Elements.OriginalProofs.proposition_35.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGsymmetric.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_36A : 
   forall A B C D E F G H M, 
   PG A B C D -> PG E F G H -> Col A D E -> Col A D H -> Col B C F -> Col B C G -> Cong B C F G -> BetS B M H -> BetS C M E ->
   EF A B C D E F G H.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E F G H /\ Par E H F G)) by (conclude_def PG ).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (neq A D) by (forward_using lemma_NCdistinct).
assert (Cong A D B C) by (forward_using proposition_34).
assert (Cong E H F G) by (forward_using proposition_34).
assert (Cong F G E H) by (conclude lemma_congruencesymmetric).
assert (Cong B C E H) by (conclude lemma_congruencetransitive).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq E H) by (conclude axiom_nocollapse).
assert (Par B C E H) by (conclude lemma_collinearparallel2).
assert ((Par B E C H /\ Cong B E C H)) by (conclude proposition_33).
assert (Par E B C H) by (forward_using lemma_parallelflip).
assert (Par E H B C) by (conclude lemma_parallelsymmetric).
assert (PG E B C H) by (conclude_def PG ).
assert (EF A B C D E B C H) by (conclude proposition_35).
assert (Cong F G B C) by (conclude lemma_congruencesymmetric).
assert (Cong G F C B) by (forward_using lemma_congruenceflip).
assert (PG C H E B) by (conclude lemma_PGsymmetric).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Col C F G) by (conclude lemma_collinear4).
assert (Col G F C) by (forward_using lemma_collinearorder).
assert (Col C B F) by (forward_using lemma_collinearorder).
assert (Col C B G) by (forward_using lemma_collinearorder).
assert (Col B F G) by (conclude lemma_collinear4).
assert (Col G F B) by (forward_using lemma_collinearorder).
assert (PG G H E F) by (conclude lemma_PGsymmetric).
assert (EF G H E F C H E B) by (conclude proposition_35).
assert (EF G H E F E B C H) by (forward_using axiom_EFpermutation).
assert (EF E B C H G H E F) by (conclude axiom_EFsymmetric).
assert (EF A B C D G H E F) by (conclude axiom_EFtransitive).
assert (EF A B C D E F G H) by (forward_using axiom_EFpermutation).
close.
Qed.

End Euclid.


