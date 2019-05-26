Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crisscross.
Require Export GeoCoq.Elements.OriginalProofs.proposition_33.
Require Export GeoCoq.Elements.OriginalProofs.proposition_35.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_36 : 
   forall A B C D E F G H, 
   PG A B C D -> PG E F G H -> Col A D E -> Col A D H -> Col B C F -> Col B C G -> Cong B C F G ->
   EF A B C D E F G H.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E F G H /\ Par E H F G)) by (conclude_def PG ).
assert (nCol E H G) by (forward_using lemma_parallelNC).
assert (neq E H) by (forward_using lemma_NCdistinct).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (Cong E H F G) by (forward_using proposition_34).
assert (Cong F G E H) by (conclude lemma_congruencesymmetric).
assert (Cong B C E H) by (conclude lemma_congruencetransitive).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par B C E H) by (conclude lemma_collinearparallel2).
assert (Par E H B C) by (conclude lemma_parallelsymmetric).
assert (Cong E H B C) by (conclude lemma_congruencesymmetric).
assert (~ ~ (CR E C B H \/ CR E B H C)).
 {
 intro.
 assert (CR E C B H) by (conclude lemma_crisscross).
 contradict.
 }
assert (EF A B C D E F G H).
by cases on (CR E C B H \/ CR E B H C).
{
 let Tf:=fresh in
 assert (Tf:exists M, (BetS E M C /\ BetS B M H)) by (conclude_def CR );destruct Tf as [M];spliter.
 assert (BetS H M B) by (conclude axiom_betweennesssymmetry).
 assert ((Par E B H C /\ Cong E B H C)) by (conclude proposition_33).
 assert (Par E B C H) by (forward_using lemma_parallelflip).
 assert (PG E B C H) by (conclude_def PG ).
 assert (EF A B C D E B C H) by (conclude proposition_35).
 assert (Col C F G) by (conclude lemma_collinear4).
 assert (Col G F C) by (forward_using lemma_collinearorder).
 assert (Col C B F) by (forward_using lemma_collinearorder).
 assert (Col C B G) by (forward_using lemma_collinearorder).
 assert (neq C B) by (conclude lemma_inequalitysymmetric).
 assert (Col B F G) by (conclude lemma_collinear4).
 assert (Col G F B) by (forward_using lemma_collinearorder).
 assert (Par F G E H) by (conclude lemma_parallelsymmetric).
 assert (Par G F H E) by (forward_using lemma_parallelflip).
 assert (Par E F G H) by (conclude_def PG ).
 assert (Par G H E F) by (conclude lemma_parallelsymmetric).
 assert (PG G H E F) by (conclude_def PG ).
 assert (Par C H E B) by (conclude lemma_parallelsymmetric).
 assert (Par B C E H) by (conclude lemma_parallelsymmetric).
 assert (Par C B H E) by (forward_using lemma_parallelflip).
 assert (PG C H E B) by (conclude_def PG ).
 assert (EF G H E F C H E B) by (conclude proposition_35).
 assert (EF G H E F E B C H) by (forward_using axiom_EFpermutation).
 assert (EF E B C H G H E F) by (conclude axiom_EFsymmetric).
 assert (EF A B C D G H E F) by (conclude axiom_EFtransitive).
 assert (EF A B C D E F G H) by (forward_using axiom_EFpermutation).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists M, (BetS E M B /\ BetS H M C)) by (conclude_def CR );destruct Tf as [M];spliter.
 assert (Par H E B C) by (forward_using lemma_parallelflip).
 assert (Cong H E B C) by (forward_using lemma_congruenceflip).
 assert ((Par H B E C /\ Cong H B E C)) by (conclude proposition_33).
 assert (Par H B C E) by (forward_using lemma_parallelflip).
 assert (PG H B C E) by (conclude_def PG ).
 assert (EF A B C D H B C E) by (conclude proposition_35).
 assert (Col C G F) by (conclude lemma_collinear4).
 assert (Col F G C) by (forward_using lemma_collinearorder).
 assert (Col C B G) by (forward_using lemma_collinearorder).
 assert (Col C B F) by (forward_using lemma_collinearorder).
 assert (neq C B) by (conclude lemma_inequalitysymmetric).
 assert (Col B G F) by (conclude lemma_collinear4).
 assert (Col F G B) by (forward_using lemma_collinearorder).
 assert (Par H E F G) by (forward_using lemma_parallelflip).
 assert (Par F G H E) by (conclude lemma_parallelsymmetric).
 assert (Par F G E H) by (forward_using lemma_parallelflip).
 assert (Par F E H G) by (forward_using lemma_parallelflip).
 assert (PG F E H G) by (conclude_def PG ).
 assert (Par C E H B) by (conclude lemma_parallelsymmetric).
 assert (Par C B E H) by (forward_using lemma_parallelflip).
 assert (PG C E H B) by (conclude_def PG ).
 assert (EF F E H G C E H B) by (conclude proposition_35).
 assert (EF F E H G H B C E) by (forward_using axiom_EFpermutation).
 assert (EF H B C E F E H G) by (conclude axiom_EFsymmetric).
 assert (EF A B C D F E H G) by (conclude axiom_EFtransitive).
 assert (EF A B C D E F G H) by (forward_using axiom_EFpermutation).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


