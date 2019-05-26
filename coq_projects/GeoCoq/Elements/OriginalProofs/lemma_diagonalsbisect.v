Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossimpliesopposite.
Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_diagonalsbisect : 
   forall A B C D, 
   PG A B C D ->
   exists X, Midpoint A X C /\ Midpoint B X D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert (neq A C) by (forward_using lemma_betweennotequal).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (CR A C B D) by (conclude_def CR ).
assert (Par A B C D) by (conclude_def PG ).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (nCol A B D) by (forward_using lemma_parallelNC).
assert (TS A B D C) by (forward_using lemma_crossimpliesopposite).
assert (Par B A D C) by (forward_using lemma_parallelflip).
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (BetS D M B) by (conclude axiom_betweennesssymmetry).
assert (CR B D A C) by (conclude_def CR ).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (nCol B A C) by (forward_using lemma_NCorder).
assert (TS B A C D) by (forward_using lemma_crossimpliesopposite).
assert (Cong A B D C) by (forward_using proposition_34).
assert (Cong A B C D) by (forward_using lemma_congruenceflip).
assert (~ Col M A B).
 {
 intro.
 assert (Col A M C) by (conclude_def Col ).
 assert (Col M A C) by (forward_using lemma_collinearorder).
 assert (neq A M) by (forward_using lemma_betweennotequal).
 assert (neq M A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 assert (nCol A B C) by (forward_using lemma_parallelNC).
 contradict.
 }
assert (Triangle M A B) by (conclude_def Triangle ).
assert (~ Col M C D).
 {
 intro.
 assert (Col A M C) by (conclude_def Col ).
 assert (Col M C A) by (forward_using lemma_collinearorder).
 assert (neq M C) by (forward_using lemma_betweennotequal).
 assert (Col C D A) by (conclude lemma_collinear4).
 assert (Col A C D) by (forward_using lemma_collinearorder).
 assert (nCol A C D) by (forward_using lemma_parallelNC).
 contradict.
 }
assert (Triangle M C D) by (conclude_def Triangle ).
assert (Par B A C D) by (forward_using lemma_parallelflip).
assert (CongA B A C A C D) by (conclude proposition_29B).
assert (CongA B A C B A C) by (conclude lemma_equalanglesreflexive).
assert (Out A C M) by (conclude lemma_ray4).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (Out A B B) by (conclude lemma_ray4).
assert (CongA B A C B A M) by (conclude lemma_equalangleshelper).
assert (CongA B A M B A C) by (conclude lemma_equalanglessymmetric).
assert (CongA B A M A C D) by (conclude lemma_equalanglestransitive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (neq C A) by (forward_using lemma_NCdistinct).
assert (Out C D D) by (conclude lemma_ray4).
assert (Out C A M) by (conclude lemma_ray4).
assert (CongA A C D A C D) by (conclude lemma_equalanglesreflexive).
assert (CongA A C D M C D) by (conclude lemma_equalangleshelper).
assert (CongA B A M M C D) by (conclude lemma_equalanglestransitive).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (Col A M C) by (conclude_def Col ).
assert (Col A C M) by (forward_using lemma_collinearorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col A C C) by (conclude_def Col ).
assert (neq M C) by (forward_using lemma_betweennotequal).
assert (nCol M C D) by (conclude lemma_NChelper).
assert (CongA M C D D C M) by (conclude lemma_ABCequalsCBA).
assert (CongA B A M D C M) by (conclude lemma_equalanglestransitive).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (CongA A B D B D C) by (conclude proposition_29B).
assert (CongA A B D A B D) by (conclude lemma_equalanglesreflexive).
assert (Out B D M) by (conclude lemma_ray4).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (nCol B A D) by (forward_using lemma_parallelNC).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Out B A A) by (conclude lemma_ray4).
assert (CongA A B D A B M) by (conclude lemma_equalangleshelper).
assert (CongA A B M A B D) by (conclude lemma_equalanglessymmetric).
assert (CongA A B M B D C) by (conclude lemma_equalanglestransitive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (nCol B D C) by (forward_using lemma_parallelNC).
assert (neq D C) by (forward_using lemma_NCdistinct).
assert (neq D B) by (forward_using lemma_NCdistinct).
assert (Out D C C) by (conclude lemma_ray4).
assert (Out D B M) by (conclude lemma_ray4).
assert (CongA B D C B D C) by (conclude lemma_equalanglesreflexive).
assert (CongA B D C M D C) by (conclude lemma_equalangleshelper).
assert (CongA A B M M D C) by (conclude lemma_equalanglestransitive).
assert (nCol B D C) by (forward_using lemma_parallelNC).
assert (Col B M D) by (conclude_def Col ).
assert (Col B D M) by (forward_using lemma_collinearorder).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col B D D) by (conclude_def Col ).
assert (neq M D) by (forward_using lemma_betweennotequal).
assert (nCol M D C) by (conclude lemma_NChelper).
assert (CongA M D C C D M) by (conclude lemma_ABCequalsCBA).
assert (CongA A B M C D M) by (conclude lemma_equalanglestransitive).
assert (CongA M A B M C D) by (conclude lemma_equalanglesflip).
assert ((Cong M A M C /\ Cong M B M D /\ CongA A M B C M D)) by (conclude proposition_26A).
assert (Cong A M M C) by (forward_using lemma_congruenceflip).
assert (Cong B M M D) by (forward_using lemma_congruenceflip).
assert (Midpoint A M C) by (conclude_def Midpoint ).
assert (Midpoint B M D) by (conclude_def Midpoint ).
close.
Qed.

End Euclid.


