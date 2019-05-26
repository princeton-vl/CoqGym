Require Export GeoCoq.Elements.OriginalProofs.lemma_squareparallelogram.

Section Euclid.

Context `{Ax1:euclidean_euclidean}.

Lemma lemma_squareunique : 
   forall A B C D E, 
   SQ A B C D -> SQ A B C E ->
   eq E D.
Proof.
intros.
assert (PG A B C D) by (conclude lemma_squareparallelogram).
let Tf:=fresh in
assert (Tf:exists M, (Midpoint A M C /\ Midpoint B M D)) by (conclude lemma_diagonalsbisect);destruct Tf as [M];spliter.
assert (BetS B M D) by (conclude_def Midpoint ).
assert (BetS A M C) by (conclude_def Midpoint ).
assert (Per D A B) by (conclude_def SQ ).
assert (Per E A B) by (conclude_def SQ ).
assert (nCol D A B) by (conclude lemma_rightangleNC).
assert (nCol E A B) by (conclude lemma_rightangleNC).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong A B D A) by (conclude_def SQ ).
assert (Cong A B E A) by (conclude_def SQ ).
assert (Cong E A A B) by (conclude lemma_congruencesymmetric).
assert (Cong E A D A) by (conclude lemma_congruencetransitive).
assert (Cong A E A D) by (forward_using lemma_congruenceflip).
assert (CongA E A B D A B) by (conclude lemma_Euclid4).
assert ((Cong E B D B /\ CongA A E B A D B /\ CongA A B E A B D)) by (conclude proposition_04).
assert (CongA A B D A B E) by (conclude lemma_equalanglessymmetric).
assert (neq B E) by (forward_using lemma_NCdistinct).
assert (neq B M) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists N, (Out B E N /\ Cong B N B M)) by (conclude lemma_layoff);destruct Tf as [N];spliter.
assert (Cong B M B N) by (conclude lemma_congruencesymmetric).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B M D) by (conclude lemma_ray4).
assert (Out B D M) by (conclude lemma_ray5).
assert (nCol A B D) by (forward_using lemma_NCorder).
assert (CongA A B D A B D) by (conclude lemma_equalanglesreflexive).
assert (CongA A B D A B M) by (conclude lemma_equalangleshelper).
assert (CongA A B M A B D) by (conclude lemma_equalanglessymmetric).
assert (CongA A B M A B E) by (conclude lemma_equalanglestransitive).
assert (nCol A B E) by (forward_using lemma_NCorder).
assert (CongA A B E A B E) by (conclude lemma_equalanglesreflexive).
assert (CongA A B E A B N) by (conclude lemma_equalangleshelper).
assert (CongA A B M A B N) by (conclude lemma_equalanglestransitive).
assert (Cong B A B A) by (conclude cn_congruencereflexive).
assert (Cong A M A N) by (conclude proposition_04).
assert (Per B C D) by (conclude_def SQ ).
assert (Per B C E) by (conclude_def SQ ).
assert (CongA B C E B C D) by (conclude lemma_Euclid4).
assert (Cong A B C D) by (conclude_def SQ ).
assert (Cong A B C E) by (conclude_def SQ ).
assert (Cong C E A B) by (conclude lemma_congruencesymmetric).
assert (Cong C E C D) by (conclude lemma_congruencetransitive).
assert (nCol B C E) by (conclude lemma_rightangleNC).
assert (nCol B C D) by (conclude lemma_rightangleNC).
assert (Cong C B C B) by (conclude cn_congruencereflexive).
assert ((Cong B E B D /\ CongA C B E C B D /\ CongA C E B C D B)) by (conclude proposition_04).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out B C C) by (conclude lemma_ray4).
assert (nCol B C D) by (conclude lemma_rightangleNC).
assert (nCol C B D) by (forward_using lemma_NCorder).
assert (CongA C B D C B D) by (conclude lemma_equalanglesreflexive).
assert (CongA C B D C B M) by (conclude lemma_equalangleshelper).
assert (nCol C B E) by (forward_using lemma_NCorder).
assert (CongA C B E C B E) by (conclude lemma_equalanglesreflexive).
assert (CongA C B E C B N) by (conclude lemma_equalangleshelper).
assert (CongA C B E C B D) by (conclude lemma_equalanglestransitive).
assert (CongA C B D C B E) by (conclude lemma_equalanglessymmetric).
assert (CongA C B M C B D) by (conclude lemma_equalanglessymmetric).
assert (CongA C B M C B E) by (conclude lemma_equalanglestransitive).
assert (CongA C B M C B N) by (conclude lemma_equalanglestransitive).
assert (CongA M B C N B C) by (conclude lemma_equalanglesflip).
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (Cong M C N C) by (conclude (proposition_04 B M C B N C)).
assert (Cong A C A C) by (conclude cn_congruencereflexive).
assert (BetS A N C) by (conclude lemma_betweennesspreserved).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (Out A M C) by (conclude lemma_ray4).
assert (neq A N) by (forward_using lemma_betweennotequal).
assert (Out A N C) by (conclude lemma_ray4).
assert (Out A C N) by (conclude lemma_ray5).
assert (Out A C M) by (conclude lemma_ray5).
assert (eq M N) by (conclude lemma_layoffunique).
assert (Out B N E) by (conclude lemma_ray5).
assert (Out B M D) by (conclude lemma_ray5).
assert (Out B M E) by (conclude cn_equalitysub).
assert (eq E D) by (conclude lemma_layoffunique).
close.
Qed.

End Euclid.


