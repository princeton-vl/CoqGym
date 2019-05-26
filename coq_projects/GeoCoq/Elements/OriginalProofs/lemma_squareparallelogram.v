Require Export GeoCoq.Elements.OriginalProofs.proposition_46.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesideflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_righttogether.
Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsbisect.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_squareparallelogram : 
   forall A B C D, 
   SQ A B C D ->
   PG A B C D.
Proof.
intros.
assert ((Cong A B C D /\ Cong A B B C /\ Cong A B D A /\ Per D A B /\ Per A B C /\ Per B C D /\ Per C D A)) by (conclude_def SQ ).
assert (nCol D A B) by (conclude lemma_rightangleNC).
assert (neq D A) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists R, (BetS D A R /\ Cong A R D A)) by (conclude lemma_extension);destruct Tf as [R];spliter.
assert (BetS R A D) by (conclude axiom_betweennesssymmetry).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (Col D A R) by (conclude_def Col ).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col D A A) by (conclude_def Col ).
assert (neq R A) by (forward_using lemma_betweennotequal).
assert (nCol R A B) by (conclude lemma_NChelper).
assert (nCol A B R) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists c E, (SQ A B c E /\ TS E A B R /\ PG A B c E)) by (conclude proposition_46);destruct Tf as [c[E]];spliter.
assert ((Cong A B c E /\ Cong A B B c /\ Cong A B E A /\ Per E A B /\ Per A B c /\ Per B c E /\ Per c E A)) by (conclude_def SQ ).
assert (Col R A D) by (conclude_def Col ).
assert (Col D A R) by (forward_using lemma_collinearorder).
assert (Per R A B) by (conclude lemma_collinearright).
assert (Per B A R) by (conclude lemma_8_2).
assert (TS E B A R) by (conclude lemma_oppositesideflip).
assert (BetS E A R) by (conclude lemma_righttogether).
assert (BetS R A E) by (conclude axiom_betweennesssymmetry).
assert (Out A D E) by (conclude_def Out ).
assert (Cong A B E A) by (conclude_def SQ ).
assert (Cong E A A B) by (conclude lemma_congruencesymmetric).
assert (Cong E A D A) by (conclude lemma_congruencetransitive).
assert (Cong A E A D) by (forward_using lemma_congruenceflip).
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Out A D D) by (conclude lemma_ray4).
assert (eq E D) by (conclude lemma_layoffunique).
assert (PG A B c D) by (conclude cn_equalitysub).
assert (Cong A B C D) by (conclude_def SQ ).
assert (SQ A B c D) by (conclude cn_equalitysub).
assert (Cong A B c D) by (conclude_def SQ ).
assert (Cong c D A B) by (conclude lemma_congruencesymmetric).
assert (Cong c D C D) by (conclude lemma_congruencetransitive).
assert (Cong A B B C) by (conclude_def SQ ).
assert (Cong A B B c) by (conclude_def SQ ).
assert (Cong B c A B) by (conclude lemma_congruencesymmetric).
assert (Cong B c B C) by (conclude lemma_congruencetransitive).
assert (Cong c B C B) by (forward_using lemma_congruenceflip).
assert (Per B C D) by (conclude_def SQ ).
assert (Per B c D) by (conclude_def SQ ).
assert (CongA B c D B C D) by (conclude lemma_Euclid4).
assert ((Cong B D B D /\ CongA c B D C B D /\ CongA c D B C D B)) by (conclude proposition_04).
let Tf:=fresh in
assert (Tf:exists m, (Midpoint A m c /\ Midpoint B m D)) by (conclude lemma_diagonalsbisect);destruct Tf as [m];spliter.
assert ((BetS A m c /\ Cong A m m c)) by (conclude_def Midpoint ).
assert ((BetS B m D /\ Cong B m m D)) by (conclude_def Midpoint ).
assert (CongA C D B c D B) by (conclude lemma_equalanglessymmetric).
assert (Cong D m D m) by (conclude cn_congruencereflexive).
assert (Cong D c D C) by (forward_using lemma_congruenceflip).
assert (nCol C D A) by (conclude lemma_rightangleNC).
assert (Per c D A) by (conclude cn_equalitysub).
assert (nCol c D A) by (conclude lemma_rightangleNC).
assert (nCol A c D) by (forward_using lemma_NCorder).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (Col A c c) by (conclude_def Col ).
assert (Col A m c) by (conclude_def Col ).
assert (Col A c m) by (forward_using lemma_collinearorder).
assert (neq m c) by (forward_using lemma_betweennotequal).
assert (nCol m c D) by (conclude lemma_NChelper).
assert (nCol c D m) by (forward_using lemma_NCorder).
assert (~ Col C D m).
 {
 intro.
 assert (Col B m D) by (conclude_def Col ).
 assert (Col m D B) by (forward_using lemma_collinearorder).
 assert (Col m D C) by (forward_using lemma_collinearorder).
 assert (neq m D) by (forward_using lemma_betweennotequal).
 assert (Col D B C) by (conclude lemma_collinear4).
 assert (Col B C D) by (forward_using lemma_collinearorder).
 assert (nCol B C D) by (conclude lemma_rightangleNC).
 contradict.
 }
assert (CongA c D B C D B) by (conclude lemma_equalanglessymmetric).
assert (BetS D m B) by (conclude axiom_betweennesssymmetry).
assert (neq D B) by (forward_using lemma_betweennotequal).
assert (Out D B m) by (conclude lemma_ray4).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (neq D C) by (forward_using lemma_NCdistinct).
assert (Out D C C) by (conclude lemma_ray4).
assert (CongA c D B C D m) by (conclude lemma_equalangleshelper).
assert (CongA C D m c D B) by (conclude lemma_equalanglessymmetric).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (neq D c) by (forward_using lemma_NCdistinct).
assert (Out D c c) by (conclude lemma_ray4).
assert (CongA C D m c D m) by (conclude lemma_equalangleshelper).
assert (CongA c D m C D m) by (conclude lemma_equalanglessymmetric).
assert (Cong c m C m) by (conclude proposition_04).
assert (Cong m c m C) by (forward_using lemma_congruenceflip).
assert (Cong A m A m) by (conclude cn_congruencereflexive).
assert (Cong D A D A) by (conclude cn_congruencereflexive).
assert (Per c D A) by (conclude cn_equalitysub).
assert (Per A D c) by (conclude lemma_8_2).
assert (Per A D C) by (conclude lemma_8_2).
assert (CongA A D C A D c) by (conclude lemma_Euclid4).
assert (Cong D C D c) by (conclude lemma_congruencesymmetric).
assert (Cong A C A c) by (conclude proposition_04).
assert (Cong A c A C) by (conclude lemma_congruencesymmetric).
assert (BetS A m C) by (conclude lemma_betweennesspreserved).
assert (neq A m) by (forward_using lemma_betweennotequal).
assert (Out A m c) by (conclude lemma_ray4).
assert (Out A m C) by (conclude lemma_ray4).
assert (eq c C) by (conclude lemma_layoffunique).
assert (PG A B C D) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


