Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.proposition_33B.
Require Export GeoCoq.Elements.OriginalProofs.proposition_30.
Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsbisect.
Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelbetween.
Require Export GeoCoq.Elements.OriginalProofs.proposition_43.
Require Export GeoCoq.Elements.OriginalProofs.proposition_43B.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_44A : 
   forall A B D E F G J N, 
   PG B E F G -> CongA E B G J D N -> BetS A B E ->
   exists X Y, PG A B X Y /\ CongA A B X J D N /\ EF B E F G Y X B A /\ BetS G B X.
Proof.
intros.
assert (PG E F G B) by (conclude lemma_PGrotate).
assert (PG F G B E) by (conclude lemma_PGrotate).
assert (PG G B E F) by (conclude lemma_PGrotate).
assert (Par G F B E) by (conclude_def PG ).
assert (nCol G B E) by (forward_using lemma_parallelNC).
assert (neq G B) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists q, (BetS G B q /\ Cong B q G B)) by (conclude lemma_extension);destruct Tf as [q];spliter.
assert (nCol E B G) by (forward_using lemma_NCorder).
assert (Col A B E) by (conclude_def Col ).
assert (Col E B A) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col E B B) by (conclude_def Col ).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (nCol A B G) by (conclude lemma_NChelper).
assert (Col G B q) by (conclude_def Col ).
assert (nCol G B A) by (forward_using lemma_NCorder).
assert (neq G q) by (forward_using lemma_betweennotequal).
assert (neq q G) by (conclude lemma_inequalitysymmetric).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G B G) by (conclude_def Col ).
assert (nCol q G A) by (conclude lemma_NChelper).
assert (nCol G q A) by (forward_using lemma_NCorder).
rename_H H;let Tf:=fresh in
assert (Tf:exists H h T, (BetS H A h /\ CongA h A B A B G /\ CongA h A B G B A /\ CongA B A h G B A /\ CongA H A B A B q /\ CongA H A B q B A /\ CongA B A H q B A /\ Par H h G q /\ Cong H A B q /\ Cong A h G B /\ Cong A T T B /\ Cong H T T q /\ Cong G T T h /\ BetS H T q /\ BetS G T h /\ BetS A T B)) by (conclude proposition_31);destruct Tf as [H[h[T]]];spliter.
assert (Par H h q G) by (forward_using lemma_parallelflip).
assert (Col G B q) by (conclude_def Col ).
assert (Col q G B) by (forward_using lemma_collinearorder).
assert (neq B G) by (forward_using lemma_NCdistinct).
assert (Par H h B G) by (conclude lemma_collinearparallel).
assert (Par H h G B) by (forward_using lemma_parallelflip).
assert (Par G B H h) by (conclude lemma_parallelsymmetric).
assert (Par G B h H) by (forward_using lemma_parallelflip).
assert (Col H A h) by (conclude_def Col ).
assert (Col h H A) by (forward_using lemma_collinearorder).
assert (neq H A) by (forward_using lemma_betweennotequal).
assert (neq A H) by (conclude lemma_inequalitysymmetric).
assert (Par G B A H) by (conclude lemma_collinearparallel).
assert (Par G B H A) by (forward_using lemma_parallelflip).
assert (Par H A G B) by (conclude lemma_parallelsymmetric).
assert (Cong H A G B) by (conclude lemma_congruencetransitive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (Col A T B) by (conclude_def Col ).
assert (Col A B T) by (forward_using lemma_collinearorder).
assert (nCol B H A) by (forward_using lemma_parallelNC).
assert (nCol A B H) by (forward_using lemma_NCorder).
assert (nCol H A B) by (forward_using lemma_parallelNC).
assert (nCol A B H) by (forward_using lemma_NCorder).
assert (OS H G A B) by (conclude_def OS ).
assert ((Par H G A B /\ Cong H G A B)) by (conclude proposition_33B).
assert (Par A B H G) by (conclude lemma_parallelsymmetric).
assert (Par A B G H) by (forward_using lemma_parallelflip).
assert ((Par G B E F /\ Par G F B E)) by (conclude_def PG ).
assert (Par G F E B) by (forward_using lemma_parallelflip).
assert (Col A B E) by (conclude_def Col ).
assert (Col E B A) by (forward_using lemma_collinearorder).
assert (Par G F A B) by (conclude lemma_collinearparallel).
assert (Par A B G F) by (conclude lemma_parallelsymmetric).
assert (Col G H F) by (conclude lemma_Playfair).
assert (Par H A B G) by (forward_using lemma_parallelflip).
assert (Par G B F E) by (forward_using lemma_parallelflip).
assert (Par F E G B) by (conclude lemma_parallelsymmetric).
assert (PG H A B G) by (conclude_def PG ).
let Tf:=fresh in
assert (Tf:exists j, (BetS H j B /\ BetS A j G)) by (conclude lemma_diagonalsmeet);destruct Tf as [j];spliter.
let Tf:=fresh in
assert (Tf:exists k, (BetS G k E /\ BetS B k F)) by (conclude lemma_diagonalsmeet);destruct Tf as [k];spliter.
assert (BetS E B A) by (conclude axiom_betweennesssymmetry).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col F E E) by (conclude_def Col ).
assert (Col G B B) by (conclude_def Col ).
assert (Col H A A) by (conclude_def Col ).
assert (nCol F E B) by (forward_using lemma_parallelNC).
assert (neq F E) by (forward_using lemma_NCdistinct).
assert (neq G B) by (forward_using lemma_NCdistinct).
assert (nCol H A G) by (forward_using lemma_parallelNC).
assert (neq H A) by (forward_using lemma_NCdistinct).
assert (Par H A F E) by (eauto using (proposition_30 _ _ _ _ _ _ _ _ _ _ H79 H1 H93)).
assert (Cong G B F E) by (forward_using proposition_34).
assert (Cong H A F E) by (conclude lemma_congruencetransitive).
assert (Par G F B E) by (conclude_def PG ).
assert (Par H G A B) by (conclude_def PG ).
assert (Par B E G F) by (conclude lemma_parallelsymmetric).
assert (Par A B H G) by (conclude lemma_parallelsymmetric).
assert (TP B E G F) by (conclude lemma_paralleldef2B).
assert (TP A B H G) by (conclude lemma_paralleldef2B).
assert (OS G F B E) by (conclude_def TP ).
assert (OS H G A B) by (conclude_def TP ).
assert (Col A B E) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (OS H G A E) by (conclude lemma_samesidecollinear).
assert (OS G F E B) by (conclude lemma_samesideflip).
assert (Col E B A) by (forward_using lemma_collinearorder).
assert (neq E A) by (conclude lemma_inequalitysymmetric).
assert (OS G F E A) by (conclude lemma_samesidecollinear).
assert (OS G F A E) by (conclude lemma_samesideflip).
assert (OS H F A E) by (conclude lemma_samesidetransitive).
assert (Par H F A E) by (conclude proposition_33B).
assert (Par H A E F) by (forward_using lemma_parallelflip).
assert (PG H A E F) by (conclude_def PG ).
assert (nCol H F E) by (forward_using lemma_parallelNC).
assert (nCol E F H) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists t, (Midpoint H t E /\ Midpoint A t F)) by (conclude lemma_diagonalsbisect);destruct Tf as [t];spliter.
assert ((BetS H t E /\ Cong H t t E)) by (conclude_def Midpoint ).
assert ((BetS A t F /\ Cong A t t F)) by (conclude_def Midpoint ).
assert (Cong A t F t) by (forward_using lemma_congruenceflip).
assert (Cong H t E t) by (forward_using lemma_congruenceflip).
assert (Cong t A t F) by (forward_using lemma_congruenceflip).
assert (nCol H E F) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists K, (BetS H B K /\ BetS F E K)) by (conclude postulate_Euclid5);destruct Tf as [K];spliter.
assert (Col F E K) by (conclude_def Col ).
assert (Col E F K) by (forward_using lemma_collinearorder).
assert (neq F K) by (forward_using lemma_betweennotequal).
assert (neq K F) by (conclude lemma_inequalitysymmetric).
assert (Par H A K F) by (conclude lemma_collinearparallel).
assert (Par H A F K) by (forward_using lemma_parallelflip).
assert (Par F K H A) by (conclude lemma_parallelsymmetric).
assert (Par F K A H) by (forward_using lemma_parallelflip).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col A H H) by (conclude_def Col ).
let Tf:=fresh in
assert (Tf:exists L, (PG H L K F /\ Col A H L)) by (conclude lemma_triangletoparallelogram);destruct Tf as [L];spliter.
assert (Par H L K F) by (conclude_def PG ).
assert (nCol L K F) by (forward_using lemma_parallelNC).
assert (neq L K) by (forward_using lemma_NCdistinct).
assert (neq K L) by (conclude lemma_inequalitysymmetric).
assert (Par G B E F) by (conclude_def PG ).
assert (Par G B F E) by (forward_using lemma_parallelflip).
assert (Col F E E) by (conclude_def Col ).
assert (Col F E K) by (conclude_def Col ).
assert (neq E K) by (forward_using lemma_betweennotequal).
assert (Par G B E K) by (conclude lemma_collinearparallel2).
assert (Par E K G B) by (conclude lemma_parallelsymmetric).
assert (Col G B B) by (conclude_def Col ).
let Tf:=fresh in
assert (Tf:exists M, (PG B M K E /\ Col G B M)) by (conclude lemma_triangletoparallelogram);destruct Tf as [M];spliter.
assert (PG L K F H) by (conclude lemma_PGrotate).
assert (PG K L H F) by (conclude lemma_PGflip).
assert (PG L H F K) by (conclude lemma_PGrotate).
assert (PG H F K L) by (conclude lemma_PGrotate).
assert (PG A H G B) by (conclude lemma_PGflip).
assert (Par A H G B) by (conclude_def PG ).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (Par B E M K) by (conclude_def PG ).
assert (Par M K B E) by (conclude lemma_parallelsymmetric).
assert (Par K M E B) by (forward_using lemma_parallelflip).
assert (Par G F B E) by (conclude_def PG ).
assert (nCol E M K) by (forward_using lemma_parallelNC).
assert (nCol B E K) by (forward_using lemma_parallelNC).
assert (nCol G F B) by (forward_using lemma_parallelNC).
assert (Par M K B E) by (forward_using lemma_parallelflip).
assert (Par G F B E) by (forward_using lemma_parallelflip).
assert (BetS K E F) by (conclude axiom_betweennesssymmetry).
assert (Col M K K) by (conclude_def Col ).
assert (Col B E E) by (conclude_def Col ).
assert (Col G F F) by (conclude_def Col ).
assert (neq M K) by (forward_using lemma_NCdistinct).
assert (neq B E) by (forward_using lemma_NCdistinct).
assert (neq G F) by (forward_using lemma_NCdistinct).
assert (Par M K G F) by (conclude proposition_30).
assert (Par K M F G) by (forward_using lemma_parallelflip).
assert (Par F G K M) by (conclude lemma_parallelsymmetric).
assert (Par H F L K) by (conclude_def PG ).
assert (Par L K H F) by (conclude lemma_parallelsymmetric).
assert (Par K L H F) by (forward_using lemma_parallelflip).
assert (Col H F G) by (forward_using lemma_collinearorder).
assert (Par K L G F) by (conclude lemma_collinearparallel).
assert (Par K L F G) by (forward_using lemma_parallelflip).
assert (Par F G K L) by (conclude lemma_parallelsymmetric).
assert (Col K M L) by (conclude lemma_Playfair).
assert (Col M K L) by (forward_using lemma_collinearorder).
assert (Par B E M K) by (conclude_def PG ).
assert (neq L K) by (conclude lemma_inequalitysymmetric).
assert (Par B E L K) by (conclude lemma_collinearparallel).
assert (Par L K B E) by (conclude lemma_parallelsymmetric).
assert (Par L K E B) by (forward_using lemma_parallelflip).
assert (Col A B E) by (conclude_def Col ).
assert (Col E B A) by (forward_using lemma_collinearorder).
assert (Par L K A B) by (conclude lemma_collinearparallel).
assert (Par A B L K) by (conclude lemma_parallelsymmetric).
assert (Par A B K L) by (forward_using lemma_parallelflip).
assert (BetS K B H) by (conclude axiom_betweennesssymmetry).
assert (Col L A H) by (forward_using lemma_collinearorder).
assert (BetS L A H) by (conclude lemma_parallelbetween).
assert (BetS H A L) by (conclude axiom_betweennesssymmetry).
assert (Par H A G B) by (forward_using lemma_parallelflip).
assert (nCol B M K) by (forward_using lemma_parallelNC).
assert (neq M B) by (forward_using lemma_NCdistinct).
assert (Par H A M B) by (conclude lemma_collinearparallel).
assert (Par M B H A) by (conclude lemma_parallelsymmetric).
assert (Par M B A H) by (forward_using lemma_parallelflip).
assert (Col A H L) by (forward_using lemma_collinearorder).
assert (Par H L K F) by (conclude_def PG ).
assert (nCol H L K) by (forward_using lemma_parallelNC).
assert (neq L H) by (forward_using lemma_NCdistinct).
assert (Par M B L H) by (conclude lemma_collinearparallel).
assert (Par M B H L) by (forward_using lemma_parallelflip).
assert (Col L M K) by (forward_using lemma_collinearorder).
assert (BetS L M K) by (conclude lemma_parallelbetween).
assert (Par G B E F) by (conclude_def PG ).
assert (Col F E K) by (conclude_def Col ).
assert (Col E F K) by (forward_using lemma_collinearorder).
assert (neq F K) by (forward_using lemma_betweennotequal).
assert (neq K F) by (conclude lemma_inequalitysymmetric).
assert (Par G B K F) by (conclude lemma_collinearparallel).
assert (Col F G H) by (forward_using lemma_collinearorder).
assert (BetS F G H) by (conclude lemma_parallelbetween).
assert (BetS H G F) by (conclude axiom_betweennesssymmetry).
assert (PG A B G H) by (conclude lemma_PGrotate).
assert (PG B G H A) by (conclude lemma_PGrotate).
assert (PG G H A B) by (conclude lemma_PGrotate).
assert (PG M K E B) by (conclude lemma_PGrotate).
assert (PG K E B M) by (conclude lemma_PGrotate).
assert (PG E B M K) by (conclude lemma_PGrotate).
assert (EF B E F G L M B A) by (conclude proposition_43).
assert (PG A H G B) by (conclude lemma_PGflip).
assert (PG M B E K) by (conclude lemma_PGflip).
assert (PG A B M L) by (conclude proposition_43B).
assert (Col H G F) by (forward_using lemma_collinearorder).
assert (neq H F) by (forward_using lemma_betweennotequal).
assert (neq L K) by (forward_using lemma_betweennotequal).
assert (neq H G) by (forward_using lemma_betweennotequal).
assert (neq M K) by (forward_using lemma_betweennotequal).
assert (Par H F L K) by (conclude_def PG ).
assert (~ Meet H F L K)
 by (unfold Par in H251;decompose [ex and] H251;auto).
assert (Col G M B) by (forward_using lemma_collinearorder).
assert (BetS G B M) by (conclude lemma_collinearbetween).
assert (CongA A B M G B E) by (conclude proposition_15).
assert (CongA G B E E B G) by (conclude lemma_ABCequalsCBA).
assert (CongA A B M E B G) by (conclude lemma_equalanglestransitive).
assert (CongA A B M J D N) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


