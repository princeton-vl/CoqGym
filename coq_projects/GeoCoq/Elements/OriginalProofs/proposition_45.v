Require Export GeoCoq.Elements.OriginalProofs.proposition_44.
Require Export GeoCoq.Elements.OriginalProofs.lemma_RTcongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_RTsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_14.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_45 : 
   forall A B C D E J K N O R S, 
   nCol J E N -> nCol A B D -> nCol C B D -> BetS A O C -> BetS B O D -> neq R K -> nCol K R S ->
   exists X Z U, PG X K Z U /\ CongA X K Z J E N /\ EF X K Z U A B C D /\ Out K R Z /\ OS X S K Z.
Proof.
intros.
assert (neq B D) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists m, (BetS B m D /\ Cong m B m D)) by (conclude proposition_10);destruct Tf as [m];spliter.
assert (Cong B m m D) by (forward_using lemma_congruenceflip).
assert (Midpoint B m D) by (conclude_def Midpoint ).
assert (neq B m) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists P, (BetS R K P /\ Cong K P B m)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (Triangle A B D) by (conclude_def Triangle ).
assert (neq K P) by (forward_using lemma_betweennotequal).
assert (neq P K) by (conclude lemma_inequalitysymmetric).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS P K H /\ Cong K H P K)) by (conclude lemma_extension);destruct Tf as [H];spliter.
assert (Cong P K K H) by (conclude lemma_congruencesymmetric).
assert (Midpoint P K H) by (conclude_def Midpoint ).
assert (Cong P K B m) by (forward_using lemma_congruenceflip).
assert (Cong K H B m) by (conclude lemma_congruencetransitive).
assert (Cong B m m D) by (forward_using lemma_congruenceflip).
assert (Cong K H m D) by (conclude lemma_congruencetransitive).
assert (BetS P K R) by (conclude axiom_betweennesssymmetry).
assert (Col P K H) by (conclude_def Col ).
assert (Col P K R) by (conclude_def Col ).
assert (neq P K) by (forward_using lemma_betweennotequal).
assert (Col K H R) by (conclude lemma_collinear4).
assert (Col R K H) by (forward_using lemma_collinearorder).
assert (nCol R K S) by (forward_using lemma_NCorder).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (Col R K K) by (conclude_def Col ).
assert (neq K H) by (forward_using lemma_betweennotequal).
assert (neq H K) by (conclude lemma_inequalitysymmetric).
assert (nCol H K S) by (conclude lemma_NChelper).
assert (nCol S K H) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists F G, (PG F K H G /\ EF A B m D F K H G /\ CongA H K F J E N /\ OS S F K H)) by (conclude proposition_42B);destruct Tf as [F[G]];spliter.
assert (nCol D B C) by (forward_using lemma_NCorder).
assert (Triangle D B C) by (conclude_def Triangle ).
assert (Par F K H G) by (conclude_def PG ).
assert (nCol K H G) by (forward_using lemma_parallelNC).
assert (nCol H G K) by (forward_using lemma_NCorder).
assert (nCol G H K) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists M L e, (PG G H M L /\ CongA G H M J E N /\ EF D B e C G H M L /\ Midpoint B e C /\ TS M G H K)) by (conclude proposition_44);destruct Tf as [M[L[e]]];spliter.
assert (BetS B e C) by (conclude_def Midpoint ).
assert (CongA J E N G H M) by (conclude lemma_equalanglessymmetric).
assert (CongA H K F G H M) by (conclude lemma_equalanglestransitive).
assert (Par F K H G) by (conclude_def PG ).
assert (Par K F H G) by (forward_using lemma_parallelflip).
assert (neq H K) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists s, (BetS H K s /\ Cong K s H K)) by (conclude lemma_extension);destruct Tf as [s];spliter.
assert (Par F G K H) by (conclude_def PG ).
assert (Par K H F G) by (conclude lemma_parallelsymmetric).
assert (TP K H F G) by (conclude lemma_paralleldef2B).
assert (OS F G K H) by (conclude_def TP ).
assert (RT F K H K H G) by (conclude proposition_29C).
assert (CongA G H M H K F) by (conclude lemma_equalanglessymmetric).
assert (nCol H K F) by (conclude lemma_equalanglesNC).
assert (nCol F K H) by (forward_using lemma_NCorder).
assert (CongA F K H H K F) by (conclude lemma_ABCequalsCBA).
assert (CongA F K H G H M) by (conclude lemma_equalanglestransitive).
assert (RT G H M K H G) by (conclude lemma_RTcongruence).
assert (RT K H G G H M) by (conclude lemma_RTsymmetric).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (neq H G) by (forward_using lemma_NCdistinct).
assert (Out H G G) by (conclude lemma_ray4).
assert (BetS K H M) by (conclude proposition_14).
assert (neq F K) by (forward_using lemma_NCdistinct).
assert (nCol G H M) by (conclude lemma_equalanglesNC).
assert (neq G H) by (forward_using lemma_NCdistinct).
assert (Par G H M L) by (conclude_def PG ).
assert (nCol H M L) by (forward_using lemma_parallelNC).
assert (neq L M) by (forward_using lemma_NCdistinct).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (eq M M) by (conclude cn_equalityreflexive).
assert (Col F K K) by (conclude_def Col ).
assert (Col G H H) by (conclude_def Col ).
assert (Col L M M) by (conclude_def Col ).
assert (Par F K G H) by (forward_using lemma_parallelflip).
assert (Par M L G H) by (conclude lemma_parallelsymmetric).
assert (Par L M G H) by (forward_using lemma_parallelflip).
assert (Par F K L M) by (conclude proposition_30).
assert (Par F K M L) by (forward_using lemma_parallelflip).
assert (Par F G K H) by (conclude_def PG ).
assert (Par G L H M) by (conclude_def PG ).
assert (Par F G H K) by (forward_using lemma_parallelflip).
assert (Col K H M) by (conclude_def Col ).
assert (Col H K M) by (forward_using lemma_collinearorder).
assert (neq K M) by (forward_using lemma_betweennotequal).
assert (neq M K) by (conclude lemma_inequalitysymmetric).
assert (Par F G M K) by (conclude lemma_collinearparallel).
assert (Col H M K) by (forward_using lemma_collinearorder).
assert (Par G L K M) by (conclude lemma_collinearparallel).
assert (Par G L M K) by (forward_using lemma_parallelflip).
assert (Par M K G L) by (conclude lemma_parallelsymmetric).
assert (Par M K F G) by (conclude lemma_parallelsymmetric).
assert (Par M K G F) by (forward_using lemma_parallelflip).
assert (Col G L F) by (conclude lemma_Playfair).
assert (Col G F L) by (forward_using lemma_collinearorder).
assert (nCol F L M) by (forward_using lemma_parallelNC).
assert (neq L F) by (forward_using lemma_NCdistinct).
assert (Par M K L F) by (conclude lemma_collinearparallel).
assert (Par L F M K) by (conclude lemma_parallelsymmetric).
assert (Par F L K M) by (forward_using lemma_parallelflip).
assert (PG F K M L) by (conclude_def PG ).
assert (nCol F K H) by (forward_using lemma_parallelNC).
assert (CongA F K H H K F) by (conclude lemma_ABCequalsCBA).
assert (CongA F K H J E N) by (conclude lemma_equalanglestransitive).
assert (neq K H) by (forward_using lemma_betweennotequal).
assert (Out K H M) by (conclude lemma_ray4).
assert (Out K M H) by (conclude lemma_ray5).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (neq K F) by (forward_using lemma_NCdistinct).
assert (Out K F F) by (conclude lemma_ray4).
assert (nCol F K M) by (forward_using lemma_parallelNC).
assert (CongA F K M F K M) by (conclude lemma_equalanglesreflexive).
assert (CongA F K M F K H) by (conclude lemma_equalangleshelper).
assert (CongA F K M J E N) by (conclude lemma_equalanglestransitive).
assert (Col B O D) by (conclude_def Col ).
assert (Col B D O) by (forward_using lemma_collinearorder).
assert (nCol B D A) by (forward_using lemma_NCorder).
assert (TS A B D C) by (conclude_def TS ).
assert (Par G H L M) by (forward_using lemma_parallelflip).
assert (TP G H L M) by (conclude lemma_paralleldef2B).
assert (OS L M G H) by (conclude_def TP ).
assert (Par F K G H) by (forward_using lemma_parallelflip).
assert (Par G H F K) by (conclude lemma_parallelsymmetric).
assert (TP G H F K) by (conclude lemma_paralleldef2B).
assert (OS F K G H) by (conclude_def TP ).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col G H H) by (conclude_def Col ).
assert (TS K G H M) by (conclude_def TS ).
assert (TS F G H M) by (conclude lemma_planeseparation).
assert (TS M G H F) by (conclude lemma_oppositesidesymmetric).
assert (TS L G H F) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists t, (BetS L t F /\ Col G H t /\ nCol G H L)) by (conclude_def TS );destruct Tf as [t];spliter.
assert (Col F L G) by (forward_using lemma_collinearorder).
assert (Col L t F) by (conclude_def Col ).
assert (Col F L t) by (forward_using lemma_collinearorder).
assert (neq F L) by (forward_using lemma_NCdistinct).
assert (Col L G t) by (conclude lemma_collinear4).
assert (Col t G L) by (forward_using lemma_collinearorder).
assert (Col t G H) by (forward_using lemma_collinearorder).
assert (~ neq t G).
 {
 intro.
 assert (Col G L H) by (conclude lemma_collinear4).
 assert (Col G H L) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (BetS L G F) by (conclude cn_equalitysub).
assert (BetS F G L) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists j, (BetS F j M /\ BetS K j L)) by (conclude lemma_diagonalsmeet);destruct Tf as [j];spliter.
assert (EF A B C D F K M L) by (conclude axiom_paste4).
assert (EF F K M L A B C D) by (conclude axiom_EFsymmetric).
assert (BetS P K M) by (conclude lemma_3_7b).
assert (Out K R M) by (conclude_def Out ).
assert (OS F S K H) by (forward_using lemma_samesidesymmetric).
assert (Col K H M) by (conclude_def Col ).
assert (OS F S K M) by (conclude lemma_samesidecollinear).
close.
Qed.

End Euclid.


