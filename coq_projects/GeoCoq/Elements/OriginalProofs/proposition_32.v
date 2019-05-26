Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.proposition_31short.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_32 : 
   forall A B C D, 
   Triangle A B C -> BetS B C D ->
   SumA C A B A B C A C D.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (neq A B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS B A F /\ Cong A F B A)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (Col B A F) by (conclude_def Col ).
assert (Col A B F) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (neq F B) by (conclude lemma_inequalitysymmetric).
assert (nCol F B C) by (conclude lemma_NChelper).
assert (BetS F A B) by (conclude axiom_betweennesssymmetry).
rename_H H;let Tf:=fresh in
assert (Tf:exists E H S, (BetS E C H /\ CongA E C A C A B /\ Par E H F B /\ BetS E S B /\ BetS C S A)) by (conclude proposition_31short);destruct Tf as [E[H[S]]];spliter.
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists G, (BetS C B G /\ Cong B G C B)) by (conclude lemma_extension);destruct Tf as [G];spliter.
assert (neq C A) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists J, (BetS C A J /\ Cong A J C A)) by (conclude lemma_extension);destruct Tf as [J];spliter.
assert (neq A C) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists K, (BetS A C K /\ Cong C K A C)) by (conclude lemma_extension);destruct Tf as [K];spliter.
let Tf:=fresh in
assert (Tf:exists M, (BetS A B M /\ Cong B M A B)) by (conclude lemma_extension);destruct Tf as [M];spliter.
assert (Col F B A) by (forward_using lemma_collinearorder).
assert (Par E H A B) by (conclude lemma_collinearparallel).
assert (BetS K C A) by (conclude axiom_betweennesssymmetry).
assert (Col C S A) by (conclude_def Col ).
assert (Col C A S) by (forward_using lemma_collinearorder).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (Col A C S) by (forward_using lemma_collinearorder).
assert (neq C S) by (forward_using lemma_betweennotequal).
assert (neq S C) by (conclude lemma_inequalitysymmetric).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col A C C) by (conclude_def Col ).
assert (nCol S C B) by (conclude lemma_NChelper).
assert (nCol B S C) by (forward_using lemma_NCorder).
assert (Col E S B) by (conclude_def Col ).
assert (Col B S E) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B S B) by (conclude_def Col ).
assert (BetS B S E) by (conclude axiom_betweennesssymmetry).
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (nCol B E C) by (conclude lemma_NChelper).
assert (Col B E S) by (forward_using lemma_collinearorder).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col B E E) by (conclude_def Col ).
assert (neq S E) by (forward_using lemma_betweennotequal).
assert (nCol S E C) by (conclude lemma_NChelper).
assert (nCol S C E) by (forward_using lemma_NCorder).
assert (Col S C C) by (conclude_def Col ).
assert (Col C S A) by (conclude_def Col ).
assert (Col S C A) by (forward_using lemma_collinearorder).
assert (neq C A) by (forward_using lemma_betweennotequal).
assert (nCol C A E) by (conclude lemma_NChelper).
assert (Col A B M) by (conclude_def Col ).
assert (Col B A M) by (forward_using lemma_collinearorder).
assert (Par E H B A) by (forward_using lemma_parallelflip).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (neq M A) by (conclude lemma_inequalitysymmetric).
assert (Par E H M A) by (conclude lemma_collinearparallel).
assert (BetS H C E) by (conclude axiom_betweennesssymmetry).
assert (BetS M B A) by (conclude axiom_betweennesssymmetry).
assert (BetS F A B) by (conclude axiom_betweennesssymmetry).
assert (BetS D C B) by (conclude axiom_betweennesssymmetry).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (BetS E C H) by (conclude axiom_betweennesssymmetry).
assert (BetS A S C) by (conclude axiom_betweennesssymmetry).
assert (nCol C E A) by (forward_using lemma_NCorder).
assert (Col C E H) by (conclude_def Col ).
assert (Col C E E) by (conclude_def Col ).
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (neq H E) by (conclude lemma_inequalitysymmetric).
assert (nCol H E A) by (conclude lemma_NChelper).
assert (nCol E H A) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists Q, (BetS A Q H /\ BetS E S Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
assert (Col E S Q) by (conclude_def Col ).
assert (Col S E B) by (forward_using lemma_collinearorder).
assert (Col S E Q) by (forward_using lemma_collinearorder).
assert (Col E B Q) by (conclude lemma_collinear4).
assert (Col B E Q) by (forward_using lemma_collinearorder).
assert (neq H E) by (forward_using lemma_betweennotequal).
assert (neq C E) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists L, (BetS H E L /\ Cong E L C E)) by (conclude lemma_extension);destruct Tf as [L];spliter.
assert (BetS L E H) by (conclude axiom_betweennesssymmetry).
assert (Col L E H) by (conclude_def Col ).
assert (neq L H) by (forward_using lemma_betweennotequal).
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (Col A B M) by (conclude_def Col ).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (~ Meet A M L H).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists c, (neq A M /\ neq L H /\ Col A M c /\ Col L H c)) by (conclude_def Meet );destruct Tf as [c];spliter.
 assert (Col H E L) by (conclude_def Col ).
 assert (Col L H E) by (forward_using lemma_collinearorder).
 assert (neq H L) by (forward_using lemma_betweennotequal).
 assert (neq L H) by (conclude lemma_inequalitysymmetric).
 assert (Col H c E) by (conclude lemma_collinear4).
 assert (Col E H c) by (forward_using lemma_collinearorder).
 assert (Col A B M) by (conclude_def Col ).
 assert (Col M A B) by (forward_using lemma_collinearorder).
 assert (Col M A c) by (forward_using lemma_collinearorder).
 assert (neq A M) by (forward_using lemma_betweennotequal).
 assert (neq M A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B c) by (conclude lemma_collinear4).
 assert (Col B A F) by (conclude_def Col ).
 assert (Col A B F) by (forward_using lemma_collinearorder).
 assert (Col B c F) by (conclude lemma_collinear4).
 assert (Col F B c) by (forward_using lemma_collinearorder).
 assert (Meet E H F B) by (conclude_def Meet ).
 assert (~ Meet E H F B) by (conclude_def Par ).
 contradict.
 }
assert (BetS B Q E) by (conclude lemma_collinearbetween).
assert (nCol A H E) by (forward_using lemma_NCorder).
assert (Col A Q H) by (conclude_def Col ).
assert (Col A H Q) by (forward_using lemma_collinearorder).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col A H H) by (conclude_def Col ).
assert (neq Q H) by (forward_using lemma_betweennotequal).
assert (nCol Q H E) by (conclude lemma_NChelper).
assert (nCol Q E H) by (forward_using lemma_NCorder).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col Q E E) by (conclude_def Col ).
assert (Col Q E B) by (forward_using lemma_collinearorder).
assert (nCol B E H) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists T, (BetS B T C /\ BetS H T Q)) by (conclude postulate_Pasch_inner);destruct Tf as [T];spliter.
assert (BetS Q T H) by (conclude axiom_betweennesssymmetry).
assert (BetS A T H) by (conclude lemma_3_5b).
assert (Col B T C) by (conclude_def Col ).
assert (Col C B T) by (forward_using lemma_collinearorder).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (TS A C B H) by (conclude_def TS ).
assert (TS H C B A) by (conclude lemma_oppositesidesymmetric).
assert (Par H E M A) by (forward_using lemma_parallelflip).
assert (CongA A C E B A C) by (conclude lemma_equalanglesflip).
assert ((CongA H C B C B A /\ CongA D C E C B A /\ RT E C B C B A)) by (conclude proposition_29).
assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (CongA D C E A B C) by (conclude lemma_equalanglestransitive).
assert (BetS T C D) by (conclude lemma_3_6a).
assert (neq T D) by (forward_using lemma_betweennotequal).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (Col B C T) by (forward_using lemma_collinearorder).
assert (Col B C D) by (conclude_def Col ).
assert (nCol T D A) by (conclude lemma_NChelper).
assert (nCol A T D) by (forward_using lemma_NCorder).
assert (Col A T A) by (conclude_def Col ).
assert (Col A T H) by (conclude_def Col ).
assert (neq A H) by (forward_using lemma_betweennotequal).
assert (nCol A H D) by (conclude lemma_NChelper).
assert (nCol H A D) by (forward_using lemma_NCorder).
assert (BetS H T A) by (conclude axiom_betweennesssymmetry).
assert (BetS D C T) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists R, (BetS D R A /\ BetS H C R)) by (conclude postulate_Pasch_outer);destruct Tf as [R];spliter.
assert (Out C E R) by (conclude_def Out ).
assert (Out C A A) by (conclude lemma_ray4).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (BetS A R D) by (conclude axiom_betweennesssymmetry).
assert (CongA B A C A C E) by (conclude lemma_equalanglessymmetric).
assert (CongA B A C A C R) by (conclude lemma_equalangleshelper).
assert (nCol C A B) by (forward_using lemma_NCorder).
assert (CongA C A B B A C) by (conclude lemma_ABCequalsCBA).
assert (CongA C A B A C R) by (conclude lemma_equalanglestransitive).
assert (Out C D D) by (conclude lemma_ray4).
assert (CongA A B C D C E) by (conclude lemma_equalanglessymmetric).
assert (CongA A B C D C R) by (conclude lemma_equalangleshelper).
assert (nCol A D H) by (forward_using lemma_NCorder).
assert (Col D R A) by (conclude_def Col ).
assert (Col A D R) by (forward_using lemma_collinearorder).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col A D D) by (conclude_def Col ).
assert (neq D R) by (forward_using lemma_betweennotequal).
assert (neq R D) by (conclude lemma_inequalitysymmetric).
assert (nCol R D H) by (conclude lemma_NChelper).
assert (nCol R H D) by (forward_using lemma_NCorder).
assert (Col H C R) by (conclude_def Col ).
assert (Col R H C) by (forward_using lemma_collinearorder).
assert (eq R R) by (conclude cn_equalityreflexive).
assert (Col R H R) by (conclude_def Col ).
assert (neq C R) by (forward_using lemma_betweennotequal).
assert (neq R C) by (conclude lemma_inequalitysymmetric).
assert (nCol R C D) by (conclude lemma_NChelper).
assert (nCol D C R) by (forward_using lemma_NCorder).
assert (CongA D C R R C D) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C R C D) by (conclude lemma_equalanglestransitive).
assert (SumA C A B A B C A C D) by (conclude_def SumA ).
close.
Qed.

End Euclid.


