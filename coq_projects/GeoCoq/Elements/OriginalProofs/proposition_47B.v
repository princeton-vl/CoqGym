Require Export GeoCoq.Elements.OriginalProofs.proposition_47A.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleaddition.
Require Export GeoCoq.Elements.OriginalProofs.proposition_41.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_47B : 
   forall A B C D E F G, 
   Triangle A B C -> Per B A C -> SQ A B F G -> TS G B A C -> SQ B C E D -> TS D C B A ->
   exists X Y, PG B X Y D /\ BetS B X C /\ PG X C E Y /\ BetS D Y E /\ BetS Y X A /\ Per D Y A /\ EF A B F G B X Y D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M L, (PG B M L D /\ BetS B M C /\ PG M C E L /\ BetS D L E /\ BetS L M A /\ Per D L A)) by (conclude proposition_47A);destruct Tf as [M[L]];spliter.

let Tf:=fresh in
assert (Tf:exists N, (BetS D N A /\ Col C B N /\ nCol C B D)) by (conclude_def TS );destruct Tf as [N];spliter.
assert (Per G A B) by (conclude_def SQ ).
assert (BetS G A C) by (conclude lemma_righttogether).
assert (Per A B F) by (conclude_def SQ ).
assert (Per F B A) by (conclude lemma_8_2).
assert (Per D B C) by (conclude_def SQ ).
assert (nCol A B C) by (conclude_def Triangle ).
assert (PG A B F G) by (conclude lemma_squareparallelogram).
assert (Par A B F G) by (conclude_def PG ).
assert (Par A B G F) by (forward_using lemma_parallelflip).
assert (TP A B G F) by (conclude lemma_paralleldef2B).
assert (OS G F A B) by (conclude_def TP ).
assert (OS F G A B) by (forward_using lemma_samesidesymmetric).
assert (TS G A B C) by (conclude lemma_oppositesideflip).
assert (TS F A B C) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists a, (BetS F a C /\ Col A B a /\ nCol A B F)) by (conclude_def TS );destruct Tf as [a];spliter.
assert (Col B A a) by (forward_using lemma_collinearorder).
assert (Par A G B F) by (conclude_def PG ).
assert (Par A G F B) by (forward_using lemma_parallelflip).
assert (Col G A C) by (conclude_def Col ).
assert (Col A G C) by (forward_using lemma_collinearorder).
assert (neq G C) by (forward_using lemma_betweennotequal).
assert (neq C G) by (conclude lemma_inequalitysymmetric).
assert (Par F B A G) by (conclude lemma_parallelsymmetric).
assert (Par F B C G) by (conclude lemma_collinearparallel).
assert (Par F B G C) by (forward_using lemma_parallelflip).
assert (~ Meet F B G C) by (conclude_def Par ).
assert (neq A C) by (forward_using lemma_NCdistinct).
assert (nCol A B F) by (forward_using lemma_parallelNC).
assert (neq F A) by (forward_using lemma_NCdistinct).
assert (neq F B) by (forward_using lemma_NCdistinct).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col F B B) by (conclude_def Col ).
assert (BetS B a A) by (conclude lemma_collinearbetween).
assert (neq B a) by (forward_using lemma_betweennotequal).
assert (Out B a A) by (conclude lemma_ray4).
assert (neq B F) by (conclude lemma_inequalitysymmetric).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (Out B F F) by (conclude lemma_ray4).
assert (nCol A B F) by (forward_using lemma_parallelNC).
assert (nCol F B A) by (forward_using lemma_NCorder).
assert (CongA F B A F B A) by (conclude lemma_equalanglesreflexive).
assert (Out B A a) by (conclude lemma_ray5).
assert (CongA F B A F B a) by (conclude lemma_equalangleshelper).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out B C C) by (conclude lemma_ray4).
assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
assert (CongA A B C a B C) by (conclude lemma_equalangleshelper).
assert (SumA F B A A B C F B C) by (conclude_def SumA ).
let Tf:=fresh in
assert (Tf:exists c, (BetS D c A /\ Col C B c /\ nCol C B D)) by (conclude_def TS );destruct Tf as [c];spliter.
assert (PG B C E D) by (conclude lemma_squareparallelogram).
assert (Par B D C E) by (conclude_def PG ).
assert (Par C E B D) by (conclude lemma_parallelsymmetric).
assert (Par C E D B) by (forward_using lemma_parallelflip).
assert (Col B C c) by (forward_using lemma_collinearorder).
assert (Col B M C) by (conclude_def Col ).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (Col C B c) by (forward_using lemma_collinearorder).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (Col B M c) by (conclude lemma_collinear4).
assert (Par B D M L) by (conclude_def PG ).
assert (Col L M A) by (conclude_def Col ).
assert (Col M L A) by (forward_using lemma_collinearorder).
assert (neq L A) by (forward_using lemma_betweennotequal).
assert (neq A L) by (conclude lemma_inequalitysymmetric).
assert (Par B D A L) by (conclude lemma_collinearparallel).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Par D B L A) by (forward_using lemma_parallelflip).
assert (~ Meet D B L A) by (conclude_def Par ).
assert (nCol B D L) by (forward_using lemma_parallelNC).
assert (neq D B) by (forward_using lemma_NCdistinct).
assert (neq M A) by (forward_using lemma_betweennotequal).
assert (neq L M) by (forward_using lemma_betweennotequal).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col D B B) by (conclude_def Col ).
assert (BetS B c M) by (conclude lemma_collinearbetween).
assert (BetS B c C) by (conclude lemma_3_6b).
assert (nCol D B A) by (forward_using lemma_parallelNC).
assert (~ eq B c).
 {
 intro.
 assert (Col D B c) by (conclude_def Col ).
 assert (Col D c A) by (conclude_def Col ).
 assert (Col c D B) by (forward_using lemma_collinearorder).
 assert (Col c D A) by (forward_using lemma_collinearorder).
 assert (neq D c) by (forward_using lemma_betweennotequal).
 assert (neq c D) by (conclude lemma_inequalitysymmetric).
 assert (Col D B A) by (conclude lemma_collinear4).
 contradict.
 }
assert (Out B c C) by (conclude lemma_ray4).
assert (Out B C c) by (conclude lemma_ray5).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (CongA C B A C B A) by (conclude lemma_equalanglesreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Out B A A) by (conclude lemma_ray4).
assert (CongA C B A c B A) by (conclude lemma_equalangleshelper).
assert (nCol C D B) by (forward_using lemma_parallelNC).
assert (nCol D B C) by (forward_using lemma_NCorder).
assert (CongA D B C D B C) by (conclude lemma_equalanglesreflexive).
assert (neq B D) by (conclude lemma_inequalitysymmetric).
assert (Out B D D) by (conclude lemma_ray4).
assert (CongA D B C D B c) by (conclude lemma_equalangleshelper).
assert (SumA D B C C B A D B A) by (conclude_def SumA ).
assert (CongA F B A D B C) by (conclude lemma_Euclid4).
assert (CongA A B C C B A) by (conclude lemma_ABCequalsCBA).
assert (CongA F B C D B A) by (conclude lemma_angleaddition).
assert (CongA D B A F B C) by (conclude lemma_equalanglessymmetric).
assert (~ Col C B F).
 {
 intro.
 assert (Col F B C) by (forward_using lemma_collinearorder).
 assert (Per C B A) by (conclude lemma_collinearright).
 assert (~ Per C B A) by (conclude lemma_8_7).
 contradict.
 }
assert (nCol F B C) by (assert (nCol C B F) by auto;forward_using lemma_NCorder).
assert (CongA F B C C B F) by (conclude lemma_ABCequalsCBA).
assert (CongA D B A C B F) by (conclude lemma_equalanglestransitive).
assert (Cong A B B F) by (conclude_def SQ ).
assert (Cong A B F B) by (forward_using lemma_congruenceflip).
assert (Cong F B A B) by (conclude lemma_congruencesymmetric).
assert (Cong B F B A) by (forward_using lemma_congruenceflip).
assert (Cong B A B F) by (conclude lemma_congruencesymmetric).
assert (Cong B C D B) by (conclude_def SQ ).
assert (Cong D B B C) by (conclude lemma_congruencesymmetric).
assert (Cong B D B C) by (forward_using lemma_congruenceflip).
assert ((Cong D A C F /\ CongA B D A B C F /\ CongA B A D B F C)) by (conclude proposition_04).
assert (Cong A D F C) by (forward_using lemma_congruenceflip).
assert (CongA B F C B A D) by (conclude lemma_equalanglessymmetric).
assert (nCol B A D) by (conclude lemma_equalanglesNC).
assert (nCol A B D) by (forward_using lemma_NCorder).
assert (Triangle A B D) by (conclude_def Triangle ).
assert (Cong_3 A B D F B C) by (conclude_def Cong_3 ).
assert (ET A B D F B C) by (conclude axiom_congruentequal).
assert (Par B M L D) by (conclude_def PG ).
assert (Par B D M L) by (conclude_def PG ).
assert (Par M L B D) by (conclude lemma_parallelsymmetric).
assert (Par M B D L) by (forward_using lemma_parallelflip).
assert (PG M B D L) by (conclude_def PG ).
assert (Col M L A) by (forward_using lemma_collinearorder).
assert (ET M B D A B D) by (conclude proposition_41).
assert (PG A B F G) by (conclude lemma_squareparallelogram).
assert (PG B A G F) by (conclude lemma_PGflip).
assert (Col G A C) by (conclude_def Col ).
assert (Col A G C) by (forward_using lemma_collinearorder).
assert (ET A B F C B F) by (conclude proposition_41).
assert (ET A B F F B C) by (forward_using axiom_ETpermutation).
assert (ET F B C A B D) by (conclude axiom_ETsymmetric).
assert (ET A B F A B D) by (conclude axiom_ETtransitive).
assert (ET A B D M B D) by (conclude axiom_ETsymmetric).
assert (ET A B F M B D) by (conclude axiom_ETtransitive).
assert (Cong_3 A B F F G A) by (conclude proposition_34).
assert (ET A B F F G A) by (conclude axiom_congruentequal).
assert (PG B M L D) by (conclude lemma_PGflip).
assert (Cong_3 M B D D L M) by (conclude proposition_34).
assert (ET M B D D L M) by (conclude axiom_congruentequal).
assert (ET F G A A B F) by (conclude axiom_ETsymmetric).
assert (ET F G A A B D) by (conclude axiom_ETtransitive).
assert (ET F G A M B D) by (conclude axiom_ETtransitive).
assert (ET F G A D L M) by (conclude axiom_ETtransitive).
assert (ET F G A D M L) by (forward_using axiom_ETpermutation).
assert (ET D M L F G A) by (conclude axiom_ETsymmetric).
assert (ET D M L F A G) by (forward_using axiom_ETpermutation).
assert (ET F A G D M L) by (conclude axiom_ETsymmetric).
assert (ET A B F D M B) by (forward_using axiom_ETpermutation).
assert (ET D M B A B F) by (conclude axiom_ETsymmetric).
assert (ET D M B F A B) by (forward_using axiom_ETpermutation).
assert (ET F A B D M B) by (conclude axiom_ETsymmetric).
let Tf:=fresh in
assert (Tf:exists m, (Midpoint A m F /\ Midpoint B m G)) by (conclude lemma_diagonalsbisect);destruct Tf as [m];spliter.
assert (BetS A m F) by (conclude_def Midpoint ).
assert (BetS B m G) by (conclude_def Midpoint ).
assert (BetS F m A) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists n, (Midpoint B n L /\ Midpoint M n D)) by (conclude lemma_diagonalsbisect);destruct Tf as [n];spliter.
assert (BetS B n L) by (conclude_def Midpoint ).
assert (BetS M n D) by (conclude_def Midpoint ).
assert (BetS D n M) by (conclude axiom_betweennesssymmetry).
assert (Col M n D) by (conclude_def Col ).
assert (Col D M n) by (forward_using lemma_collinearorder).
assert (nCol B M D) by (forward_using lemma_parallelNC).
assert (nCol D M B) by (forward_using lemma_NCorder).
assert (EF F B A G D B M L) by (conclude axiom_paste3).
assert (EF F B A G B M L D) by (forward_using axiom_EFpermutation).
assert (EF B M L D F B A G) by (conclude axiom_EFsymmetric).
assert (EF B M L D A B F G) by (forward_using axiom_EFpermutation).
assert (EF A B F G B M L D) by (conclude axiom_EFsymmetric).
close.
Qed.

End Euclid.


