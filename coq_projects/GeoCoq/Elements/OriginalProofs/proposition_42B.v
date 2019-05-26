Require Export GeoCoq.Elements.OriginalProofs.proposition_42.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesideflip.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_42B : 
   forall B C D E J K R a b c e, 
   Triangle a b c -> Midpoint b e c -> nCol J D K -> Midpoint B E C -> Cong E C e c -> nCol R E C ->
   exists X Z, PG X E C Z /\ EF a b e c X E C Z /\ CongA C E X J D K /\ OS R X E C.
Proof.
intros.
assert ((BetS B E C /\ Cong B E E C)) by (conclude_def Midpoint ).
assert ((BetS b e c /\ Cong b e e c)) by (conclude_def Midpoint ).
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (nCol a b c) by (conclude_def Triangle ).
assert (nCol E C R) by (forward_using lemma_NCorder).
assert (Col B E C) by (conclude_def Col ).
assert (Col E C B) by (forward_using lemma_collinearorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col E C C) by (conclude_def Col ).
assert (nCol B C R) by (conclude lemma_NChelper).
rename_H H;let Tf:=fresh in
assert (Tf:exists P H, (Out B C H /\ CongA P B H a b c /\ OS P R B C)) by (conclude proposition_23C);destruct Tf as [P[H]];spliter.
assert (Cong B E e c) by (conclude lemma_congruencetransitive).
assert (Cong E C B E) by (conclude lemma_congruencesymmetric).
assert (Cong E C e c) by (conclude lemma_congruencetransitive).
assert (Cong B E e c) by (conclude lemma_congruencetransitive).
assert (Cong e c b e) by (conclude lemma_congruencesymmetric).
assert (Cong B E b e) by (conclude lemma_congruencetransitive).
assert (Cong B C b c) by (conclude cn_sumofparts).
assert (CongA a b c P B H) by (conclude lemma_equalanglessymmetric).
assert (Out B H C) by (conclude lemma_ray5).
assert (nCol B C P) by (conclude_def OS ).
assert (neq B P) by (forward_using lemma_NCdistinct).
assert (nCol a b c) by (conclude_def Triangle ).
assert (neq b a) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists A, (Out B P A /\ Cong B A b a)) by (conclude lemma_layoff);destruct Tf as [A];spliter.
assert (CongA a b c A B C) by (conclude lemma_equalangleshelper).
assert (CongA A B C a b c) by (conclude lemma_equalanglessymmetric).
assert (nCol A B C) by (conclude lemma_equalanglesNC).
assert (Triangle A B C) by (conclude_def Triangle ).
assert (Cong A C a c) by (conclude proposition_04).
assert (Cong A B a b) by (forward_using lemma_congruenceflip).
assert (Cong C A c a) by (forward_using lemma_congruenceflip).
assert (Cong E A e a) by (conclude lemma_interior5).
assert (Cong A E a e) by (forward_using lemma_congruenceflip).
assert (Cong E B e b) by (forward_using lemma_congruenceflip).
assert (Col B E C) by (conclude_def Col ).
assert (Col B C E) by (forward_using lemma_collinearorder).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B C B) by (conclude_def Col ).
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (nCol B E A) by (conclude lemma_NChelper).
assert (nCol A E B) by (forward_using lemma_NCorder).
assert (Col b e c) by (conclude_def Col ).
assert (Col b c e) by (forward_using lemma_collinearorder).
assert (nCol b c a) by (forward_using lemma_NCorder).
assert (eq b b) by (conclude cn_equalityreflexive).
assert (Col b c b) by (conclude_def Col ).
assert (neq b e) by (forward_using lemma_betweennotequal).
assert (nCol b e a) by (conclude lemma_NChelper).
assert (nCol a e b) by (forward_using lemma_NCorder).
assert (Triangle A E B) by (conclude_def Triangle ).
assert (Cong_3 A E B a e b) by (conclude_def Cong_3 ).
assert (ET A E B a e b) by (conclude axiom_congruentequal).
assert (Col C B E) by (forward_using lemma_collinearorder).
assert (neq E C) by (forward_using lemma_betweennotequal).
assert (neq C E) by (conclude lemma_inequalitysymmetric).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C B C) by (conclude_def Col ).
assert (nCol C E A) by (conclude lemma_NChelper).
assert (nCol A E C) by (forward_using lemma_NCorder).
assert (Triangle A E C) by (conclude_def Triangle ).
assert (Cong_3 A E C a e c) by (conclude_def Cong_3 ).
assert (ET A E C a e c) by (conclude axiom_congruentequal).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col A E E) by (conclude_def Col ).
assert (TS B A E C) by (conclude_def TS ).
assert (eq e e) by (conclude cn_equalityreflexive).
assert (Col a e e) by (conclude_def Col ).
assert (TS b a e c) by (conclude_def TS ).
assert (EF A B E C a b e c) by (conclude axiom_paste3).
assert (EF a b e c A B E C) by (conclude axiom_EFsymmetric).
let Tf:=fresh in
assert (Tf:exists F G, (PG F E C G /\ EF A B E C F E C G /\ CongA C E F J D K /\ Col F G A)) by (conclude proposition_42);destruct Tf as [F[G]];spliter.
assert (EF a b e c F E C G) by (conclude axiom_EFtransitive).
assert (OS R P B C) by (forward_using lemma_samesidesymmetric).
assert (Col B B C) by (conclude_def Col ).
assert (OS R A B C) by (conclude lemma_sameside2).
assert (OS R A C B) by (conclude lemma_samesideflip).
assert (OS R A C E) by (conclude lemma_samesidecollinear).
assert (OS A R C E) by (forward_using lemma_samesidesymmetric).
assert (OS A R E C) by (conclude lemma_samesideflip).
assert (Col G F A) by (forward_using lemma_collinearorder).
assert (Par F G E C) by (conclude_def PG ).
assert (Par E C F G) by (conclude lemma_parallelsymmetric).
assert (Par E C G F) by (forward_using lemma_parallelflip).
assert (OS R F E C).
by cases on (eq A F \/ neq A F).
{
 assert (OS R A E C) by (conclude lemma_samesideflip).
 assert (OS R F E C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Par E C A F) by (conclude lemma_collinearparallel).
 assert (Par E C F A) by (forward_using lemma_parallelflip).
 assert (TP E C F A) by (conclude lemma_paralleldef2B).
 assert (OS F A E C) by (conclude_def TP ).
 assert (OS F R E C) by (conclude lemma_samesidetransitive).
 assert (OS R F E C) by (forward_using lemma_samesidesymmetric).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


