Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_pointreflectionisometry.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_27.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_31 : 
   forall A B C D, 
   BetS B D C -> nCol B C A ->
   exists X Y Z, BetS X A Y /\ CongA Y A D A D B /\ CongA Y A D B D A /\ CongA D A Y B D A /\ CongA X A D A D C /\ CongA X A D C D A /\ CongA D A X C D A /\ Par X Y B C /\ Cong X A D C /\ Cong A Y B D /\ Cong A Z Z D /\ Cong X Z Z C /\ Cong B Z Z Y /\ BetS X Z C /\ BetS B Z Y /\ BetS A Z D.
Proof.
intros.
assert (Col B D C) by (conclude_def Col ).
assert (~ eq A D).
 {
 intro.
 assert (Col B A C) by (conclude cn_equalitysub).
 assert (Col B C A) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS A M D /\ Cong M A M D)) by (conclude proposition_10);destruct Tf as [M];spliter.
assert (Cong A M M D) by (forward_using lemma_congruenceflip).
assert (Col C B D) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col C B B) by (conclude_def Col ).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (nCol B D A) by (conclude lemma_NChelper).
assert (Col B D C) by (conclude_def Col ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col B D D) by (conclude_def Col ).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (neq C D) by (conclude lemma_inequalitysymmetric).
assert (nCol C D A) by (conclude lemma_NChelper).
assert (nCol A D C) by (forward_using lemma_NCorder).
assert (Col A M D) by (conclude_def Col ).
assert (Col A D M) by (forward_using lemma_collinearorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A D A) by (conclude_def Col ).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (nCol A M C) by (conclude lemma_NChelper).
assert (~ eq C M).
 {
 intro.
 assert (Col A C M) by (conclude_def Col ).
 assert (Col A M C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq M C) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS C M E /\ Cong M E M C)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (Cong M C M E) by (conclude lemma_congruencesymmetric).
assert (Cong C M M E) by (forward_using lemma_congruenceflip).
assert (Midpoint C M E) by (conclude_def Midpoint ).
assert (neq A M) by (forward_using lemma_betweennotequal).
assert (nCol A D B) by (forward_using lemma_NCorder).
assert (nCol A M B) by (conclude lemma_NChelper).
assert (~ eq B M).
 {
 intro.
 assert (Col A B M) by (conclude_def Col ).
 assert (Col A M B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq M B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS B M F /\ Cong M F M B)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (Cong M F B M) by (forward_using lemma_congruenceflip).
assert (Cong B M M F) by (conclude lemma_congruencesymmetric).
assert (Midpoint B M F) by (conclude_def Midpoint ).
assert (Cong M D M A) by (conclude lemma_congruencesymmetric).
assert (BetS D M A) by (conclude axiom_betweennesssymmetry).
assert (Cong D M M A) by (forward_using lemma_congruenceflip).
assert (Midpoint D M A) by (conclude_def Midpoint ).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (Cong B D F A) by (conclude lemma_pointreflectionisometry).
assert (Cong D C A E) by (conclude lemma_pointreflectionisometry).
assert (Cong B C F E) by (conclude lemma_pointreflectionisometry).
assert (BetS F A E) by (conclude lemma_betweennesspreserved).
assert (BetS E A F) by (conclude axiom_betweennesssymmetry).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (neq A F) by (forward_using lemma_betweennotequal).
assert (Out A F F) by (conclude lemma_ray4).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (neq D B) by (conclude lemma_inequalitysymmetric).
assert (Out D B B) by (conclude lemma_ray4).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq D A) by (forward_using lemma_betweennotequal).
assert (Out D A A) by (conclude lemma_ray4).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (neq A D) by (conclude lemma_inequalitysymmetric).
assert (Out A D D) by (conclude lemma_ray4).
assert (nCol B M A) by (forward_using lemma_NCorder).
assert (Col B M F) by (conclude_def Col ).
assert (eq M M) by (conclude cn_equalityreflexive).
assert (Col B M M) by (conclude_def Col ).
assert (neq M F) by (forward_using lemma_betweennotequal).
assert (neq F M) by (conclude lemma_inequalitysymmetric).
assert (nCol F M A) by (conclude lemma_NChelper).
assert (nCol A M F) by (forward_using lemma_NCorder).
assert (Col A M A) by (conclude_def Col ).
assert (Col A M D) by (conclude_def Col ).
assert (nCol A D F) by (conclude lemma_NChelper).
assert (nCol F A D) by (forward_using lemma_NCorder).
assert (Cong D B A F) by (forward_using lemma_congruenceflip).
assert (Midpoint A M D) by (conclude_def Midpoint ).
assert (neq B A) by (forward_using lemma_NCdistinct).
assert (Cong B A F D) by (conclude lemma_pointreflectionisometry).
assert (Cong F D B A) by (conclude lemma_congruencesymmetric).
assert (Cong A F D B) by (conclude lemma_congruencesymmetric).
assert (Cong A D D A) by (conclude cn_equalityreverse).
assert (CongA F A D B D A) by (conclude_def CongA ).
assert (nCol B D A) by (conclude lemma_NChelper).
assert (CongA B D A A D B) by (conclude lemma_ABCequalsCBA).
assert (CongA F A D A D B) by (conclude lemma_equalanglestransitive).
assert (CongA A D B F A D) by (conclude lemma_equalanglessymmetric).
assert (nCol D A B) by (forward_using lemma_NCorder).
assert (nCol F A D) by (forward_using lemma_NCorder).
assert (CongA F A D D A F) by (conclude lemma_ABCequalsCBA).
assert (CongA A D B D A F) by (conclude lemma_equalanglestransitive).
assert (CongA D A F A D B) by (conclude lemma_equalanglessymmetric).
assert (nCol A D B) by (forward_using lemma_NCorder).
assert (CongA A D B B D A) by (conclude lemma_ABCequalsCBA).
assert (CongA D A F B D A) by (conclude lemma_equalanglestransitive).
assert (TS B A D F) by (conclude_def TS ).
assert (TS F A D B) by (conclude lemma_oppositesidesymmetric).
assert (BetS C D B) by (conclude axiom_betweennesssymmetry).
assert (Par F E C B) by (conclude proposition_27).
assert (Par E F B C) by (forward_using lemma_parallelflip).
assert (Cong D C E A) by (forward_using lemma_congruenceflip).
assert (Cong E A D C) by (conclude lemma_congruencesymmetric).
assert (Cong B D A F) by (forward_using lemma_congruenceflip).
assert (Cong A F B D) by (conclude lemma_congruencesymmetric).
assert (Cong M C E M) by (forward_using lemma_congruenceflip).
assert (Cong E M M C) by (conclude lemma_congruencesymmetric).
assert (neq E A) by (forward_using lemma_betweennotequal).
assert (neq A E) by (conclude lemma_inequalitysymmetric).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Out A E E) by (conclude lemma_ray4).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out D C C) by (conclude lemma_ray4).
assert (Cong E M M C) by (forward_using lemma_congruenceflip).
assert (BetS E M C) by (conclude axiom_betweennesssymmetry).
assert (Midpoint E M C) by (conclude_def Midpoint ).
assert (~ eq E D).
 {
 intro.
 assert (BetS C M D) by (conclude cn_equalitysub).
 assert (Col C M D) by (conclude_def Col ).
 assert (Col M D C) by (forward_using lemma_collinearorder).
 assert (Col A M D) by (conclude_def Col ).
 assert (Col M D A) by (forward_using lemma_collinearorder).
 assert (neq M D) by (forward_using lemma_betweennotequal).
 assert (Col D C A) by (conclude lemma_collinear4).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (neq D C) by (forward_using lemma_betweennotequal).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col B C A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq E D) by auto.
assert (neq D A) by (forward_using lemma_betweennotequal).
assert (neq A D) by (conclude lemma_inequalitysymmetric).
assert (Cong E D C A) by (conclude lemma_pointreflectionisometry).
assert (Cong A E D C) by (conclude lemma_pointreflectionisometry).
assert (Col E A F) by (conclude_def Col ).
assert (Col F A E) by (forward_using lemma_collinearorder).
assert (Col F A A) by (conclude_def Col ).
assert (nCol E A D) by (conclude lemma_NChelper).
assert (CongA E A D C D A) by (conclude_def CongA ).
assert (nCol C D A) by (forward_using lemma_NCorder).
assert (CongA C D A A D C) by (conclude lemma_ABCequalsCBA).
assert (CongA E A D A D C) by (conclude lemma_equalanglestransitive).
assert (nCol D A E) by (forward_using lemma_NCorder).
assert (CongA D A E E A D) by (conclude lemma_ABCequalsCBA).
assert (CongA D A E C D A) by (conclude lemma_equalanglestransitive).
remove_exists;eauto 20.
Qed.

End Euclid.
