Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.proposition_16.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crossbar.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_17 : 
   forall A B C, 
   Triangle A B C ->
   exists X Y Z, SumA A B C B C A X Y Z.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq B C) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists D, (BetS B C D /\ Cong C D B C)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (Col B C D) by (conclude_def Col ).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B C B) by (conclude_def Col ).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (nCol B D A) by (conclude lemma_NChelper).
assert (nCol A D B) by (forward_using lemma_NCorder).
assert (LtA C B A A C D) by (conclude proposition_16).
assert (CongA A B C C B A) by (conclude lemma_ABCequalsCBA).
assert (LtA A B C A C D) by (conclude lemma_angleorderrespectscongruence2).
let Tf:=fresh in
assert (Tf:exists a d e, (BetS a e d /\ Out C A a /\ Out C D d /\ CongA A B C A C e)) by (conclude_def LtA );destruct Tf as [a[d[e]]];spliter.
assert (Out C a A) by (conclude lemma_ray5).
assert (Out C d D) by (conclude lemma_ray5).
assert (Col B C D) by (conclude_def Col ).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col B C C) by (conclude_def Col ).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (nCol C D A) by (conclude lemma_NChelper).
assert (Col C D C) by (conclude_def Col ).
assert (Col C D d) by (conclude lemma_rayimpliescollinear).
assert (neq C d) by (conclude lemma_ray2).
assert (nCol C d A) by (conclude lemma_NChelper).
assert (nCol C A d) by (forward_using lemma_NCorder).
assert (Col C A a) by (conclude lemma_rayimpliescollinear).
assert (Col C A C) by (conclude_def Col ).
assert (neq C a) by (conclude lemma_ray2).
assert (nCol C a d) by (conclude lemma_NChelper).
assert (nCol a C d) by (forward_using lemma_NCorder).
assert (nCol D A C) by (forward_using lemma_NCorder).
assert (Triangle a C d) by (conclude_def Triangle ).
let Tf:=fresh in
assert (Tf:exists E, (Out C e E /\ BetS A E D)) by (conclude lemma_crossbar);destruct Tf as [E];spliter.
assert (Out C E e) by (conclude lemma_ray5).
assert (Col A E D) by (conclude_def Col ).
assert (Col D A E) by (forward_using lemma_collinearorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col D A A) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq E A) by (conclude lemma_inequalitysymmetric).
assert (nCol E A C) by (conclude lemma_NChelper).
assert (nCol A C E) by (forward_using lemma_NCorder).
assert (nCol C E A) by (forward_using lemma_NCorder).
assert (Col C E e) by (conclude lemma_rayimpliescollinear).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C E C) by (conclude_def Col ).
assert (neq C e) by (conclude lemma_ray2).
assert (nCol C e A) by (conclude lemma_NChelper).
assert (nCol A C e) by (forward_using lemma_NCorder).
assert (Col C A a) by (conclude lemma_rayimpliescollinear).
assert (Col A C a) by (forward_using lemma_collinearorder).
assert (Col A C C) by (conclude_def Col ).
assert (neq C a) by (conclude lemma_ray2).
assert (neq a C) by (conclude lemma_inequalitysymmetric).
assert (nCol a C e) by (conclude lemma_NChelper).
assert (nCol E C A) by (forward_using lemma_NCorder).
assert (CongA a C e a C e) by (conclude lemma_equalanglesreflexive).
assert (CongA a C e A C E) by (conclude lemma_equalangleshelper).
assert (eq e e) by (conclude cn_equalityreflexive).
assert (neq C e) by (conclude lemma_ray2).
assert (Out C e e) by (conclude lemma_ray4).
assert (CongA A C e A C e) by (conclude lemma_equalanglesreflexive).
assert (CongA A C e a C e) by (conclude lemma_equalangleshelper).
assert (CongA A B C a C e) by (conclude lemma_equalanglestransitive).
assert (CongA A B C A C E) by (conclude lemma_equalanglestransitive).
assert (eq B B) by (conclude cn_equalityreflexive).
let Tf:=fresh in
assert (Tf:exists F, (BetS A F C /\ BetS B F E)) by (conclude postulate_Pasch_inner);destruct Tf as [F];spliter.
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (Col A F C) by (conclude_def Col ).
assert (Col A C F) by (forward_using lemma_collinearorder).
assert (Col A C C) by (conclude_def Col ).
assert (neq F C) by (forward_using lemma_betweennotequal).
assert (nCol F C B) by (conclude lemma_NChelper).
assert (nCol B C F) by (forward_using lemma_NCorder).
assert (BetS E F B) by (conclude axiom_betweennesssymmetry).
assert (CongA A C E E C A) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C E C A) by (conclude lemma_equalanglestransitive).
assert (CongA E C A E C A) by (conclude lemma_equalanglesreflexive).
assert (BetS C F A) by (conclude axiom_betweennesssymmetry).
assert (neq C F) by (forward_using lemma_betweennotequal).
assert (Out C F A) by (conclude lemma_ray4).
assert (Out C A F) by (conclude lemma_ray5).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (neq C E) by (forward_using lemma_NCdistinct).
assert (Out C E E) by (conclude lemma_ray4).
assert (CongA E C A E C F) by (conclude lemma_equalangleshelper).
assert (CongA A B C E C F) by (conclude lemma_equalanglestransitive).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (CongA B C A B C A) by (conclude lemma_equalanglesreflexive).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (Out C B B) by (conclude lemma_ray4).
assert (CongA B C A B C F) by (conclude lemma_equalangleshelper).
assert (CongA B C F F C B) by (conclude lemma_ABCequalsCBA).
assert (CongA B C A F C B) by (conclude lemma_equalanglestransitive).
assert (SumA A B C B C A E C B) by (conclude_def SumA ).
close.
Qed.

End Euclid.

