Require Export GeoCoq.Elements.OriginalProofs.proposition_01.
Require Export GeoCoq.Elements.OriginalProofs.proposition_03.
Require Export GeoCoq.Elements.OriginalProofs.lemma_interior5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_twolines.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_10 : 
   forall A B, 
   neq A B ->
   exists X, BetS A X B /\ Cong X A X B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists C, (equilateral A B C /\ Triangle A B C)) by (conclude proposition_01);destruct Tf as [C];spliter.
assert (nCol A B C) by (conclude_def Triangle ).
assert ((Cong A B B C /\ Cong B C C A)) by (conclude_def equilateral ).
assert (Cong A C C B) by (forward_using lemma_doublereverse).
assert (Cong A C B C) by (forward_using lemma_congruenceflip).
assert (~ eq C B).
 {
 intro.
 assert (Col A C B) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists D, (BetS C B D /\ Cong B D A B)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert (~ eq C A).
 {
 intro.
 assert (Col B C A) by (conclude_def Col ).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS C A E /\ Cong A E A B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (BetS D B C) by (conclude axiom_betweennesssymmetry).
assert (BetS E A C) by (conclude axiom_betweennesssymmetry).
assert (~ Col D C E).
 {
 intro.
 assert (Col C A E) by (conclude_def Col ).
 assert (Col C B D) by (conclude_def Col ).
 assert (Col E C D) by (forward_using lemma_collinearorder).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 assert (neq E C) by (conclude lemma_inequalitysymmetric).
 assert (Col C D A) by (conclude lemma_collinear4).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (neq C D) by (forward_using lemma_betweennotequal).
 assert (neq D C) by (conclude lemma_inequalitysymmetric).
 assert (Col C B A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists F, (BetS D F A /\ BetS E F B)) by (conclude postulate_Pasch_inner);destruct Tf as [F];spliter.
assert (BetS B F E) by (conclude axiom_betweennesssymmetry).
assert (BetS A F D) by (conclude axiom_betweennesssymmetry).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (~ Col A D C).
 {
 intro.
 assert (Col C B D) by (conclude_def Col ).
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS A M B /\ BetS C M F)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
assert (Cong C A C B) by (forward_using lemma_congruenceflip).
assert (Cong A B A E) by (conclude lemma_congruencesymmetric).
assert (Cong B D A E) by (conclude lemma_congruencetransitive).
assert (Cong A E B D) by (conclude lemma_congruencesymmetric).
assert (Cong A B B A) by (conclude cn_equalityreverse).
assert (Cong C B C A) by (conclude lemma_congruencesymmetric).
assert (Cong B E A D) by (conclude axiom_5_line).
assert (Cong B F B F) by (conclude cn_congruencereflexive).
assert (Lt B F B E) by (conclude_def Lt ).
assert (Cong A D B E) by (conclude lemma_congruencesymmetric).
let Tf:=fresh in
assert (Tf:exists G, (BetS A G D /\ Cong A G B F)) by (conclude proposition_03);destruct Tf as [G];spliter.
assert (Cong G D F E) by (conclude lemma_differenceofparts).
assert (Cong E F D G) by (forward_using lemma_doublereverse).
assert (Cong F B G A) by (forward_using lemma_doublereverse).
assert (Cong E A D B) by (forward_using lemma_congruenceflip).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (BetS D G A) by (conclude axiom_betweennesssymmetry).
assert (Cong F A G B) by (conclude lemma_interior5).
assert (Cong A F B G) by (forward_using lemma_congruenceflip).
assert (Cong E D D E) by (conclude cn_equalityreverse).
assert (Cong F D G E) by (conclude lemma_interior5).
assert (BetS B G E) by (conclude lemma_betweennesspreserved).
assert (BetS E G B) by (conclude axiom_betweennesssymmetry).
assert (~ Col A D E).
 {
 intro.
 assert (Col C A E) by (conclude_def Col ).
 assert (Col A E D) by (forward_using lemma_collinearorder).
 assert (Col A E C) by (forward_using lemma_collinearorder).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (Col E D C) by (conclude lemma_collinear4).
 assert (Col E C D) by (forward_using lemma_collinearorder).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 assert (neq E C) by (conclude lemma_inequalitysymmetric).
 assert (Col C D A) by (conclude lemma_collinear4).
 assert (Col C B D) by (conclude_def Col ).
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (neq C D) by (forward_using lemma_betweennotequal).
 assert (neq D C) by (conclude lemma_inequalitysymmetric).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col A D B).
 {
 intro.
 assert (Col D B A) by (forward_using lemma_collinearorder).
 assert (Col C B D) by (conclude_def Col ).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Cut A D E B G) by (conclude_def Cut ).
assert (Cut A D E B F) by (conclude_def Cut ).
assert (~ Col D E B).
 {
 intro.
 assert (Col C B D) by (conclude_def Col ).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (Col D B E) by (forward_using lemma_collinearorder).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B C E) by (conclude lemma_collinear4).
 assert (Col C A E) by (conclude_def Col ).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (Col E C B) by (forward_using lemma_collinearorder).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 assert (neq E C) by (conclude lemma_inequalitysymmetric).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (eq G F) by (conclude lemma_twolines).
assert (Cong A F B F) by (conclude cn_equalitysub).
assert (Cong F A F B) by (forward_using lemma_congruenceflip).
assert (Cong C M C M) by (conclude cn_congruencereflexive).
assert (Cong M F M F) by (conclude cn_congruencereflexive).
assert (Cong M A M B) by (conclude lemma_interior5).
close.
Qed.

End Euclid.


