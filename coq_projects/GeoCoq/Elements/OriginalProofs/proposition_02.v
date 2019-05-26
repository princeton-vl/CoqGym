Require Export GeoCoq.Elements.OriginalProofs.proposition_01.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_differenceofparts.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_02 : 
   forall A B C, 
   neq A B -> neq B C ->
   exists X, Cong A X B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (equilateral A B D /\ Triangle A B D)) by (conclude proposition_01);destruct Tf as [D];spliter.
assert (Cong A B B D) by (conclude_def equilateral ).
assert (Cong B D A B) by (conclude lemma_congruencesymmetric).
assert (Cong B D B A) by (forward_using lemma_congruenceflip).
assert (Cong B D D A) by (conclude_def equilateral ).
assert (nCol A B D) by (conclude_def Triangle ).
assert (eq B B) by (conclude cn_equalityreflexive).
let Tf:=fresh in
assert (Tf:exists J, CI J B B C) by (conclude postulate_Euclid3);destruct Tf as [J];spliter.

assert (InCirc B J) by (conclude_def InCirc ).
assert (neq D B) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists P G, (Col D B P /\ BetS D B G /\ OnCirc P J /\ OnCirc G J /\ BetS P B G)) by (conclude postulate_line_circle);destruct Tf as [P[G]];spliter.
assert (neq D G) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists R, CI R D D G) by (conclude postulate_Euclid3);destruct Tf as [R];spliter.
assert (Cong B G B C) by (conclude axiom_circle_center_radius).
assert (Cong B C B G) by (conclude lemma_congruencesymmetric).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Cong D A B D) by (conclude lemma_congruencesymmetric).
assert (Cong D A D B) by (forward_using lemma_congruenceflip).
assert (Cong D G D G) by (conclude cn_congruencereflexive).
assert (InCirc A R) by (conclude_def InCirc ).
assert (neq D A) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists Q L, (Col D A Q /\ BetS D A L /\ OnCirc Q R /\ OnCirc L R /\ BetS Q A L)) by (conclude postulate_line_circle);destruct Tf as [Q[L]];spliter.
assert (Cong D L D G) by (conclude axiom_circle_center_radius).
assert (Cong D B D B) by (conclude cn_congruencereflexive).
assert (Cong D B D A) by (conclude lemma_congruencesymmetric).
assert (Cong D G D L) by (conclude lemma_congruencesymmetric).
assert (Cong B G A L) by (conclude lemma_differenceofparts).
assert (Cong A L B C) by (conclude cn_congruencetransitive).
close.
Unshelve.
exact A.
exact A.
Qed.

End Euclid.
