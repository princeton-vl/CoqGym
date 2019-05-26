Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_oppositesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_14 : 
   forall A B C D E, 
   RT A B C D B E -> Out B C D -> TS E D B A ->
   Supp A B C D E /\ BetS A B E.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d e, (Supp a b c d e /\ CongA A B C a b c /\ CongA D B E d b e)) by (conclude_def RT );destruct Tf as [a[b[c[d[e]]]]];spliter.
assert (CongA a b c A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA d b e D B E) by (conclude lemma_equalanglessymmetric).
assert (nCol A B C) by (conclude lemma_equalanglesNC).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (nCol D B E) by (conclude lemma_equalanglesNC).
assert (neq B E) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists T, (BetS A B T /\ Cong B T B E)) by (conclude lemma_extension);destruct Tf as [T];spliter.
assert (Cong B D B D) by (conclude cn_congruencereflexive).
assert (Supp A B C D T) by (conclude_def Supp ).
assert (CongA a b c A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA d b e D B E) by (conclude lemma_equalanglessymmetric).
assert (CongA d b e D B T) by (conclude lemma_supplements).
assert (CongA D B E D B T) by (conclude lemma_equalanglestransitive).
assert (CongA D B T D B E) by (conclude lemma_equalanglessymmetric).
assert (Col A B T) by (conclude_def Col ).
assert (neq B T) by (forward_using lemma_betweennotequal).
assert (neq T B) by (conclude lemma_inequalitysymmetric).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (nCol T B C) by (conclude lemma_NChelper).
assert (nCol C B T) by (forward_using lemma_NCorder).
assert (Col B C D) by (conclude lemma_rayimpliescollinear).
assert (Col C B D) by (forward_using lemma_collinearorder).
assert (neq D B) by (forward_using lemma_NCdistinct).
assert (Col C B B) by (conclude_def Col ).
assert (nCol D B T) by (conclude lemma_NChelper).
assert (Cong D T D E) by (conclude proposition_04).
assert (Cong T D E D) by (forward_using lemma_congruenceflip).
assert (Cong T B E B) by (forward_using lemma_congruenceflip).
assert (Col D B B) by (conclude_def Col ).
assert (TS A D B E) by (conclude lemma_oppositesidesymmetric).
let Tf:=fresh in
assert (Tf:exists m, (BetS A m E /\ Col D B m /\ nCol D B A)) by (conclude_def TS );destruct Tf as [m];spliter.
assert (BetS E m A) by (conclude axiom_betweennesssymmetry).
assert (BetS T B A) by (conclude axiom_betweennesssymmetry).
assert (OS T E D B) by (conclude_def OS ).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (eq T E) by (conclude proposition_07).
assert (BetS A B E) by (conclude cn_equalitysub).
assert (Supp A B C D E) by (conclude_def Supp ).
close.
Qed.

End Euclid.


