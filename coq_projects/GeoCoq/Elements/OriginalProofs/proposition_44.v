Require Export GeoCoq.Elements.OriginalProofs.proposition_42B.
Require Export GeoCoq.Elements.OriginalProofs.proposition_44A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_44 : 
   forall A B D J N R a b c, 
   Triangle a b c -> nCol J D N -> nCol A B R ->
   exists X Y Z, PG A B X Y /\ CongA A B X J D N /\ EF a b Z c A B X Y /\ Midpoint b Z c /\ TS X A B R.
Proof.
intros.
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (nCol a b c) by (conclude_def Triangle ).
assert (neq b c) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists m, (BetS b m c /\ Cong m b m c)) by (conclude proposition_10);destruct Tf as [m];spliter.
assert (Cong b m m c) by (forward_using lemma_congruenceflip).
assert (Midpoint b m c) by (conclude_def Midpoint ).
assert (neq m c) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists E, (BetS A B E /\ Cong B E m c)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (Col A B E) by (conclude_def Col ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B A B) by (conclude_def Col ).
assert (nCol B A R) by (forward_using lemma_NCorder).
assert (nCol B E R) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists g e, (Out B E e /\ CongA g B e J D N /\ OS g R B E)) by (conclude proposition_23C);destruct Tf as [g[e]];spliter.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists P, (BetS B A P /\ Cong A P B A)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (neq E B) by (conclude lemma_inequalitysymmetric).
assert (neq b m) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists Q, (BetS E B Q /\ Cong B Q b m)) by (conclude lemma_extension);destruct Tf as [Q];spliter.
assert (Cong b m m c) by (forward_using lemma_congruenceflip).
assert (Cong B Q m c) by (conclude lemma_congruencetransitive).
assert (Cong m c B E) by (conclude lemma_congruencesymmetric).
assert (Cong B Q B E) by (conclude lemma_congruencetransitive).
assert (BetS Q B E) by (conclude axiom_betweennesssymmetry).
assert (Cong Q B B E) by (forward_using lemma_congruenceflip).
assert (Midpoint Q B E) by (conclude_def Midpoint ).
assert (nCol B A R) by (forward_using lemma_NCorder).
assert (Col A B E) by (conclude_def Col ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (nCol B E R) by (conclude lemma_NChelper).
assert (nCol R B E) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists G F, (PG G B E F /\ EF a b m c G B E F /\ CongA E B G J D N /\ OS R G B E)) by (conclude proposition_42B);destruct Tf as [G[F]];spliter.
assert (PG B E F G) by (conclude lemma_PGrotate).
let Tf:=fresh in
assert (Tf:exists M L, (PG A B M L /\ CongA A B M J D N /\ EF B E F G L M B A /\ BetS G B M)) by (conclude proposition_44A);destruct Tf as [M[L]];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (Par G B E F) by (conclude_def PG ).
assert (nCol G B E) by (forward_using lemma_parallelNC).
assert (nCol E B G) by (forward_using lemma_NCorder).
assert (Col E B A) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col E B B) by (conclude_def Col ).
assert (nCol A B G) by (conclude lemma_NChelper).
assert (TS G A B M) by (conclude_def TS ).
assert (EF a b m c B E F G) by (forward_using axiom_EFpermutation).
assert (EF a b m c L M B A) by (conclude axiom_EFtransitive).
assert (EF a b m c A B M L) by (forward_using axiom_EFpermutation).
assert (Col B E A) by (forward_using lemma_collinearorder).
assert (OS R G B A) by (conclude lemma_samesidecollinear).
assert (OS R G A B) by (conclude lemma_samesideflip).
assert (TS R A B M) by (conclude lemma_planeseparation).
assert (TS M A B R) by (conclude lemma_oppositesidesymmetric).
close.
Qed.

End Euclid.


