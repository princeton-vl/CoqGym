Require Export GeoCoq.Elements.OriginalProofs.proposition_10.
Require Export GeoCoq.Elements.OriginalProofs.proposition_15.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_16 : 
   forall A B C D, 
   Triangle A B C -> BetS B C D ->
   LtA B A C A C D /\ LtA C B A A C D.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS A E C /\ Cong E A E C)) by (conclude proposition_10);destruct Tf as [E];spliter.
assert (~ eq B E).
 {
 intro.
 assert (BetS A B C) by (conclude cn_equalitysub).
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq E B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS B E F /\ Cong E F E B)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (neq E C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists G, (BetS A C G /\ Cong C G E C)) by (conclude lemma_extension);destruct Tf as [G];spliter.
assert (~ Col B E A).
 {
 intro.
 assert (Col A E C) by (conclude_def Col ).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (Col E A C) by (forward_using lemma_collinearorder).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 contradict.
 }
assert (CongA B E A C E F) by (conclude proposition_15a).
assert (~ Col A E B).
 {
 intro.
 assert (Col B E A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A E B B E A) by (conclude lemma_ABCequalsCBA).
assert (CongA A E B C E F) by (conclude lemma_equalanglestransitive).
assert (Cong B E F E) by (forward_using lemma_doublereverse).
assert (Cong E B E F) by (forward_using lemma_congruenceflip).
assert (~ Col E A B).
 {
 intro.
 assert (Col B E A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert ((Cong A B C F /\ CongA E A B E C F /\ CongA E B A E F C)) by (conclude proposition_04).
assert (~ Col B A E).
 {
 intro.
 assert (Col E A B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out A C E) by (conclude lemma_ray4).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (neq A B) by (forward_using lemma_angledistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Out A B B) by (conclude lemma_ray4).
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B A C B A C) by (conclude lemma_equalanglesreflexive).
assert (CongA B A C B A E) by (conclude lemma_equalangleshelper).
assert (CongA B A E E A B) by (conclude lemma_ABCequalsCBA).
assert (CongA B A C E A B) by (conclude lemma_equalanglestransitive).
assert (CongA B A C E C F) by (conclude lemma_equalanglestransitive).
assert (BetS C E A) by (conclude axiom_betweennesssymmetry).
assert (neq C E) by (forward_using lemma_betweennotequal).
assert (Out C E A) by (conclude lemma_ray4).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (~ Col E C F).
 {
 intro.
 assert (Col B E F) by (conclude_def Col ).
 assert (Col F E B) by (forward_using lemma_collinearorder).
 assert (Col F E C) by (forward_using lemma_collinearorder).
 assert (neq E F) by (forward_using lemma_betweennotequal).
 assert (neq F E) by (conclude lemma_inequalitysymmetric).
 assert (Col E B C) by (conclude lemma_collinear4).
 assert (Col A E C) by (conclude_def Col ).
 assert (Col E C B) by (forward_using lemma_collinearorder).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (neq E C) by (forward_using lemma_betweennotequal).
 assert (Col C B A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq C F).
 {
 intro.
 assert (Col E C F) by (conclude_def Col ).
 contradict.
 }
assert (Out C F F) by (conclude lemma_ray4).
assert (CongA E C F E C F) by (conclude lemma_equalanglesreflexive).
assert (CongA E C F A C F) by (conclude lemma_equalangleshelper).
assert (CongA B A C A C F) by (conclude lemma_equalanglestransitive).
assert (BetS D C B) by (conclude axiom_betweennesssymmetry).
assert (BetS F E B) by (conclude axiom_betweennesssymmetry).
assert (~ Col D B F).
 {
 intro.
 assert (Col F B D) by (forward_using lemma_collinearorder).
 assert (Col B E F) by (conclude_def Col ).
 assert (Col F B E) by (forward_using lemma_collinearorder).
 assert (neq B F) by (forward_using lemma_betweennotequal).
 assert (neq F B) by (conclude lemma_inequalitysymmetric).
 assert (Col B D E) by (conclude lemma_collinear4).
 assert (Col D B E) by (forward_using lemma_collinearorder).
 assert (Col B C D) by (conclude_def Col ).
 assert (Col D B C) by (forward_using lemma_collinearorder).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B E C) by (conclude lemma_collinear4).
 assert (Col E C B) by (forward_using lemma_collinearorder).
 assert (Col A E C) by (conclude_def Col ).
 assert (Col E C A) by (forward_using lemma_collinearorder).
 assert (neq E C) by (forward_using lemma_betweennotequal).
 assert (Col C B A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
rename_H H;
let Tf:=fresh in
assert (Tf:exists H, (BetS D H E /\ BetS F H C)) by (conclude postulate_Pasch_inner);destruct Tf as [H];spliter.
assert (BetS C H F) by (conclude axiom_betweennesssymmetry).
assert (Out C F H) by (conclude lemma_ray4).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out C A A) by (conclude lemma_ray4).
assert (CongA B A C A C H) by (conclude lemma_equalangleshelper).
assert (CongA B A C A C F) by (conclude lemma_equalangleshelper).
assert (BetS E H D) by (conclude axiom_betweennesssymmetry).
assert (Out C A E) by (conclude lemma_ray5).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (neq C D) by (conclude lemma_inequalitysymmetric).
assert (Out C D D) by (conclude lemma_ray4).
assert (CongA B A C A C H) by (conclude lemma_equalanglestransitive).
assert (LtA B A C A C D) by (conclude_def LtA ).
assert (neq B C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists e, (BetS B e C /\ Cong e B e C)) by (conclude proposition_10);destruct Tf as [e];spliter.
assert (Col B e C) by (conclude_def Col ).
assert (~ eq A e).
 {
 intro.
 assert (BetS B A C) by (conclude cn_equalitysub).
 assert (Col B A C) by (conclude_def Col ).
 contradict.
 }
assert (neq e A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists f, (BetS A e f /\ Cong e f e A)) by (conclude lemma_extension);destruct Tf as [f];spliter.
assert (~ eq B C).
 {
 intro.
 assert (Col B A C) by (conclude_def Col ).
 contradict.
 }
assert (~ Col A e B).
 {
 intro.
 assert (Col B e C) by (conclude_def Col ).
 assert (Col e B A) by (forward_using lemma_collinearorder).
 assert (Col e B C) by (forward_using lemma_collinearorder).
 assert (neq B e) by (forward_using lemma_betweennotequal).
 assert (neq e B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 contradict.
 }
assert (CongA A e B C e f) by (conclude proposition_15a).
assert (~ Col B e A).
 {
 intro.
 assert (Col A e B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B e A A e B) by (conclude lemma_ABCequalsCBA).
assert (CongA B e A C e f) by (conclude lemma_equalanglestransitive).
assert (Cong A e f e) by (forward_using lemma_doublereverse).
assert (Cong e A e f) by (forward_using lemma_congruenceflip).
assert (~ Col e B A).
 {
 intro.
 assert (Col A e B) by (forward_using lemma_collinearorder).
 contradict.
 }
assert ((Cong B A C f /\ CongA e B A e C f /\ CongA e A B e f C)) by (conclude proposition_04).
assert (~ Col A B e).
 {
 intro.
 assert (Col e B A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Out B C e) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (~ Col A B C).
 {
 intro.
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
assert (CongA A B C A B e) by (conclude lemma_equalangleshelper).
assert (CongA A B e e B A) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C e B A) by (conclude lemma_equalanglestransitive).
assert (CongA A B C e C f) by (conclude lemma_equalanglestransitive).
assert (BetS C e B) by (conclude axiom_betweennesssymmetry).
assert (neq C e) by (forward_using lemma_betweennotequal).
assert (Out C e B) by (conclude lemma_ray4).
assert (eq f f) by (conclude cn_equalityreflexive).
assert (nCol e C f) by (conclude lemma_equalanglesNC).
assert (~ eq C f).
 {
 intro.
 assert (Col e C f) by (conclude_def Col ).
 contradict.
 }
assert (Out C f f) by (conclude lemma_ray4).
assert (~ Col e C f).
 {
 intro.
 assert (Col A e f) by (conclude_def Col ).
 assert (Col f e A) by (forward_using lemma_collinearorder).
 assert (Col f e C) by (forward_using lemma_collinearorder).
 assert (neq e f) by (forward_using lemma_betweennotequal).
 assert (neq f e) by (conclude lemma_inequalitysymmetric).
 assert (Col e A C) by (conclude lemma_collinear4).
 assert (Col e C A) by (forward_using lemma_collinearorder).
 assert (Col e C B) by (forward_using lemma_collinearorder).
 assert (neq e C) by (forward_using lemma_betweennotequal).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA e C f e C f) by (conclude lemma_equalanglesreflexive).
assert (CongA e C f B C f) by (conclude lemma_equalangleshelper).
assert (CongA A B C B C f) by (conclude lemma_equalanglestransitive).
assert (BetS G C A) by (conclude axiom_betweennesssymmetry).
assert (neq G C) by (forward_using lemma_betweennotequal).
assert (neq C G) by (conclude lemma_inequalitysymmetric).
assert (BetS f e A) by (conclude axiom_betweennesssymmetry).
assert (~ Col G A f).
 {
 intro.
 assert (Col f A G) by (forward_using lemma_collinearorder).
 assert (Col A e f) by (conclude_def Col ).
 assert (Col f A e) by (forward_using lemma_collinearorder).
 assert (neq A f) by (forward_using lemma_betweennotequal).
 assert (neq f A) by (conclude lemma_inequalitysymmetric).
 assert (Col A G e) by (conclude lemma_collinear4).
 assert (Col G A e) by (forward_using lemma_collinearorder).
 assert (Col A C G) by (conclude_def Col ).
 assert (Col G A C) by (forward_using lemma_collinearorder).
 assert (neq A G) by (forward_using lemma_betweennotequal).
 assert (neq G A) by (conclude lemma_inequalitysymmetric).
 assert (Col A e C) by (conclude lemma_collinear4).
 assert (Col e C A) by (forward_using lemma_collinearorder).
 assert (Col B e C) by (conclude_def Col ).
 assert (Col e C B) by (forward_using lemma_collinearorder).
 assert (neq e C) by (forward_using lemma_betweennotequal).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists h, (BetS G h e /\ BetS f h C)) by (conclude postulate_Pasch_inner);destruct Tf as [h];spliter.
assert (BetS C h f) by (conclude axiom_betweennesssymmetry).
assert (neq h C) by (forward_using lemma_betweennotequal).
assert (neq C h) by (conclude lemma_inequalitysymmetric).
assert (Out C h f) by (conclude lemma_ray4).
assert (Out C f h) by (conclude lemma_ray5).
assert (Out C B B) by (conclude lemma_ray4).
assert (CongA A B C B C h) by (conclude lemma_equalangleshelper).
assert (CongA A B C B C f) by (conclude lemma_equalangleshelper).
assert (BetS e h G) by (conclude axiom_betweennesssymmetry).
assert (BetS C e B) by (conclude axiom_betweennesssymmetry).
assert (Out C e B) by (conclude lemma_ray4).
assert (Out C B e) by (conclude lemma_ray5).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Out C G G) by (conclude lemma_ray4).
assert (CongA A B C B C h) by (conclude lemma_equalanglestransitive).
assert (LtA A B C B C G) by (conclude_def LtA ).
assert (~ Col G C B).
 {
 intro.
 assert (Col A C G) by (conclude_def Col ).
 assert (Col G C A) by (forward_using lemma_collinearorder).
 assert (neq C G) by (forward_using lemma_betweennotequal).
 assert (neq G C) by (conclude lemma_inequalitysymmetric).
 assert (Col C B A) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA G C B D C A) by (conclude proposition_15a).
assert (~ Col A C D).
 {
 intro.
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (Col B C D) by (conclude_def Col ).
 assert (Col D C B) by (forward_using lemma_collinearorder).
 assert (neq C D) by (forward_using lemma_betweennotequal).
 assert (neq D C) by (conclude lemma_inequalitysymmetric).
 assert (Col C A B) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA G C B B C G) by (conclude lemma_ABCequalsCBA).
assert (LtA A B C G C B) by (conclude lemma_angleorderrespectscongruence).
assert (~ Col D C A).
 {
 intro.
 assert (Col A C D) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA D C A A C D) by (conclude lemma_ABCequalsCBA).
assert (CongA G C B A C D) by (conclude lemma_equalanglestransitive).
assert (CongA A C D G C B) by (conclude lemma_equalanglessymmetric).
assert (LtA A B C A C D) by (conclude lemma_angleorderrespectscongruence).
assert (~ Col C B A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA C B A A B C) by (conclude lemma_ABCequalsCBA).
assert (LtA C B A A C D) by (conclude lemma_angleorderrespectscongruence2).
close.
Qed.

End Euclid.


