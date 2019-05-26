Require Export GeoCoq.Elements.OriginalProofs.proposition_23B.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_23C : 
   forall A B C D E P, 
   neq A B -> nCol D C E -> nCol A B P ->
   exists X Y, Out A B Y /\ CongA X A Y D C E /\ OS X P A B.
Proof.
intros.
assert (~ eq P A).
 {
 intro.
 assert (eq A P) by (conclude lemma_equalitysymmetric).
 assert (Col A B P) by (conclude_def Col ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists Q, (BetS P A Q /\ Cong A Q P A)) by (conclude lemma_extension);destruct Tf as [Q];spliter.
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (~ Col A B Q).
 {
 intro.
 assert (Col P A Q) by (conclude_def Col ).
 assert (Col Q A B) by (forward_using lemma_collinearorder).
 assert (Col Q A P) by (forward_using lemma_collinearorder).
 assert (neq A Q) by (forward_using lemma_betweennotequal).
 assert (neq Q A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B P) by (conclude lemma_collinear4).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists F G, (Out A B G /\ CongA F A G D C E /\ TS F A B Q)) by (conclude proposition_23B);destruct Tf as [F[G]];spliter.
let Tf:=fresh in
assert (Tf:exists J, (BetS F J Q /\ Col A B J /\ nCol A B F)) by (conclude_def TS );destruct Tf as [J];spliter.
assert (OS F P A B) by (conclude_def OS ).
close.
Qed.

End Euclid.


