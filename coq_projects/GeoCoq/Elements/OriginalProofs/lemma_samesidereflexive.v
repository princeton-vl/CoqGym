Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidereflexive : 
   forall A B P, 
   nCol A B P ->
   OS P P A B.
Proof.
intros.
assert (eq A A) by (conclude cn_equalityreflexive).
assert (~ eq P A).
 {
 intro.
 assert (Col A B A) by (conclude_def Col ).
 assert (Col A B P) by (conclude cn_equalitysub).
 contradict.
 }
assert (neq A P) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists C, (BetS P A C /\ Cong A C A P)) by (conclude lemma_extension);destruct Tf as [C];spliter.
assert (Col A B A) by (conclude_def Col ).
assert (OS P P A B) by (conclude_def OS ).
close.
Qed.

End Euclid.


