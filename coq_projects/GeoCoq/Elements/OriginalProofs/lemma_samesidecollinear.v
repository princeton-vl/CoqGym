Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidecollinear : 
   forall A B C P Q, 
   OS P Q A B -> Col A B C -> neq A C ->
   OS P Q A C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists p q r, (Col A B p /\ Col A B q /\ BetS P p r /\ BetS Q q r /\ nCol A B P /\ nCol A B Q)) by (conclude_def OS );destruct Tf as [p[q[r]]];spliter.
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (nCol A C P) by (conclude lemma_NChelper).
assert (nCol A C Q) by (conclude lemma_NChelper).
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col B A C) by (forward_using lemma_collinearorder).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Col A C p) by (conclude lemma_collinear4).
assert (Col B A q) by (forward_using lemma_collinearorder).
assert (Col A C q) by (conclude lemma_collinear4).
assert (OS P Q A C) by (conclude_def OS ).
close.
Qed.

End Euclid.


