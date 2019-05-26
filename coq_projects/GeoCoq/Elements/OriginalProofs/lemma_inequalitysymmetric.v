Require Export GeoCoq.Elements.OriginalProofs.lemma_equalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_inequalitysymmetric : 
   forall A B, 
   neq A B ->
   neq B A.
Proof.
intros.
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 contradict.
 }
close.
Qed.

End Euclid.
