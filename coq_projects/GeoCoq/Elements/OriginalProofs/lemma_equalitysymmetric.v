Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_equalitysymmetric : 
   forall A B, 
   eq B A ->
   eq A B.
Proof.
intros.
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq A B) by (conclude cn_equalitytransitive).
close.
Qed.

End Euclid.
