Require Export GeoCoq.Elements.OriginalProofs.lemma_ray.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ray1 : 
   forall A B P, 
   Out A B P ->
   (BetS A P B \/ eq B P \/ BetS A B P).
Proof.
intros.
assert (~ ~ (BetS A P B \/ eq B P \/ BetS A B P)).
 {
 intro.
 assert (neq P B) by (conclude lemma_inequalitysymmetric).
 assert (BetS A B P) by (conclude lemma_ray).
 contradict.
 }
close.
Qed.

End Euclid.


