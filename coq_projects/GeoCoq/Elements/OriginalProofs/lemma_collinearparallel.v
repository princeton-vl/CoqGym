Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearparallel : 
   forall A B C c d, 
   Par A B c d -> Col c d C -> neq C d ->
   Par A B C d.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists R a b p q, (neq A B /\ neq c d /\ Col A B a /\ Col A B b /\ neq a b /\ Col c d p /\ Col c d q /\ neq p q /\ ~ Meet A B c d /\ BetS a R q /\ BetS p R b)) by (conclude_def Par );destruct Tf as [R[a[b[p[q]]]]];spliter.
assert (neq d C) by (conclude lemma_inequalitysymmetric).
assert (Col d C p) by (conclude lemma_collinear4).
assert (Col C d p) by (forward_using lemma_collinearorder).
assert (Col d C q) by (conclude lemma_collinear4).
assert (Col C d q) by (forward_using lemma_collinearorder).
assert (~ Meet A B C d).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists E, (neq A B /\ neq C d /\ Col A B E /\ Col C d E)) by (conclude_def Meet );destruct Tf as [E];spliter.
 assert (Col C d c) by (forward_using lemma_collinearorder).
 assert (Col d E c) by (conclude lemma_collinear4).
 assert (Col c d E) by (forward_using lemma_collinearorder).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (Par A B C d) by (conclude_def Par ).
close.
Qed.

End Euclid.


