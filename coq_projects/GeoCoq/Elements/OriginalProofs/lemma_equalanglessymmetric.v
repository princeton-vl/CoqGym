Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearitypreserved.
Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglessymmetric : 
   forall A B C a b c, 
   CongA A B C a b c ->
   CongA a b c A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists U V u v, (Out B A U /\ Out B C V /\ Out b a u /\ Out b c v /\ Cong B U b u /\ Cong B V b v /\ Cong U V u v /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
assert (Cong b u B U) by (conclude lemma_congruencesymmetric).
assert (Cong b v B V) by (conclude lemma_congruencesymmetric).
assert (Cong v u V U) by (forward_using lemma_doublereverse).
assert (~ Col a b c).
 {
 intro.
 assert (Col b a u) by (conclude lemma_rayimpliescollinear).
 assert (Col b c v) by (conclude lemma_rayimpliescollinear).
 assert (Col B A U) by (conclude lemma_rayimpliescollinear).
 assert (Col B C V) by (conclude lemma_rayimpliescollinear).
 assert (Col a b u) by (forward_using lemma_collinearorder).
 assert (neq b a) by (conclude lemma_ray2).
 assert (neq a b) by (conclude lemma_inequalitysymmetric).
 assert (Col b u c) by (conclude lemma_collinear4).
 assert (Col c b u) by (forward_using lemma_collinearorder).
 assert (Col c b v) by (forward_using lemma_collinearorder).
 assert (neq b c) by (conclude lemma_ray2).
 assert (neq c b) by (conclude lemma_inequalitysymmetric).
 assert (Col b u v) by (conclude lemma_collinear4).
 assert (Cong u v U V) by (conclude lemma_congruencesymmetric).
 assert (Col B U V) by (conclude lemma_collinearitypreserved).
 assert (Col U B V) by (forward_using lemma_collinearorder).
 assert (Col U B A) by (forward_using lemma_collinearorder).
 assert (neq B U) by (conclude lemma_raystrict).
 assert (neq U B) by (conclude lemma_inequalitysymmetric).
 assert (Col B V A) by (conclude lemma_collinear4).
 assert (Col V B A) by (forward_using lemma_collinearorder).
 assert (Col V B C) by (forward_using lemma_collinearorder).
 assert (neq B V) by (conclude lemma_raystrict).
 assert (neq V B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Cong u v U V) by (conclude lemma_congruencesymmetric).
assert (CongA a b c A B C) by (conclude_def CongA ).
close.
Qed.

End Euclid.


