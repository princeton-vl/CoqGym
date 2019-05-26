Require Export GeoCoq.Elements.OriginalProofs.lemma_ray2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearitypreserved.
Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalanglesNC : 
   forall A B C a b c, 
   CongA A B C a b c ->
   nCol a b c.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists U V u v, (Out B A U /\ Out B C V /\ Out b a u /\ Out b c v /\ Cong B U b u /\ Cong B V b v /\ Cong U V u v /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
assert (neq b a) by (conclude lemma_ray2).
assert (neq a b) by (conclude lemma_inequalitysymmetric).
assert (Cong b u B U) by (conclude lemma_congruencesymmetric).
assert (Cong b v B V) by (conclude lemma_congruencesymmetric).
assert (Col B A U) by (conclude lemma_rayimpliescollinear).
assert (Col B C V) by (conclude lemma_rayimpliescollinear).
assert (Col b a u) by (conclude lemma_rayimpliescollinear).
assert (Col b c v) by (conclude lemma_rayimpliescollinear).
assert (Col a b u) by (forward_using lemma_collinearorder).
assert (~ Col a b c).
 {
 intro.
 assert (Col b u c) by (conclude lemma_collinear4).
 assert (Col c b u) by (forward_using lemma_collinearorder).
 assert (Col c b v) by (forward_using lemma_collinearorder).
 assert (neq b c) by (conclude lemma_ray2).
 assert (neq c b) by (conclude lemma_inequalitysymmetric).
 assert (Col b u v) by (conclude lemma_collinear4).
 assert (Cong u v U V) by (conclude lemma_congruencesymmetric).
 assert (Col B U V) by (conclude lemma_collinearitypreserved).
 assert (Col B U A) by (forward_using lemma_collinearorder).
 assert (neq B U) by (conclude lemma_raystrict).
 assert (Col U V A) by (conclude lemma_collinear4).
 assert (Col U V B) by (forward_using lemma_collinearorder).
 assert (Col V A B).
 by cases on (eq U V \/ neq U V).
 {
  assert (Col B A V) by (conclude cn_equalitysub).
  assert (Col V A B) by (forward_using lemma_collinearorder).
  close.
  }
 {
  assert (Col V A B) by (conclude lemma_collinear4).
  close.
  }
(** cases *)
 assert (Col V B A) by (forward_using lemma_collinearorder).
 assert (Col V B C) by (forward_using lemma_collinearorder).
 assert (neq B V) by (conclude lemma_raystrict).
 assert (neq V B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
close.
Qed.

End Euclid.
