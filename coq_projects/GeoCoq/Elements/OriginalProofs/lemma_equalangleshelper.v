Require Export GeoCoq.Elements.OriginalProofs.lemma_ray3.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equalangleshelper : 
   forall A B C a b c p q, 
   CongA A B C a b c -> Out b a p -> Out b c q ->
   CongA A B C p b q.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists U V u v, (Out B A U /\ Out B C V /\ Out b a u /\ Out b c v /\ Cong B U b u /\ Cong B V b v /\ Cong U V u v /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
assert (Out b p u) by (conclude lemma_ray3).
assert (Out b q v) by (conclude lemma_ray3).
assert (CongA A B C p b q) by (conclude_def CongA ).
close.
Qed.

End Euclid.


