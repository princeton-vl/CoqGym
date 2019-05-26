Require Export GeoCoq.Elements.OriginalProofs.lemma_outerconnectivity.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.


Lemma lemma_ray3 : 
   forall B C D V, 
   Out B C D -> Out B C V ->
   Out B D V.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS E B D /\ BetS E B C)) by (conclude_def Out );destruct Tf as [E];spliter.
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS H B V /\ BetS H B C)) by (conclude_def Out );destruct Tf as [H];spliter.
assert (~ ~ BetS E B V).
 {
 intro.
 assert (~ BetS B E H).
  {
  intro.
  assert (BetS H E B) by (conclude axiom_betweennesssymmetry).
  assert (BetS E B V) by (conclude lemma_3_6a).
  contradict.
  }
 assert (~ BetS B H E).
  {
  intro.
  assert (BetS E H B) by (conclude axiom_betweennesssymmetry).
  assert (BetS E B V) by (conclude lemma_3_7a).
  contradict.
  }
 assert (BetS C B E) by (conclude axiom_betweennesssymmetry).
 assert (BetS C B H) by (conclude axiom_betweennesssymmetry).
 assert (eq H E) by (conclude lemma_outerconnectivity).
 assert (BetS E B V) by (conclude cn_equalitysub).
 contradict.
 }
assert (Out B D V) by (conclude_def Out ).
close.
Qed.

End Euclid.


