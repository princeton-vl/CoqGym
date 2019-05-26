Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_3_7b.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_partnotequalwhole : 
   forall A B C, 
   BetS A B C ->
   ~ Cong A B A C.
Proof.
intros.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists D, BetS B A D) by (conclude postulate_Euclid2);destruct Tf as [D];spliter.
assert (BetS D A B) by (conclude axiom_betweennesssymmetry).
assert (BetS D A C) by (conclude lemma_3_7b).
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (~ Cong A B A C).
 {
 intro.
 assert (eq B C) by (conclude lemma_extensionunique).
 contradict.
 }
close.
Qed.

End Euclid.


