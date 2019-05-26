Require Export GeoCoq.Elements.OriginalProofs.lemma_3_6a.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_betweennotequal : 
   forall A B C, 
   BetS A B C ->
   neq B C /\ neq A B /\ neq A C.
Proof.
intros.
assert (~ eq B C).
 {
 intro.
 assert (BetS A C B) by (conclude cn_equalitysub).
 assert (BetS B C B) by (conclude lemma_3_6a).
 assert (~ BetS B C B) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (~ eq A B).
 {
 intro.
 assert (BetS B A C) by (conclude cn_equalitysub).
 assert (BetS A B A) by (conclude axiom_innertransitivity).
 assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (BetS A B A) by (conclude cn_equalitysub).
 assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
 contradict.
 }
close.
Qed.

End Euclid.


