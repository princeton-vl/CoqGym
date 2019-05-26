Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_layoff : 
   forall A B C D, 
   neq A B -> neq C D ->
   exists X, Out A B X /\ Cong A X C D.
Proof.
intros.
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS B A E /\ Cong A E C D)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (BetS E A B) by (conclude axiom_betweennesssymmetry).
assert (neq E A) by (forward_using lemma_betweennotequal).
assert (BetS E A B) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists P, (BetS E A P /\ Cong A P C D)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (Out A B P) by (conclude_def Out ).
close.
Qed.

End Euclid.


