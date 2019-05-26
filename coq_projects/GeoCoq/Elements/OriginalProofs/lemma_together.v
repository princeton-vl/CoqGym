Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_together : 
   forall A B C D F G P Q a b c, 
   TG A a B b C c -> Cong D F A a -> Cong F G B b -> BetS D F G -> Cong P Q C c ->
   Lt P Q D G /\ neq A a /\ neq B b /\ neq C c.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists R, (BetS A a R /\ Cong a R B b /\ Lt C c A R)) by (conclude_def TG );destruct Tf as [R];spliter.
assert (Cong A a A a) by (conclude cn_congruencereflexive).
assert (Cong B b a R) by (conclude lemma_congruencesymmetric).
assert (Cong F G a R) by (conclude lemma_congruencetransitive).
assert (Cong D G A R) by (conclude cn_sumofparts).
assert (Cong A R D G) by (conclude lemma_congruencesymmetric).
assert (Cong C c P Q) by (conclude lemma_congruencesymmetric).
assert (Lt P Q A R) by (conclude lemma_lessthancongruence2).
assert (Lt P Q D G) by (conclude lemma_lessthancongruence).
assert (neq A a) by (forward_using lemma_betweennotequal).
assert (neq a R) by (forward_using lemma_betweennotequal).
assert (neq B b) by (conclude axiom_nocollapse).
let Tf:=fresh in
assert (Tf:exists S, (BetS A S R /\ Cong A S C c)) by (conclude_def Lt );destruct Tf as [S];spliter.
assert (neq A S) by (forward_using lemma_betweennotequal).
assert (neq C c) by (conclude axiom_nocollapse).
close.
Qed.

End Euclid.


