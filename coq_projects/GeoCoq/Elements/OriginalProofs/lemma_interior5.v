Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_interior5 : 
   forall A B C D a b c d, 
   BetS A B C -> BetS a b c -> Cong A B a b -> Cong B C b c -> Cong A D a d -> Cong C D c d ->
   Cong B D b d.
Proof.
intros.
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (neq A C) by (forward_using lemma_betweennotequal).
assert (~ eq C A).
 {
 intro.
 assert (eq A C) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS C A M /\ Cong A M B C)) by (conclude lemma_extension);destruct Tf as [M];spliter.
assert (Cong A M M A) by (conclude cn_equalityreverse).
assert (Cong M A A M) by (conclude lemma_congruencesymmetric).
assert (Cong M A B C) by (conclude lemma_congruencetransitive).
assert (neq b c) by (conclude axiom_nocollapse).
assert (neq a c) by (forward_using lemma_betweennotequal).
assert (~ eq c a).
 {
 intro.
 assert (eq a c) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists m, (BetS c a m /\ Cong a m b c)) by (conclude lemma_extension);destruct Tf as [m];spliter.
assert (Cong m a a m) by (conclude cn_equalityreverse).
assert (Cong m a b c) by (conclude lemma_congruencetransitive).
assert (Cong b c m a) by (conclude lemma_congruencesymmetric).
assert (Cong B C m a) by (conclude lemma_congruencetransitive).
assert (Cong M A m a) by (conclude lemma_congruencetransitive).
assert (Cong A C a c) by (conclude cn_sumofparts).
assert (Cong c a C A) by (forward_using lemma_doublereverse).
assert (Cong C A c a) by (conclude lemma_congruencesymmetric).
assert (BetS C B A) by (conclude axiom_betweennesssymmetry).
assert (BetS B A M) by (conclude lemma_3_6a).
assert (BetS c b a) by (conclude axiom_betweennesssymmetry).
assert (BetS b a m) by (conclude lemma_3_6a).
assert (Cong A M a m) by (forward_using lemma_congruenceflip).
assert (Cong D M d m) by (conclude axiom_5_line).
assert (BetS m a b) by (conclude axiom_betweennesssymmetry).
assert (BetS M A B) by (conclude axiom_betweennesssymmetry).
assert (Cong M D m d) by (forward_using lemma_congruenceflip).
assert (Cong D B d b) by (conclude axiom_5_line).
assert (Cong B D b d) by (forward_using lemma_congruenceflip).
close.
Qed.

End Euclid.

