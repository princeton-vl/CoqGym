Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_localextension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_doublereverse.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_differenceofparts : 
   forall A B C a b c, 
   Cong A B a b -> Cong A C a c -> BetS A B C -> BetS a b c ->
   Cong B C b c.
Proof.
intros.
assert (Cong B C b c).
by cases on (eq B A \/ neq B A).
{
 assert (Cong A A a b) by (conclude cn_equalitysub).
 assert (Cong a b A A) by (conclude lemma_congruencesymmetric).
 assert (~ neq a b).
  {
  intro.
  assert (neq A A) by (conclude axiom_nocollapse).
  assert (eq A A) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (Cong A C A C) by (conclude cn_congruencereflexive).
 assert (Cong B C A C) by (conclude cn_equalitysub).
 assert (Cong B C a c) by (conclude lemma_congruencetransitive).
 assert (Cong b c b c) by (conclude cn_congruencereflexive).
 assert (Cong b c a c) by (conclude cn_equalitysub).
 assert (Cong a c b c) by (conclude lemma_congruencesymmetric).
 assert (Cong B C b c) by (conclude lemma_congruencetransitive).
 close.
 }
{
 assert (~ eq C A).
  {
  intro.
  assert (BetS A B A) by (conclude cn_equalitysub).
  assert (~ BetS A B A) by (conclude axiom_betweennessidentity).
  contradict.
  }
 assert (neq A C) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists E, (BetS C A E /\ Cong A E A C)) by (conclude lemma_localextension);destruct Tf as [E];spliter.
 assert (neq A C) by (conclude lemma_inequalitysymmetric).
 assert (neq a c) by (conclude axiom_nocollapse).
 assert (neq c a) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists e, (BetS c a e /\ Cong a e a c)) by (conclude lemma_localextension);destruct Tf as [e];spliter.
 assert (Cong E A A E) by (conclude cn_equalityreverse).
 assert (Cong E A A C) by (conclude lemma_congruencetransitive).
 assert (Cong E A a c) by (conclude lemma_congruencetransitive).
 assert (Cong e a a e) by (conclude cn_equalityreverse).
 assert (Cong e a a c) by (conclude lemma_congruencetransitive).
 assert (Cong a c e a) by (conclude lemma_congruencesymmetric).
 assert (Cong E A a c) by (conclude lemma_congruencetransitive).
 assert (Cong E A e a) by (conclude lemma_congruencetransitive).
 assert (BetS E A C) by (conclude axiom_betweennesssymmetry).
 assert (BetS e a c) by (conclude axiom_betweennesssymmetry).
 assert (Cong E C e c) by (conclude cn_sumofparts).
 assert (BetS E A B) by (conclude axiom_innertransitivity).
 assert (BetS e a b) by (conclude axiom_innertransitivity).
 assert (Cong C B c b) by (conclude axiom_5_line).
 assert (Cong b c B C) by (forward_using lemma_doublereverse).
 assert (Cong B C b c) by (conclude lemma_congruencesymmetric).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.
