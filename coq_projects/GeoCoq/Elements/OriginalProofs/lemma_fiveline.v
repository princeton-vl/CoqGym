Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennesspreserved.
Require Export GeoCoq.Elements.OriginalProofs.lemma_interior5.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_fiveline : 
   forall A B C D a b c d, 
   Col A B C -> Cong A B a b -> Cong B C b c -> Cong A D a d -> Cong C D c d -> Cong A C a c -> neq A C ->
   Cong B D b d.
Proof.
intros.
assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
assert (Cong B D b d).
by cases on (eq A B \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B).
{
 assert (Cong B B a b) by (conclude cn_equalitysub).
 assert (Cong a b B B) by (conclude lemma_congruencesymmetric).
 assert (~ neq a b).
  {
  intro.
  assert (neq B B) by (conclude axiom_nocollapse).
  assert (eq B B) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (Cong B D a d) by (conclude cn_equalitysub).
 assert (Cong B D b d) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong B B b c) by (conclude cn_equalitysub).
 assert (Cong b c B B) by (conclude lemma_congruencesymmetric).
 assert (~ neq b c).
  {
  intro.
  assert (neq B B) by (conclude axiom_nocollapse).
  assert (eq B B) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (Cong B D c d) by (conclude cn_equalitysub).
 assert (Cong B D b d) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS C A B) by (conclude axiom_betweennesssymmetry).
 assert (Cong C A c a) by (forward_using lemma_congruenceflip).
 assert (Cong C B c b) by (forward_using lemma_congruenceflip).
 assert (BetS c a b) by (conclude lemma_betweennesspreserved).
 assert (Cong D B d b) by (conclude axiom_5_line).
 assert (Cong B D b d) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (BetS a b c) by (conclude lemma_betweennesspreserved).
 assert (Cong B D b d) by (conclude lemma_interior5).
 close.
 }
{
 assert (Cong C B c b) by (forward_using lemma_congruenceflip).
 assert (BetS a c b) by (conclude lemma_betweennesspreserved).
 assert (Cong D B d b) by (conclude axiom_5_line).
 assert (Cong B D b d) by (forward_using lemma_congruenceflip).
 close.
 }
(* cases *)
close.
Qed.

End Euclid.
