Require Export GeoCoq.Elements.OriginalProofs.lemma_betweennotequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_ondiameter : 
   forall D F K M N P Q, 
   CI K F P Q -> Cong F D P Q -> Cong F M P Q -> BetS D F M -> BetS D N M ->
   InCirc N K.
Proof.
intros.
assert (neq D F) by (forward_using lemma_betweennotequal).
assert (neq F D) by (conclude lemma_inequalitysymmetric).
assert (~ ~ (BetS D N F \/ BetS F N M \/ eq F N)).
 {
 intro.
 assert (~ BetS D F N).
  {
  intro.
  assert (BetS F N M) by (conclude lemma_3_6a).
  contradict.
  }
 assert (eq F N) by (conclude axiom_connectivity).
 contradict.
 }
assert (Cong F N F N) by (conclude cn_congruencereflexive).
assert (InCirc N K).
by cases on (BetS D N F \/ BetS F N M \/ eq F N).
{
 assert (BetS F N D) by (conclude axiom_betweennesssymmetry).
 assert (InCirc N K) by (conclude_def InCirc ).
 close.
 }
{
 assert (InCirc N K) by (conclude_def InCirc ).
 close.
 }
{
 assert (eq N F) by (conclude lemma_equalitysymmetric).
 assert (InCirc N K) by (conclude_def InCirc ).
 close.
 }
(* cases *)
close.
Unshelve.
exact M.
exact M.
Qed.

End Euclid.
