Require Export GeoCoq.Elements.OriginalProofs.lemma_8_2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_3.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_collinearright : 
   forall A B C D, 
   Per A B D -> Col A B C -> neq C B ->
   Per C B D.
Proof.
intros.
assert ((eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B)) by (conclude_def Col ).
assert (nCol A B D) by (conclude lemma_rightangleNC).
assert (~ eq A B).
 {
 intro.
 assert (nCol A A D) by (conclude cn_equalitysub).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col D A A) by (conclude_def Col ).
 assert (Col A A D) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Per D B A) by (conclude lemma_8_2).
assert (Per D B C).
by cases on (eq A B \/ eq A C \/ eq B C \/ BetS B A C \/ BetS A B C \/ BetS A C B).
{
 assert (~ ~ Per D B C).
  {
  intro.
  assert (Col A B D) by (conclude_def Col ).
  contradict.
  }
 close.
 }
{
 assert (Per D B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (~ ~ Per D B C).
  {
  intro.
  assert (eq C B) by (conclude lemma_equalitysymmetric).
  contradict.
  }
 close.
 }
{
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Out B A C) by (conclude lemma_ray4).
 assert (Per D B C) by (conclude lemma_8_3).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists E, (BetS A B E /\ Cong A B E B /\ Cong A D E D /\ neq B D)) by (conclude_def Per );destruct Tf as [E];spliter.
 assert (BetS E B A) by (conclude axiom_betweennesssymmetry).
 assert (Cong E B A B) by (conclude lemma_congruencesymmetric).
 assert (Cong E D A D) by (conclude lemma_congruencesymmetric).
 assert (Per E B D) by (conclude_def Per ).
 assert (Per D B E) by (conclude lemma_8_2).
 assert (BetS A B E) by (conclude axiom_betweennesssymmetry).
 assert (Out B E C) by (conclude_def Out ).
 assert (Per D B C) by (conclude lemma_8_3).
 close.
 }
{
 assert (BetS B C A) by (conclude axiom_betweennesssymmetry).
 assert (neq C B) by (forward_using lemma_betweennotequal).
 assert (neq B C) by (conclude lemma_inequalitysymmetric).
 assert (Out B C A) by (conclude lemma_ray4).
 assert (Per D B A) by (conclude lemma_8_2).
 assert (Out B A C) by (conclude lemma_ray5).
 assert (Per D B C) by (conclude lemma_8_3).
 close.
 }
(** cases *)
assert (Per C B D) by (conclude lemma_8_2).
close.
Qed.

End Euclid.


