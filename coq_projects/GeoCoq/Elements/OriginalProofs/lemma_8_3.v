Require Export GeoCoq.Elements.OriginalProofs.lemma_ray1.
Require Export GeoCoq.Elements.OriginalProofs.lemma_interior5.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_8_3 : 
   forall A B C D, 
   Per A B C -> Out B C D ->
   Per A B D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS A B E /\ Cong A B E B /\ Cong A C E C /\ neq B C)) by (conclude_def Per );destruct Tf as [E];spliter.
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (Cong C D C D) by (conclude cn_congruencereflexive).
assert (Cong B A B E) by (forward_using lemma_congruenceflip).
assert (Cong C A C E) by (forward_using lemma_congruenceflip).
assert ((BetS B D C \/ eq C D \/ BetS B C D)) by (conclude lemma_ray1).
assert (Per A B D).
by cases on (BetS B D C \/ eq C D \/ BetS B C D).
{
 assert (Cong B D B D) by (conclude cn_congruencereflexive).
 assert (Cong D C D C) by (conclude cn_congruencereflexive).
 assert (Cong D A D E) by (conclude lemma_interior5).
 assert (Cong A D E D) by (forward_using lemma_congruenceflip).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (Per A B D) by (conclude_def Per ).
 close.
 }
{
 assert (Per A B D) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong A D E D) by (conclude axiom_5_line).
 assert (neq B D) by (forward_using lemma_betweennotequal).
 assert (Per A B D) by (conclude_def Per ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


