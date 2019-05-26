Require Export GeoCoq.Elements.OriginalProofs.lemma_linereflectionisometry.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_10_12 : 
   forall A B C H, 
   Per A B C -> Per A B H -> Cong B C B H ->
   Cong A C A H.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
assert (neq B H) by (conclude_def Per ).
let Tf:=fresh in
assert (Tf:exists F, (BetS A B F /\ Cong A B F B /\ Cong A H F H /\ neq B H)) by (conclude_def Per );destruct Tf as [F];spliter.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (Cong D B A B) by (conclude lemma_congruencesymmetric).
assert (Cong D B F B) by (conclude lemma_congruencetransitive).
assert (Cong B F B D) by (forward_using lemma_doublereverse).
assert (eq F D) by (conclude lemma_extensionunique).
assert (Cong A H D H) by (conclude cn_equalitysub).
assert (Cong A C A H).
by cases on (eq C H \/ neq C H).
{
 assert (Cong A C A C) by (conclude cn_congruencereflexive).
 assert (Cong A C A H) by (conclude cn_equalitysub).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists M, (BetS C M H /\ Cong M C M H)) by (conclude proposition_10);destruct Tf as [M];spliter.
 assert (Cong C B H B) by (forward_using lemma_doublereverse).
 assert (Cong A C A H).
 by cases on (eq B M \/ neq B M).
 {
  assert (Per C B A) by (conclude lemma_8_2).
  assert (BetS C B H) by (conclude cn_equalitysub).
  assert (Cong B C B H) by (conclude cn_equalitysub).
  assert (Cong C B B H) by (forward_using lemma_congruenceflip).
  assert (Cong C A H A) by (conclude lemma_rightreverse).
  assert (Cong A C A H) by (forward_using lemma_congruenceflip).
  close.
  }
 {
  assert (neq M B) by (conclude lemma_inequalitysymmetric).
  assert (Cong C M H M) by (forward_using lemma_congruenceflip).
  assert (Per C M B) by (conclude_def Per ).
  assert (Per B M C) by (conclude lemma_8_2).
  assert (Cong C A C D) by (forward_using lemma_congruenceflip).
  assert (Cong H A H D) by (forward_using lemma_congruenceflip).
  assert (Cong C M C M) by (conclude cn_congruencereflexive).
  assert (Cong M H M H) by (conclude cn_congruencereflexive).
  assert (Cong M A M D) by (conclude lemma_interior5).
  assert (Cong A M D M) by (forward_using lemma_congruenceflip).
  assert (neq B M) by (conclude lemma_inequalitysymmetric).
  assert (Per A B M) by (conclude_def Per ).
  assert (Cong B A B D) by (forward_using lemma_congruenceflip).
  assert (Per M B A) by (conclude lemma_8_2).
  assert (Cong C A H D) by (conclude lemma_linereflectionisometry).
  assert (Cong A C D H) by (forward_using lemma_congruenceflip).
  assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
  assert (Cong B D B A) by (forward_using lemma_congruenceflip).
  assert (Cong A B B D) by (forward_using lemma_congruenceflip).
  assert (Cong A H D H) by (conclude lemma_rightreverse).
  assert (Cong D H A H) by (conclude lemma_congruencesymmetric).
  assert (Cong C A H D) by (forward_using lemma_congruenceflip).
  assert (Cong H D H A) by (forward_using lemma_congruenceflip).
  assert (Cong C A H A) by (conclude lemma_congruencetransitive).
  assert (Cong A C A H) by (forward_using lemma_congruenceflip).
  close.
  }
(** cases *)
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


