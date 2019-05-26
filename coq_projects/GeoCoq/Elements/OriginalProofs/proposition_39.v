Require Export GeoCoq.Elements.OriginalProofs.lemma_samesideflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_39A.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_39 : 
   forall A B C D, 
   Triangle A B C -> Triangle D B C -> OS A D B C -> ET A B C D B C -> neq A D ->
   Par A D B C.
Proof.
intros.
assert (OS D A B C) by (forward_using lemma_samesidesymmetric).
assert (OS A D C B) by (conclude lemma_samesideflip).
assert (OS D A C B) by (forward_using lemma_samesidesymmetric).
assert (nCol A B C) by (conclude_def Triangle ).
assert (nCol D B C) by (conclude_def Triangle ).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq B D) by (forward_using lemma_NCdistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C A) by (forward_using lemma_NCdistinct).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B D D) by (conclude lemma_ray4).
assert (Out C B B) by (conclude lemma_ray4).
assert (Out C A A) by (conclude lemma_ray4).
assert (Out C D D) by (conclude lemma_ray4).
assert (~ ~ Par A D B C).
 {
 intro.
 assert (~ LtA C B D C B A).
  {
  intro.
  let Tf:=fresh in
  assert (Tf:exists M, (BetS A M C /\ Out B D M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
  assert (Par A D B C) by (conclude proposition_39A).
  contradict.
  }
 assert (~ LtA C B A C B D).
  {
  intro.
  let Tf:=fresh in
  assert (Tf:exists M, (BetS D M C /\ Out B A M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
  assert (ET D B C A B C) by (conclude axiom_ETsymmetric).
  assert (Par D A B C) by (conclude proposition_39A).
  assert (Par A D B C) by (forward_using lemma_parallelflip).
  contradict.
  }
 assert (~ ~ CongA C B D C B A).
  {
  intro.
  assert (nCol C B A) by (forward_using lemma_NCorder).
  assert (nCol C B D) by (forward_using lemma_NCorder).
  assert (LtA C B D C B A) by (conclude lemma_angletrichotomy2).
  contradict.
  }
 assert (nCol A C B) by (forward_using lemma_NCorder).
 assert (Triangle A C B) by (conclude_def Triangle ).
 assert (nCol D C B) by (forward_using lemma_NCorder).
 assert (Triangle D C B) by (conclude_def Triangle ).
 assert (OS A D C B) by (conclude lemma_samesideflip).
 assert (ET A B C D C B) by (forward_using axiom_ETpermutation).
 assert (ET D C B A B C) by (conclude axiom_ETsymmetric).
 assert (ET D C B A C B) by (forward_using axiom_ETpermutation).
 assert (ET A C B D C B) by (conclude axiom_ETsymmetric).
 assert (~ LtA B C D B C A).
  {
  intro.
  let Tf:=fresh in
  assert (Tf:exists M, (BetS A M B /\ Out C D M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
  assert (Par A D C B) by (conclude proposition_39A).
  assert (Par A D B C) by (forward_using lemma_parallelflip).
  contradict.
  }
 assert (~ LtA B C A B C D).
  {
  intro.
  let Tf:=fresh in
  assert (Tf:exists M, (BetS D M B /\ Out C A M)) by (conclude lemma_crossbar2);destruct Tf as [M];spliter.
  assert (ET D C B A C B) by (conclude axiom_ETsymmetric).
  assert (Par D A C B) by (conclude proposition_39A).
  assert (Par A D B C) by (forward_using lemma_parallelflip).
  contradict.
  }
 assert (~ ~ CongA B C D B C A).
  {
  intro.
  assert (nCol B C A) by (forward_using lemma_NCorder).
  assert (nCol B C D) by (forward_using lemma_NCorder).
  assert (LtA B C D B C A) by (conclude lemma_angletrichotomy2).
  contradict.
  }
 assert (CongA B C A B C D) by (conclude lemma_equalanglessymmetric).
 assert (Cong B C B C) by (conclude cn_congruencereflexive).
 assert (CongA D B C A B C) by (conclude lemma_equalanglesflip).
 assert (CongA A B C D B C) by (conclude lemma_equalanglessymmetric).
 assert ((Cong A B D B /\ Cong A C D C /\ CongA B A C B D C)) by (conclude proposition_26A).
 assert (neq B C) by (forward_using lemma_NCdistinct).
 assert (eq A D) by (conclude proposition_07).
 contradict.
 }
close.
Qed.

End Euclid.


