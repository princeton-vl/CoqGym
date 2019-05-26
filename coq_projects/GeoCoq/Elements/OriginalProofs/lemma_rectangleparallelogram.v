Require Export GeoCoq.Elements.OriginalProofs.lemma_8_7.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_rectangleparallelogram : 
   forall A B C D, 
   RE A B C D ->
   PG A B C D.
Proof.
intros.
assert ((Per D A B /\ Per A B C /\ Per B C D /\ Per C D A /\ CR A C B D)) by (conclude_def RE ).
assert (nCol D A B) by (conclude lemma_rightangleNC).
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (nCol C D A) by (conclude lemma_rightangleNC).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (~ Meet A B C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq A B /\ neq C D /\ Col A B P /\ Col C D P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (~ eq A P).
  {
  intro.
  assert (Col C D A) by (conclude cn_equalitysub).
  contradict.
  }
 assert (~ eq D P).
  {
  intro.
  assert (Col A B D) by (conclude cn_equalitysub).
  assert (Col D A B) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Per B A D) by (conclude lemma_8_2).
 assert (Col B A P) by (forward_using lemma_collinearorder).
 assert (neq P A) by (conclude lemma_inequalitysymmetric).
 assert (Per P A D) by (conclude lemma_collinearright).
 assert (neq P D) by (conclude lemma_inequalitysymmetric).
 assert (Per P D A) by (conclude lemma_collinearright).
 assert (Per A D P) by (conclude lemma_8_2).
 assert (~ Per P A D) by (conclude lemma_8_7).
 contradict.
 }
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (neq D C) by (forward_using lemma_NCdistinct).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C D C) by (conclude_def Col ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col C D D) by (conclude_def Col ).
assert (BetS D M B) by (conclude axiom_betweennesssymmetry).
assert (Par A B C D) by (conclude_def Par ).
assert (~ Meet A D B C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq A D /\ neq B C /\ Col A D P /\ Col B C P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (~ eq A P).
  {
  intro.
  assert (Col B C A) by (conclude cn_equalitysub).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (~ eq B P).
  {
  intro.
  assert (Col A D B) by (conclude cn_equalitysub).
  assert (Col D A B) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (neq P A) by (conclude lemma_inequalitysymmetric).
 assert (Col D A P) by (forward_using lemma_collinearorder).
 assert (Per P A B) by (conclude lemma_collinearright).
 assert (Per C B A) by (conclude lemma_8_2).
 assert (Col C B P) by (forward_using lemma_collinearorder).
 assert (neq P B) by (conclude lemma_inequalitysymmetric).
 assert (Per P B A) by (conclude lemma_collinearright).
 assert (Per B A P) by (conclude lemma_8_2).
 assert (~ Per P B A) by (conclude lemma_8_7).
 contradict.
 }
assert (neq A D) by (forward_using lemma_NCdistinct).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col A D A) by (conclude_def Col ).
assert (Col A D D) by (conclude_def Col ).
assert (Col B C B) by (conclude_def Col ).
assert (Col B C C) by (conclude_def Col ).
assert (Par A D B C) by (conclude_def Par ).
assert (PG A B C D) by (conclude_def PG ).
close.
Qed.

End Euclid.


