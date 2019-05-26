Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsmeet.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29B.
Require Export GeoCoq.Elements.OriginalProofs.proposition_26A.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_34 : 
   forall A B C D, 
   PG A C D B ->
   Cong A B C D /\ Cong A C B D /\ CongA C A B B D C /\ CongA A B D D C A /\ Cong_3 C A B B D C.
Proof.
intros.
assert ((Par A C D B /\ Par A B C D)) by (conclude_def PG ).
assert (Par A C B D) by (forward_using lemma_parallelflip).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M D /\ BetS C M B)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
assert (BetS B M C) by (conclude axiom_betweennesssymmetry).
assert (Col B M C) by (conclude_def Col ).
assert (Col B C M) by (forward_using lemma_collinearorder).
assert (~ Meet A B C D) by (conclude_def Par ).
assert (neq A B) by (conclude_def Par ).
assert (neq C D) by (conclude_def Par ).
assert (~ Col B C A).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Col C D C) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (TS A B C D) by (conclude_def TS ).
assert (CongA A B C B C D) by (conclude proposition_29B).
assert (~ Col B C D).
 {
 intro.
 assert (Col C D B) by (forward_using lemma_collinearorder).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (Col A B B) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 assert (~ Meet A B C D) by (conclude_def Par ).
 contradict.
 }
assert (CongA B C D D C B) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C D C B) by (conclude lemma_equalanglestransitive).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (nCol C B A).
 {
 assert (nCol B C A) by auto.
 forward_using lemma_NCorder.
 }
assert (TS A C B D) by (conclude_def TS ).
assert (CongA A C B C B D) by (conclude proposition_29B).
assert (nCol A B C) by (forward_using lemma_NCorder).
assert (CongA B C A A C B) by (conclude lemma_ABCequalsCBA).
assert (CongA B C A C B D) by (conclude lemma_equalanglestransitive).
assert (Triangle A B C) by (conclude_def Triangle ).
assert (nCol D C B) by (conclude lemma_equalanglesNC).
assert (Triangle D C B) by (conclude_def Triangle ).
assert (Cong B C C B) by (conclude cn_equalityreverse).
assert ((Cong A B D C /\ Cong A C D B /\ CongA B A C C D B)) by (conclude proposition_26A).
assert (Cong A B C D) by (forward_using lemma_congruenceflip).
assert (Cong A C B D) by (forward_using lemma_congruenceflip).
assert (Cong C A B D) by (forward_using lemma_congruenceflip).
assert (Cong C B B C) by (conclude cn_equalityreverse).
assert (Cong_3 C A B B D C) by (conclude_def Cong_3 ).
assert (CongA C A B B D C) by (conclude lemma_equalanglesflip).
assert (Cong A D D A) by (conclude cn_equalityreverse).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (neq A C) by (forward_using lemma_angledistinct).
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (neq C D) by (forward_using lemma_angledistinct).
assert (neq B A) by (forward_using lemma_angledistinct).
assert (neq D B) by (forward_using lemma_angledistinct).
assert (neq B D) by (conclude lemma_inequalitysymmetric).
assert (Out C A A) by (conclude lemma_ray4).
assert (Out C D D) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B D D) by (conclude lemma_ray4).
assert (Cong B A C D) by (forward_using lemma_congruenceflip).
assert (Cong C A B D) by (forward_using lemma_congruenceflip).
assert (Cong B D C A) by (conclude lemma_congruencesymmetric).
assert (~ Col A B D).
 {
 intro.
 assert (eq D D) by (conclude cn_equalityreflexive).
 assert (Col C D D) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (CongA A B D D C A) by (conclude_def CongA ).
close.
Qed.

End Euclid.


