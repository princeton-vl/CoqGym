Require Export GeoCoq.Elements.OriginalProofs.lemma_diagonalsbisect.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_trapezoiddiagonals : 
   forall A B C D E, 
   PG A B C D -> BetS A E D ->
   exists X, BetS B X D /\ BetS C X E.
Proof.
intros.
assert (Par A B C D) by (conclude_def PG ).
assert (Par A D B C) by (conclude_def PG ).
assert (~ Meet A B C D) by (conclude_def Par ).
assert (neq A B) by (conclude_def Par ).
assert (neq C D) by (conclude_def Par ).
let Tf:=fresh in
assert (Tf:exists M, (Midpoint A M C /\ Midpoint B M D)) by (conclude lemma_diagonalsbisect);destruct Tf as [M];spliter.
assert (BetS A M C) by (conclude_def Midpoint ).
assert (Cong A M M C) by (conclude_def Midpoint ).
assert (BetS B M D) by (conclude_def Midpoint ).
assert (Cong B M M D) by (conclude_def Midpoint ).
assert (Cong B M D M) by (forward_using lemma_congruenceflip).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (~ Col B D C).
 {
 intro.
 assert (Col C D B) by (forward_using lemma_collinearorder).
 assert (Col A B B) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (Cong M A M C) by (forward_using lemma_congruenceflip).
let Tf:=fresh in
assert (Tf:exists P, (BetS B E P /\ BetS C D P)) by (conclude postulate_Euclid5);destruct Tf as [P];spliter.
assert (~ Col B P C).
 {
 intro.
 assert (Col P C B) by (forward_using lemma_collinearorder).
 assert (Col C D P) by (conclude_def Col ).
 assert (Col P C D) by (forward_using lemma_collinearorder).
 assert (neq C P) by (forward_using lemma_betweennotequal).
 assert (neq P C) by (conclude lemma_inequalitysymmetric).
 assert (Col C B D) by (conclude lemma_collinear4).
 assert (Col C D B) by (forward_using lemma_collinearorder).
 assert (Col A B B) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists H', (BetS B H' D /\ BetS C H' E)) by (conclude postulate_Pasch_inner);destruct Tf as [H'];spliter.
close.
Qed.

End Euclid.

