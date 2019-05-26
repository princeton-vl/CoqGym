Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_paralleldef2A : 
   forall A B C D, 
   TP A B C D ->
   Par A B C D.
Proof.
intros.
assert ((neq A B /\ neq C D /\ ~ Meet A B C D /\ OS C D A B)) by (conclude_def TP ).
let Tf:=fresh in
assert (Tf:exists a b e, (Col A B a /\ Col A B b /\ BetS C a e /\ BetS D b e /\ nCol A B C /\ nCol A B D)) by (conclude_def OS );destruct Tf as [a[b[e]]];spliter.
assert (Col C a e) by (conclude_def Col ).
assert (Col D b e) by (conclude_def Col ).
assert (neq a e) by (forward_using lemma_betweennotequal).
assert (neq e a) by (conclude lemma_inequalitysymmetric).
assert (neq C e) by (forward_using lemma_betweennotequal).
assert (neq e C) by (conclude lemma_inequalitysymmetric).
assert (neq D e) by (forward_using lemma_betweennotequal).
assert (neq e D) by (conclude lemma_inequalitysymmetric).
assert (~ eq a b).
 {
 intro.
 assert (Col D a e) by (conclude cn_equalitysub).
 assert (Col a e C) by (forward_using lemma_collinearorder).
 assert (Col a e D) by (forward_using lemma_collinearorder).
 assert (Col e C D) by (conclude lemma_collinear4).
 assert (Col e D C) by (forward_using lemma_collinearorder).
 assert (Col e D b) by (forward_using lemma_collinearorder).
 assert (Col D C b) by (conclude lemma_collinear4).
 assert (Col C D b) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col C e D).
 {
 intro.
 assert (Col C e a) by (forward_using lemma_collinearorder).
 assert (Col e D a) by (conclude lemma_collinear4).
 assert (Col e D b) by (forward_using lemma_collinearorder).
 assert (Col D a b) by (conclude lemma_collinear4).
 assert (Col e D C) by (forward_using lemma_collinearorder).
 assert (Col D C a) by (conclude lemma_collinear4).
 assert (Col C D a) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS C M b /\ BetS D M a)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
assert (BetS a M D) by (conclude axiom_betweennesssymmetry).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C D C) by (conclude_def Col ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col C D D) by (conclude_def Col ).
assert (Par A B C D) by (conclude_def Par ).
close.
Qed.

End Euclid.


