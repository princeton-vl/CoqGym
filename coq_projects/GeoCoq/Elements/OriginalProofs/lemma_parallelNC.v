Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_parallelNC : 
   forall A B C D, 
   Par A B C D ->
   nCol A B C /\ nCol A C D /\ nCol B C D /\ nCol A B D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M a b c d, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a M d /\ BetS c M b)) by (conclude_def Par );destruct Tf as [M[a[b[c[d]]]]];spliter.
assert (~ Col A C D).
 {
 intro.
 assert (Col C D A) by (forward_using lemma_collinearorder).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col A B C).
 {
 intro.
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Col C D C) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col B C D).
 {
 intro.
 assert (Col C D B) by (forward_using lemma_collinearorder).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (Col A B B) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col A B D).
 {
 intro.
 assert (eq D D) by (conclude cn_equalityreflexive).
 assert (Col C D D) by (conclude_def Col ).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
close.
Qed.

End Euclid.


