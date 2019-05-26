Require Export GeoCoq.Elements.OriginalProofs.proposition_29B.
Require Export GeoCoq.Elements.OriginalProofs.proposition_27B.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33 : 
   forall A B C D M, 
   Par A B C D -> Cong A B C D -> BetS A M D -> BetS B M C ->
   Par A C B D /\ Cong A C B D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d m, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a m d /\ BetS c m b)) by (conclude_def Par );destruct Tf as [a[b[c[d[m]]]]];spliter.
assert (Col B M C) by (conclude_def Col ).
assert (Col B C M) by (forward_using lemma_collinearorder).
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
 contradict.
 }
assert (CongA B C D D C B) by (conclude lemma_ABCequalsCBA).
assert (CongA A B C D C B) by (conclude lemma_equalanglestransitive).
assert (Cong B C B C) by (conclude cn_congruencereflexive).
assert (nCol A B C) by (assert (nCol B C A) by auto;
 (forward_using lemma_NCorder)). 
assert (Cong B A C D) by (forward_using lemma_congruenceflip).
assert (Cong B C C B) by (forward_using lemma_congruenceflip).
assert ((Cong A C D B /\ CongA B A C C D B /\ CongA B C A C B D)) by (conclude proposition_04).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (CongA A C B B C A) by (conclude lemma_ABCequalsCBA).
assert (CongA A C B C B D) by (conclude lemma_equalanglestransitive).
assert (Cong A C B D) by (forward_using lemma_congruenceflip).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (nCol C B A) by (forward_using lemma_NCorder).
assert (TS A C B D) by (conclude_def TS ).
assert (Par A C B D) by (conclude proposition_27B).
close.
Qed.

End Euclid.


