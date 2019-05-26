Require Export GeoCoq.Elements.OriginalProofs.lemma_26helper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy1.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_26B : 
   forall A B C D E F, 
   Triangle A B C -> Triangle D E F -> CongA A B C D E F -> CongA B C A E F D -> Cong A B D E ->
   Cong B C E F /\ Cong A C D F /\ CongA B A C E D F.
Proof.
intros.
assert (~ Lt E F B C) by (conclude lemma_26helper).
assert (CongA D E F A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA E F D B C A) by (conclude lemma_equalanglessymmetric).
assert (Cong D E A B) by (conclude lemma_congruencesymmetric).
assert (~ Lt B C E F) by (conclude lemma_26helper).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (nCol A B C) by (conclude_def Triangle ).
 contradict.
 }
assert (~ eq E F).
 {
 intro.
 assert (Col D E F) by (conclude_def Col ).
 assert (nCol D E F) by (conclude_def Triangle ).
 contradict.
 }
assert (Cong B C E F) by (conclude lemma_trichotomy1).
assert (Cong B A E D) by (forward_using lemma_congruenceflip).
assert ((Cong A C D F /\ CongA B A C E D F /\ CongA B C A E F D)) by (conclude proposition_04).
close.
Qed.

End Euclid.


