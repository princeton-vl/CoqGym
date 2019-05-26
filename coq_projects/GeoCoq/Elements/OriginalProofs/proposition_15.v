Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_15 : 
   forall A B C D E, 
   BetS A E B -> BetS C E D -> nCol A E C ->
   CongA A E C D E B /\ CongA C E B A E D.
Proof.
intros.
assert (neq E D) by (forward_using lemma_betweennotequal).
assert (neq D E) by (conclude lemma_inequalitysymmetric).
assert (neq E B) by (forward_using lemma_betweennotequal).
assert (neq B E) by (conclude lemma_inequalitysymmetric).
assert (~ Col B E D).
 {
 intro.
 assert (Col A E B) by (conclude_def Col ).
 assert (Col B E A) by (forward_using lemma_collinearorder).
 assert (Col E A D) by (conclude lemma_collinear4).
 assert (Col C E D) by (conclude_def Col ).
 assert (Col D E C) by (forward_using lemma_collinearorder).
 assert (Col D E A) by (forward_using lemma_collinearorder).
 assert (Col E C A) by (conclude lemma_collinear4).
 assert (Col A E C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out E D D) by (conclude lemma_ray4).
assert (Out E B B) by (conclude lemma_ray4).
assert (BetS B E A) by (conclude axiom_betweennesssymmetry).
assert (Supp B E D D A) by (conclude_def Supp ).
assert (BetS D E C) by (conclude axiom_betweennesssymmetry).
assert (Supp D E B B C) by (conclude_def Supp ).
assert (~ Col A E D).
 {
 intro.
 assert (Col C E D) by (conclude_def Col ).
 assert (Col D E C) by (forward_using lemma_collinearorder).
 assert (Col D E A) by (forward_using lemma_collinearorder).
 assert (Col E C A) by (conclude lemma_collinear4).
 assert (Col A E C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B E D D E B) by (conclude lemma_ABCequalsCBA).
assert (CongA D E A B E C) by (conclude lemma_supplements).
assert (~ Col B E C).
 {
 intro.
 assert (Col A E B) by (conclude_def Col ).
 assert (Col B E A) by (forward_using lemma_collinearorder).
 assert (Col E A C) by (conclude lemma_collinear4).
 assert (Col A E C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B E C C E B) by (conclude lemma_ABCequalsCBA).
assert (CongA D E A C E B) by (conclude lemma_equalanglestransitive).
assert (CongA A E D D E A) by (conclude lemma_ABCequalsCBA).
assert (CongA A E D C E B) by (conclude lemma_equalanglestransitive).
assert (CongA C E B A E D) by (conclude lemma_equalanglessymmetric).
assert (~ eq E C).
 {
 intro.
 assert (Col B E C) by (conclude_def Col ).
 contradict.
 }
assert (Out E C C) by (conclude lemma_ray4).
assert (Supp B E C C A) by (conclude_def Supp ).
assert (BetS C E D) by (conclude axiom_betweennesssymmetry).
assert (Supp C E B B D) by (conclude_def Supp ).
assert (~ Col A E C).
 {
 intro.
 assert (Col D E C) by (conclude_def Col ).
 assert (Col C E D) by (forward_using lemma_collinearorder).
 assert (Col C E A) by (forward_using lemma_collinearorder).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 assert (Col E D A) by (conclude lemma_collinear4).
 assert (Col A E D) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B E C C E B) by (conclude lemma_ABCequalsCBA).
assert (CongA C E A B E D) by (conclude lemma_supplements).
assert (~ Col B E D).
 {
 intro.
 assert (Col A E B) by (conclude_def Col ).
 assert (Col B E A) by (forward_using lemma_collinearorder).
 assert (Col E A D) by (conclude lemma_collinear4).
 assert (Col A E D) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA B E D D E B) by (conclude lemma_ABCequalsCBA).
assert (CongA C E A D E B) by (conclude lemma_equalanglestransitive).
assert (CongA A E C C E A) by (conclude lemma_ABCequalsCBA).
assert (CongA A E C D E B) by (conclude lemma_equalanglestransitive).
close.
Qed.

Lemma proposition_15a :
 forall A B C D E : Point,
       BetS A E B ->
       BetS C E D -> nCol A E C -> CongA A E C D E B.
Proof.
intros.
apply (proposition_15 A B C D E);assumption.
Qed.

Lemma proposition_15b :
 forall A B C D E : Point,
       BetS A E B ->
       BetS C E D -> nCol A E C ->
       CongA C E B A E D.
Proof.
intros.
apply (proposition_15 A B C D E);assumption.
Qed.

End Euclid.


