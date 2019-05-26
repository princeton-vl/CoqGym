Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.proposition_20.
Require Export GeoCoq.Elements.OriginalProofs.lemma_21helper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TTorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TTflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TTtransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TTflip2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_21 : 
   forall A B C D E, 
   Triangle A B C -> BetS A E C -> BetS B D E ->
   TT B A A C B D D C /\ LtA B A C B D C.
Proof.
intros.
assert (BetS E D B) by (conclude axiom_betweennesssymmetry).
assert (nCol A B C) by (conclude_def Triangle ).
assert (Col A E C) by (conclude_def Col ).
assert (Col A C E) by (forward_using lemma_collinearorder).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A C A) by (conclude_def Col ).
assert (nCol A E B) by (conclude lemma_NChelper).
assert (nCol A B E) by (forward_using lemma_NCorder).
assert (Triangle A B E) by (conclude_def Triangle ).
assert (TG B A A E B E) by (conclude proposition_20).
assert (TT B A A C B E E C) by (conclude lemma_21helper).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (Col A E C) by (conclude_def Col ).
assert (Col A C E) by (forward_using lemma_collinearorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col A C C) by (conclude_def Col ).
assert (neq E C) by (forward_using lemma_betweennotequal).
assert (nCol E C B) by (conclude lemma_NChelper).
assert (nCol E B C) by (forward_using lemma_NCorder).
assert (Col E D B) by (conclude_def Col ).
assert (Col E B D) by (forward_using lemma_collinearorder).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col E B E) by (conclude_def Col ).
assert (neq E D) by (forward_using lemma_betweennotequal).
assert (nCol E D C) by (conclude lemma_NChelper).
assert (nCol E C D) by (forward_using lemma_NCorder).
assert (Triangle E C D) by (conclude_def Triangle ).
assert (TG C E E D C D) by (conclude proposition_20).
assert (TT C E E B C D D B) by (conclude lemma_21helper).
assert (TT E B C E C D D B) by (conclude lemma_TTorder).
assert (TT B E E C C D D B) by (conclude lemma_TTflip).
assert (TT B A A C C D D B) by (conclude lemma_TTtransitive).
assert (TT B A A C B D D C) by (conclude lemma_TTflip2).
assert (nCol C E D) by (forward_using lemma_NCorder).
assert (Triangle C E D) by (conclude_def Triangle ).
assert (LtA D E C C D B) by (conclude proposition_16).
assert (nCol E B C) by (forward_using lemma_NCorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col E B B) by (conclude_def Col ).
assert (Col E D B) by (conclude_def Col ).
assert (Col E B D) by (forward_using lemma_collinearorder).
assert (neq B D) by (forward_using lemma_betweennotequal).
assert (neq D B) by (conclude lemma_inequalitysymmetric).
assert (nCol D B C) by (conclude lemma_NChelper).
assert (nCol B A E) by (forward_using lemma_NCorder).
assert (Triangle B A E) by (conclude_def Triangle ).
assert (LtA E A B B E C) by (conclude proposition_16).
assert (CongA B A E E A B) by (conclude lemma_ABCequalsCBA).
assert (LtA B A E B E C) by (conclude lemma_angleorderrespectscongruence2).
assert (nCol C E B) by (forward_using lemma_NCorder).
assert (CongA C E B B E C) by (conclude lemma_ABCequalsCBA).
assert (LtA B A E C E B) by (conclude lemma_angleorderrespectscongruence).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (Out A E C) by (conclude lemma_ray4).
assert (Out A C E) by (conclude lemma_ray5).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (Out A B B) by (conclude lemma_ray4).
assert (nCol B A C) by (forward_using lemma_NCorder).
assert (CongA B A C B A C) by (conclude lemma_equalanglesreflexive).
assert (CongA B A C B A E) by (conclude lemma_equalangleshelper).
assert (BetS E D B) by (conclude axiom_betweennesssymmetry).
assert (Out E D B) by (conclude lemma_ray4).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out E C C) by (conclude lemma_ray4).
assert (nCol C E D) by (forward_using lemma_NCorder).
assert (CongA C E D C E D) by (conclude lemma_equalanglesreflexive).
assert (CongA C E D C E B) by (conclude lemma_equalangleshelper).
assert (LtA B A E C E D) by (conclude lemma_angleorderrespectscongruence).
assert (LtA B A C C E D) by (conclude lemma_angleorderrespectscongruence2).
assert (nCol D E C) by (forward_using lemma_NCorder).
assert (CongA D E C C E D) by (conclude lemma_ABCequalsCBA).
assert (LtA B A C D E C) by (conclude lemma_angleorderrespectscongruence).
assert (LtA B A C C D B) by (conclude lemma_angleordertransitive).
assert (nCol B D C) by (forward_using lemma_NCorder).
assert (CongA B D C C D B) by (conclude lemma_ABCequalsCBA).
assert (LtA B A C B D C) by (conclude lemma_angleorderrespectscongruence).
close.
Qed.

End Euclid.

