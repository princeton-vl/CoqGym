Require Export GeoCoq.Elements.OriginalProofs.lemma_Euclid4.
Require Export GeoCoq.Elements.OriginalProofs.proposition_14.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_righttogether : 
   forall A B C G, 
   Per G A B -> Per B A C -> TS G B A C ->
   RT G A B B A C /\ BetS G A C.
Proof.
intros.
assert (Per B A G) by (conclude lemma_8_2).
assert (neq A G) by (conclude_def Per ).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists D, (BetS G A D /\ Cong A D G A)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (neq A B) by (conclude_def Per ).
assert (Out A B B) by (conclude lemma_ray4).
assert (Supp G A B B D) by (conclude_def Supp ).
assert (nCol B A G) by (conclude_def TS ).
assert (nCol G A B) by (forward_using lemma_NCorder).
assert (CongA G A B G A B) by (conclude lemma_equalanglesreflexive).
assert (Col G A D) by (conclude_def Col ).
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (Per D A B) by (conclude lemma_collinearright).
assert (Per B A D) by (conclude lemma_8_2).
assert (CongA B A C B A D) by (conclude lemma_Euclid4).
assert (RT G A B B A C) by (conclude_def RT ).
assert (TS C B A G) by (conclude lemma_oppositesidesymmetric).
assert (BetS G A C) by (conclude proposition_14).
close.
Qed.

End Euclid.


