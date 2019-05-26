Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5.
Require Export GeoCoq.Elements.OriginalProofs.proposition_14.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleaddition : 
   forall A B C D E F P Q R a b c d e f p q r, 
   SumA A B C D E F P Q R -> CongA A B C a b c -> CongA D E F d e f -> SumA a b c d e f p q r ->
   CongA P Q R p q r.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists S, (CongA A B C P Q S /\ CongA D E F S Q R /\ BetS P S R)) by (conclude_def SumA );destruct Tf as [S];spliter.
let Tf:=fresh in
assert (Tf:exists s, (CongA a b c p q s /\ CongA d e f s q r /\ BetS p s r)) by (conclude_def SumA );destruct Tf as [s];spliter.
assert (nCol P Q S) by (conclude lemma_equalanglesNC).
assert (nCol S Q R) by (conclude lemma_equalanglesNC).
assert (neq Q P) by (forward_using lemma_NCdistinct).
assert (neq Q S) by (forward_using lemma_NCdistinct).
assert (neq Q R) by (forward_using lemma_NCdistinct).
assert (nCol p q s) by (conclude lemma_equalanglesNC).
assert (nCol s q r) by (conclude lemma_equalanglesNC).
assert (neq q p) by (forward_using lemma_NCdistinct).
assert (neq q r) by (forward_using lemma_NCdistinct).
assert (neq q s) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists G, (Out q p G /\ Cong q G Q P)) by (conclude lemma_layoff);destruct Tf as [G];spliter.
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (Out q s H /\ Cong q H Q S)) by (conclude lemma_layoff);destruct Tf as [H];spliter.
let Tf:=fresh in
assert (Tf:exists K, (Out q r K /\ Cong q K Q R)) by (conclude lemma_layoff);destruct Tf as [K];spliter.
assert (CongA P Q S A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA P Q S a b c) by (conclude lemma_equalanglestransitive).
assert (CongA P Q S p q s) by (conclude lemma_equalanglestransitive).
assert (CongA P Q S G q H) by (conclude lemma_equalangleshelper).
assert (CongA S Q R D E F) by (conclude lemma_equalanglessymmetric).
assert (CongA S Q R d e f) by (conclude lemma_equalanglestransitive).
assert (CongA S Q R s q r) by (conclude lemma_equalanglestransitive).
assert (CongA S Q R H q K) by (conclude lemma_equalangleshelper).
assert (nCol G q H) by (conclude lemma_equalanglesNC).
assert (CongA G q H P Q S) by (conclude lemma_equalanglessymmetric).
assert ((Cong G H P S /\ CongA q G H Q P S /\ CongA q H G Q S P)) by (conclude proposition_04).
assert (CongA H q K S Q R) by (conclude lemma_equalanglessymmetric).
assert ((Cong H K S R /\ CongA q H K Q S R /\ CongA q K H Q R S)) by (conclude proposition_04).
assert (CongA G H q P S Q) by (conclude lemma_equalanglesflip).
assert (eq Q Q) by (conclude cn_equalityreflexive).
assert (neq S Q) by (forward_using lemma_NCdistinct).
assert (Out S Q Q) by (conclude lemma_ray4).
assert (Supp P S Q Q R) by (conclude_def Supp ).
assert (RT G H q q H K) by (conclude_def RT ).
assert (Col q s H) by (conclude lemma_rayimpliescollinear).
assert (Col q H s) by (forward_using lemma_collinearorder).
assert (Col q p G) by (conclude lemma_rayimpliescollinear).
assert (Col G q p) by (forward_using lemma_collinearorder).
assert (eq q q) by (conclude cn_equalityreflexive).
assert (Col G q q) by (conclude_def Col ).
assert (neq q p) by (conclude lemma_ray2).
assert (neq p q) by (conclude lemma_inequalitysymmetric).
assert (nCol p q H) by (conclude lemma_NChelper).
assert (nCol q H p) by (forward_using lemma_NCorder).
assert (TS p q H r) by (conclude_def TS ).
assert (TS r q H p) by (conclude lemma_oppositesidesymmetric).
assert (Col q H q) by (conclude_def Col ).
assert (Out q K r) by (conclude lemma_ray5).
assert (TS K q H p) by (conclude lemma_9_5).
assert (TS p q H K) by (conclude lemma_oppositesidesymmetric).
assert (Out q G p) by (conclude lemma_ray5).
assert (TS G q H K) by (conclude lemma_9_5).
assert (TS K q H G) by (conclude lemma_oppositesidesymmetric).
assert (neq q H) by (conclude lemma_raystrict).
assert (neq H q) by (conclude lemma_inequalitysymmetric).
assert (Out H q q) by (conclude lemma_ray4).
assert (BetS G H K) by (conclude proposition_14).
assert (Cong G K P R) by (conclude cn_sumofparts).
assert (eq P P) by (conclude cn_equalityreflexive).
assert (eq R R) by (conclude cn_equalityreflexive).
assert (Out Q P P) by (conclude lemma_ray4).
assert (Out Q R R) by (conclude lemma_ray4).
assert (nCol P S Q) by (forward_using lemma_NCorder).
assert (Col P S R) by (conclude_def Col ).
assert (eq P P) by (conclude cn_equalityreflexive).
assert (Col P S P) by (conclude_def Col ).
assert (neq P R) by (forward_using lemma_betweennotequal).
assert (nCol P R Q) by (conclude lemma_NChelper).
assert (nCol P Q R) by (forward_using lemma_NCorder).
assert (Cong Q P q G) by (conclude lemma_congruencesymmetric).
assert (Cong Q R q K) by (conclude lemma_congruencesymmetric).
assert (Cong P R G K) by (conclude lemma_congruencesymmetric).
assert (CongA P Q R p q r) by (conclude_def CongA ).
close.
Qed.

End Euclid.


