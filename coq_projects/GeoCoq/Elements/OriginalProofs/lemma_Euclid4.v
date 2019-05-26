Require Export GeoCoq.Elements.OriginalProofs.proposition_20.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TGflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TGsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_22.
Require Export GeoCoq.Elements.OriginalProofs.lemma_10_12.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_Euclid4 : 
   forall A B C a b c, 
   Per A B C -> Per a b c ->
   CongA A B C a b c.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists D, (BetS A B D /\ Cong A B D B /\ Cong A C D C /\ neq B C)) by (conclude_def Per );destruct Tf as [D];spliter.
let Tf:=fresh in
assert (Tf:exists d, (BetS a b d /\ Cong a b d b /\ Cong a c d c /\ neq b c)) by (conclude_def Per );destruct Tf as [d];spliter.
assert (neq a b) by (forward_using lemma_betweennotequal).
assert (neq b a) by (conclude lemma_inequalitysymmetric).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists p, (Out b a p /\ Cong b p B A)) by (conclude lemma_layoff);destruct Tf as [p];spliter.
let Tf:=fresh in
assert (Tf:exists q, (Out b c q /\ Cong b q B C)) by (conclude lemma_layoff);destruct Tf as [q];spliter.
assert (Per a b q) by (conclude lemma_8_3).
assert (Per q b a) by (conclude lemma_8_2).
assert (Per q b p) by (conclude lemma_8_3).
assert (Per p b q) by (conclude lemma_8_2).
let Tf:=fresh in
assert (Tf:exists r, (BetS p b r /\ Cong p b r b /\ Cong p q r q /\ neq b q)) by (conclude_def Per );destruct Tf as [r];spliter.
assert (Cong q p q r) by (forward_using lemma_congruenceflip).
assert (nCol p b q) by (conclude lemma_rightangleNC).
assert (~ Col b q p).
 {
 intro.
 assert (Col p b q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ Col q p b).
 {
 intro.
 assert (Col p b q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle p b q) by (conclude_def Triangle ).
assert (Triangle b q p) by (conclude_def Triangle ).
assert (Triangle q p b) by (conclude_def Triangle ).
assert (TG b p p q b q) by (conclude proposition_20).
assert (TG q b b p q p) by (conclude proposition_20).
assert (TG p q q b p b) by (conclude proposition_20).
assert (TG b q b p q p) by (forward_using lemma_TGflip).
assert (TG b q b p p q) by (forward_using lemma_TGflip).
assert (TG q b p q p b) by (conclude lemma_TGsymmetric).
assert (TG b q p q p b) by (forward_using lemma_TGflip).
assert (TG b q p q b p) by (forward_using lemma_TGflip).
assert (TG b p p q q b) by (forward_using lemma_TGflip).
let Tf:=fresh in
assert (Tf:exists E F, (Cong B E b p /\ Cong B F b q /\ Cong E F p q /\ Out B A E /\ Triangle B E F)) by (conclude proposition_22);destruct Tf as [E[F]];spliter.
assert (BetS D B A) by (conclude axiom_betweennesssymmetry).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out B A A) by (conclude lemma_ray4).
assert (Cong B E B A) by (conclude lemma_congruencetransitive).
assert (eq E A) by (conclude lemma_layoffunique).
assert (Cong B A b p) by (conclude cn_equalitysub).
assert (Cong A F p q) by (conclude cn_equalitysub).
assert (~ eq p b).
 {
 intro.
 assert (Col p b q) by (conclude_def Col ).
 assert (nCol p b q) by (conclude lemma_rightangleNC).
 contradict.
 }
assert (Cong r b p b) by (conclude lemma_congruencesymmetric).
assert (Cong b r p b) by (forward_using lemma_congruenceflip).
assert (Cong b p B E) by (conclude lemma_congruencesymmetric).
assert (neq b p) by (conclude lemma_inequalitysymmetric).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Cong p b b r) by (conclude lemma_congruencesymmetric).
assert (Cong p q r q) by (conclude lemma_rightreverse).
assert (Cong p b A B) by (forward_using lemma_doublereverse).
assert (Cong b r p b) by (conclude lemma_congruencesymmetric).
assert (Cong b r A B) by (conclude lemma_congruencetransitive).
assert (Cong A B B D) by (forward_using lemma_congruenceflip).
assert (Cong b r B D) by (conclude lemma_congruencetransitive).
assert (Cong b q B F) by (conclude lemma_congruencesymmetric).
assert (Cong p q A F) by (conclude lemma_congruencesymmetric).
assert (Cong q r F D) by (conclude axiom_5_line).
assert (Cong A F r q) by (conclude lemma_congruencetransitive).
assert (Cong A F q r) by (forward_using lemma_congruenceflip).
assert (Cong A F F D) by (conclude lemma_congruencetransitive).
assert (Cong A F D F) by (forward_using lemma_congruenceflip).
assert (neq b q) by (conclude_def Per ).
assert (Cong q b b q) by (conclude cn_equalityreverse).
assert (Cong q b B F) by (conclude lemma_congruencetransitive).
assert (neq B F) by (conclude axiom_nocollapse).
assert (Per A B F) by (conclude_def Per ).
assert (Cong b q B F) by (conclude lemma_congruencesymmetric).
assert (Cong B C b q) by (conclude lemma_congruencesymmetric).
assert (Cong B C B F) by (conclude lemma_congruencetransitive).
assert (Cong A C A F) by (conclude lemma_10_12).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Out B F F) by (conclude lemma_ray4).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (Cong B A B A) by (conclude cn_congruencereflexive).
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (CongA A B C A B F) by (conclude_def CongA ).
assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
assert (CongA A B C A B F) by (conclude lemma_equalanglestransitive).
assert (eq p p) by (conclude cn_equalityreflexive).
assert (eq q q) by (conclude cn_equalityreflexive).
assert (Out b p p) by (conclude lemma_ray4).
assert (Out b q q) by (conclude lemma_ray4).
assert (Out B F F) by (conclude lemma_ray4).
assert (Out B A A) by (conclude lemma_ray4).
assert (Cong B A b p) by (conclude lemma_congruencesymmetric).
assert (Cong B A p b) by (forward_using lemma_congruenceflip).
assert (nCol A B F) by (conclude lemma_rightangleNC).
assert (CongA A B F p b q) by (conclude_def CongA ).
assert (CongA A B C p b q) by (conclude lemma_equalanglestransitive).
assert (nCol a b c) by (conclude lemma_rightangleNC).
assert (Out b p p) by (conclude lemma_ray4).
assert (Out b q q) by (conclude lemma_ray4).
assert (Cong b p b p) by (conclude cn_congruencereflexive).
assert (Cong b q b q) by (conclude cn_congruencereflexive).
assert (Cong p q p q) by (conclude cn_congruencereflexive).
assert (CongA a b c p b q) by (conclude_def CongA ).
assert (CongA p b q a b c) by (conclude lemma_equalanglessymmetric).
assert (CongA A B C a b c) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


