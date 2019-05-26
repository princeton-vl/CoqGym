Require Export GeoCoq.Elements.OriginalProofs.proposition_31short.
Require Export GeoCoq.Elements.OriginalProofs.proposition_38.
Require Export GeoCoq.Elements.OriginalProofs.proposition_39.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_40 : 
   forall A B C D E H, 
   Cong B C H E -> ET A B C D H E -> Triangle A B C -> Triangle D H E -> Col B C H -> Col B C E -> OS A D B C -> neq A D ->
   Par A D B C.
Proof.
intros.
assert (nCol D H E) by (conclude_def Triangle ).
assert (neq H E) by (forward_using lemma_NCdistinct).
assert (neq E H) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists R, (BetS E H R /\ Cong H R E H)) by (conclude lemma_extension);destruct Tf as [R];spliter.
assert (BetS R H E) by (conclude axiom_betweennesssymmetry).
assert (nCol H E D) by (forward_using lemma_NCorder).
assert (Col R H E) by (conclude_def Col ).
assert (Col H E R) by (forward_using lemma_collinearorder).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col H E E) by (conclude_def Col ).
assert (neq R E) by (forward_using lemma_betweennotequal).
assert (nCol R E D) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists P Q M, (BetS P D Q /\ CongA P D H D H E /\ Par P Q R E /\ BetS P M E /\ BetS D M H)) by (conclude proposition_31short);destruct Tf as [P[Q[M]]];spliter.
assert (Col R E H) by (forward_using lemma_collinearorder).
assert (Par P Q H E) by (conclude lemma_collinearparallel).
assert (Col P D Q) by (conclude_def Col ).
assert (Col P Q D) by (forward_using lemma_collinearorder).
assert (Cong H E B C) by (conclude lemma_congruencesymmetric).
assert (Col C B H) by (forward_using lemma_collinearorder).
assert (Col C B E) by (forward_using lemma_collinearorder).
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Col B H E) by (conclude lemma_collinear4).
assert (Col H E B) by (forward_using lemma_collinearorder).
assert (Col B C H) by (forward_using lemma_collinearorder).
assert (Col B C E) by (forward_using lemma_collinearorder).
assert (Col C H E) by (conclude lemma_collinear4).
assert (Col H E C) by (forward_using lemma_collinearorder).
assert (ET D H E D B C) by (conclude proposition_38).
assert (ET A B C D B C) by (conclude axiom_ETtransitive).
assert (nCol H E D) by (forward_using lemma_NCorder).
assert (nCol B C D) by (conclude lemma_NChelper).
assert (nCol D B C) by (forward_using lemma_NCorder).
assert (Triangle D B C) by (conclude_def Triangle ).
assert (Par A D B C) by (conclude proposition_39).
close.
Qed.

End Euclid.


