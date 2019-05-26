Require Export GeoCoq.Elements.OriginalProofs.lemma_crossbar.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_sameside2.
Require Export GeoCoq.Elements.OriginalProofs.proposition_07.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossbar2 : 
   forall A G H P S T, 
   LtA H G A H G P -> OS A P G H -> Out G H S -> Out G P T ->
   exists X, BetS T X S /\ Out G A X.
Proof.
intros.
assert (nCol G H P) by (conclude_def OS ).
let Tf:=fresh in
assert (Tf:exists J K L, (BetS L K J /\ Out G H L /\ Out G P J /\ CongA H G A H G K)) by (conclude_def LtA );destruct Tf as [J[K[L]]];spliter.
assert (nCol H G K) by (conclude lemma_equalanglesNC).
assert (~ Col L G J).
 {
 intro.
 assert (Col G H L) by (conclude lemma_rayimpliescollinear).
 assert (Col G P J) by (conclude lemma_rayimpliescollinear).
 assert (Col L G H) by (forward_using lemma_collinearorder).
 assert (neq G L) by (conclude lemma_raystrict).
 assert (neq L G) by (conclude lemma_inequalitysymmetric).
 assert (Col G J H) by (conclude lemma_collinear4).
 assert (Col J G H) by (forward_using lemma_collinearorder).
 assert (Col J G P) by (forward_using lemma_collinearorder).
 assert (neq G J) by (conclude lemma_raystrict).
 assert (neq J G) by (conclude lemma_inequalitysymmetric).
 assert (Col G H P) by (conclude lemma_collinear4).
 contradict.
 }
assert (Triangle L G J) by (conclude_def Triangle ).
assert (Out G J T) by (conclude lemma_ray3).
assert (Out G L S) by (conclude lemma_ray3).
let Tf:=fresh in
assert (Tf:exists M, (Out G K M /\ BetS S M T)) by (conclude lemma_crossbar);destruct Tf as [M];spliter.
assert (BetS T M S) by (conclude axiom_betweennesssymmetry).
assert (CongA H G K H G A) by (conclude lemma_equalanglessymmetric).
assert (neq G A) by (forward_using lemma_angledistinct).
assert (neq G M) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists N, (Out G A N /\ Cong G N G M)) by (conclude lemma_layoff);destruct Tf as [N];spliter.
assert (eq H H) by (conclude cn_equalityreflexive).
assert (~ eq G H).
 {
 intro.
 assert (Col G H P) by (conclude_def Col ).
 contradict.
 }
assert (Out G H H) by (conclude lemma_ray4).
assert (~ Col H G M).
 {
 intro.
 assert (Col G K M) by (conclude lemma_rayimpliescollinear).
 assert (Col M G K) by (forward_using lemma_collinearorder).
 assert (Col M G H) by (forward_using lemma_collinearorder).
 assert (neq G M) by (conclude lemma_raystrict).
 assert (neq M G) by (conclude lemma_inequalitysymmetric).
 assert (Col G K H) by (conclude lemma_collinear4).
 assert (Col H G K) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA H G M H G M) by (conclude lemma_equalanglesreflexive).
assert (Out G M K) by (conclude lemma_ray5).
assert (CongA H G M H G K) by (conclude lemma_equalangleshelper).
assert (CongA H G M H G A) by (conclude lemma_equalanglestransitive).
assert (nCol H G A) by (conclude lemma_equalanglesNC).
assert (CongA H G A H G A) by (conclude lemma_equalanglesreflexive).
assert (CongA H G A H G N) by (conclude lemma_equalangleshelper).
assert (CongA H G M H G N) by (conclude lemma_equalanglestransitive).
assert (CongA H G N H G M) by (conclude lemma_equalanglessymmetric).
assert (Cong G H G H) by (conclude cn_congruencereflexive).
assert (Cong H N H M) by (conclude proposition_04).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G G H) by (conclude_def Col ).
assert (OS A T G H) by (conclude lemma_sameside2).
assert (neq S M) by (forward_using lemma_betweennotequal).
assert (Out S M T) by (conclude lemma_ray4).
assert (Out S T M) by (conclude lemma_ray5).
assert (Col G H S) by (conclude lemma_rayimpliescollinear).
assert (Col G S H) by (forward_using lemma_collinearorder).
assert (OS A M G H) by (conclude lemma_sameside2).
assert (OS M A G H) by (forward_using lemma_samesidesymmetric).
assert (OS M N G H) by (conclude lemma_sameside2).
assert (Cong N H M H) by (forward_using lemma_congruenceflip).
assert (Cong M H N H) by (conclude lemma_congruencesymmetric).
assert (Cong N G M G) by (forward_using lemma_congruenceflip).
assert (Cong M G N G) by (conclude lemma_congruencesymmetric).
assert (eq M N) by (conclude proposition_07).
assert (eq N M) by (conclude lemma_equalitysymmetric).
assert (Out G A M) by (conclude cn_equalitysub).
close.
Qed.

End Euclid.


