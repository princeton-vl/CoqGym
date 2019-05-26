Require Export GeoCoq.Elements.OriginalProofs.lemma_crisscross.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_30helper : 
   forall A B E F G H, 
   Par A B E F -> BetS A G B -> BetS E H F -> ~ CR A F G H ->
   CR A E G H.
Proof.
intros.
assert (Col A G B) by (conclude_def Col ).
assert (Col E H F) by (conclude_def Col ).
assert (Col B A G) by (forward_using lemma_collinearorder).
assert (Col E F H) by (forward_using lemma_collinearorder).
assert (neq H F) by (forward_using lemma_betweennotequal).
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (neq H E) by (conclude lemma_inequalitysymmetric).
assert (neq F H) by (conclude lemma_inequalitysymmetric).
assert (neq A G) by (forward_using lemma_betweennotequal).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (Par A B F E) by (forward_using lemma_parallelflip).
assert (Col F E H) by (forward_using lemma_collinearorder).
assert (Par A B H E) by (conclude lemma_collinearparallel).
assert (Par A B H F) by (conclude lemma_collinearparallel).
assert (Par H F A B) by (conclude lemma_parallelsymmetric).
assert (Par H F B A) by (forward_using lemma_parallelflip).
assert (Par H F G A) by (conclude lemma_collinearparallel).
assert (Par H F A G) by (forward_using lemma_parallelflip).
assert (Par A G H F) by (conclude lemma_parallelsymmetric).
assert (Par A G F H) by (forward_using lemma_parallelflip).
assert (CR A H F G) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M H /\ BetS F M G)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (neq A H) by (forward_using lemma_betweennotequal).
assert (neq F G) by (forward_using lemma_betweennotequal).
assert (BetS G M F) by (conclude axiom_betweennesssymmetry).
assert (nCol A E F) by (forward_using lemma_parallelNC).
assert (nCol F E A) by (forward_using lemma_NCorder).
assert (BetS F H E) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists p, (BetS A p E /\ BetS F M p)) by (conclude postulate_Pasch_outer);destruct Tf as [p];spliter.
assert (nCol A G H) by (forward_using lemma_parallelNC).
assert (nCol A H G) by (forward_using lemma_NCorder).
assert (Col F M G) by (conclude_def Col ).
assert (Col F M p) by (conclude_def Col ).
assert (neq F M) by (forward_using lemma_betweennotequal).
assert (Col M G p) by (conclude lemma_collinear4).
assert (Col M p G) by (forward_using lemma_collinearorder).
assert (Col M p F) by (forward_using lemma_collinearorder).
assert (neq M p) by (forward_using lemma_betweennotequal).
assert (Col p G F) by (conclude lemma_collinear4).
assert (Col G F p) by (forward_using lemma_collinearorder).
assert (Col H F E) by (forward_using lemma_collinearorder).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq A G) by (forward_using lemma_betweennotequal).
assert (neq E F) by (forward_using lemma_betweennotequal).
assert (neq F E) by (conclude lemma_inequalitysymmetric).
assert (~ Meet A B H E) by (conclude_def Par ).
assert (BetS G p F) by (conclude lemma_collinearbetween).
assert (BetS F p G) by (conclude axiom_betweennesssymmetry).
assert (BetS M p G) by (conclude lemma_3_6a).
assert (BetS G p M) by (conclude axiom_betweennesssymmetry).
assert (nCol A G H) by (forward_using lemma_parallelNC).
assert (nCol A H G) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists m, (BetS G m H /\ BetS A p m)) by (conclude postulate_Pasch_outer);destruct Tf as [m];spliter.
assert (Col A p m) by (conclude_def Col ).
assert (Col A p E) by (conclude_def Col ).
assert (neq A p) by (forward_using lemma_betweennotequal).
assert (Col p m E) by (conclude lemma_collinear4).
assert (Col p m A) by (forward_using lemma_collinearorder).
assert (neq p m) by (forward_using lemma_betweennotequal).
assert (Col m E A) by (conclude lemma_collinear4).
assert (Col A E m) by (forward_using lemma_collinearorder).
assert (neq A E) by (forward_using lemma_NCdistinct).
assert (neq G H) by (forward_using lemma_NCdistinct).
assert (neq G B) by (forward_using lemma_betweennotequal).
assert (neq B G) by (conclude lemma_inequalitysymmetric).
assert (Par H F B G) by (conclude lemma_collinearparallel).
assert (Par B G H F) by (conclude lemma_parallelsymmetric).
assert (Par G B F H) by (forward_using lemma_parallelflip).
assert (~ Meet G B F H) by (conclude_def Par ).
assert (Col G A B) by (forward_using lemma_collinearorder).
assert (BetS A m E) by (conclude lemma_collinearbetween).
assert (CR A E G H) by (conclude_def CR ).
close.
Qed.

End Euclid.


