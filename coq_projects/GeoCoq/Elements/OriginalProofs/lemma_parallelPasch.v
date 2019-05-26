Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleldef2B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelPasch : 
   forall A B C D E, 
   PG A B C D -> BetS A D E ->
   exists X, BetS B X E /\ BetS C X D.
Proof.
intros.
assert (Par A B C D) by (conclude_def PG ).
assert (Par A D B C) by (conclude_def PG ).
assert (Par C D A B) by (conclude lemma_parallelsymmetric).
assert (TP C D A B) by (conclude lemma_paralleldef2B).
assert (OS A B C D) by (conclude_def TP ).
assert (OS B A C D) by (forward_using lemma_samesidesymmetric).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (Col A D D) by (conclude_def Col ).
assert (Col A D E) by (conclude_def Col ).
assert (Col D D E) by (conclude lemma_collinear4).
assert (Col E D D) by (forward_using lemma_collinearorder).
assert (Col C D D) by (conclude_def Col ).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (nCol C D A) by (forward_using lemma_NCorder).
assert (TS A C D E) by (conclude_def TS ).
assert (TS B C D E) by (conclude lemma_planeseparation).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS B H E /\ Col C D H /\ nCol C D B)) by (conclude_def TS );destruct Tf as [H];spliter.
assert (BetS E H B) by (conclude axiom_betweennesssymmetry).
assert (Col D C H) by (forward_using lemma_collinearorder).
assert (neq A D) by (conclude_def Par ).
assert (~ Meet A D B C) by (conclude_def Par ).
assert (~ Meet E D C B).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists p, (neq E D /\ neq C B /\ Col E D p /\ Col C B p)) by (conclude_def Meet );destruct Tf as [p];spliter.
 assert (neq B C) by (conclude lemma_inequalitysymmetric).
 assert (Col B C p) by (forward_using lemma_collinearorder).
 assert (Col E D A) by (forward_using lemma_collinearorder).
 assert (Col D A p) by (conclude lemma_collinear4).
 assert (Col A D p) by (forward_using lemma_collinearorder).
 assert (Meet A D B C) by (conclude_def Meet ).
 contradict.
 }
assert (eq C C) by (conclude cn_equalityreflexive).
assert (neq D E) by (forward_using lemma_betweennotequal).
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (neq B C) by (conclude_def Par ).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Col C C B) by (conclude_def Col ).
assert (BetS D H C) by (conclude lemma_collinearbetween).
assert (BetS C H D) by (conclude axiom_betweennesssymmetry).
close.
Qed.

End Euclid.


