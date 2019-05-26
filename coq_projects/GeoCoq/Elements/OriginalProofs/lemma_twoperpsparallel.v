Require Export GeoCoq.Elements.OriginalProofs.lemma_Euclid4.
Require Export GeoCoq.Elements.OriginalProofs.proposition_28C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_twoperpsparallel : 
   forall A B C D, 
   Per A B C -> Per B C D -> OS A D B C ->
   Par A B C D.
Proof.
intros.
assert (nCol A B C) by (conclude lemma_rightangleNC).
assert (neq B C) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists E, (BetS B C E /\ Cong C E B C)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (Col B C E) by (conclude_def Col ).
assert (neq C E) by (forward_using lemma_betweennotequal).
assert (neq E C) by (conclude lemma_inequalitysymmetric).
assert (Per E C D) by (conclude lemma_collinearright).
assert (Per D C E) by (conclude lemma_8_2).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (nCol B C D) by (conclude lemma_rightangleNC).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (Out C D D) by (conclude lemma_ray4).
assert (Supp B C D D E) by (conclude_def Supp ).
assert (CongA A B C B C D) by (conclude lemma_Euclid4).
assert (CongA B C D D C E) by (conclude lemma_Euclid4).
assert (RT A B C B C D) by (conclude_def RT ).
assert (Par B A C D) by (conclude proposition_28C).
assert (Par C D B A) by (conclude lemma_parallelsymmetric).
assert (Par C D A B) by (forward_using lemma_parallelflip).
assert (Par A B C D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.


