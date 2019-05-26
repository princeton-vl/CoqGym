Require Export GeoCoq.Elements.OriginalProofs.proposition_33.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_Playfair.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_triangletoparallelogram : 
   forall A C D E F, 
   Par D C E F -> Col E F A ->
   exists X, PG A X C D /\ Col E F X.
Proof.
intros.
assert (nCol D C E) by (forward_using lemma_parallelNC).
assert (neq D C) by (forward_using lemma_NCdistinct).
assert (neq C D) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists B, (BetS C D B /\ Cong D B C D)) by (conclude lemma_extension);destruct Tf as [B];spliter.
assert (BetS B D C) by (conclude axiom_betweennesssymmetry).
assert (nCol C E F) by (forward_using lemma_parallelNC).
assert (neq E F) by (forward_using lemma_NCdistinct).
assert (~ Col B C A).
 {
 intro.
 assert (Col C D B) by (conclude_def Col ).
 assert (Col B C D) by (forward_using lemma_collinearorder).
 assert (neq B C) by (forward_using lemma_betweennotequal).
 assert (Col C A D) by (conclude lemma_collinear4).
 assert (Col D C A) by (forward_using lemma_collinearorder).
 assert (Meet D C E F) by (conclude_def Meet ).
 assert (~ Meet D C E F) by (conclude_def Par ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists c b M, (BetS c A b /\ CongA b A D A D B /\ CongA b A D B D A /\ CongA D A b B D A /\ CongA c A D A D C /\ CongA c A D C D A /\ CongA D A c C D A /\ Par c b B C /\ Cong c A D C /\ Cong A b B D /\ Cong A M M D /\ Cong c M M C /\ Cong B M M b /\ BetS c M C /\ BetS B M b /\ BetS A M D)) by (conclude proposition_31);destruct Tf as [c[b[M]]];spliter.
assert (BetS b M B) by (conclude axiom_betweennesssymmetry).
assert (nCol b B C) by (forward_using lemma_parallelNC).
let Tf:=fresh in
assert (Tf:exists R, (BetS b R D /\ BetS C R M)) by (conclude postulate_Pasch_inner);destruct Tf as [R];spliter.
assert (BetS C M c) by (conclude axiom_betweennesssymmetry).
assert (BetS C R c) by (conclude lemma_3_6b).
assert (BetS b A c) by (conclude axiom_betweennesssymmetry).
assert (nCol c b C) by (forward_using lemma_parallelNC).
assert (nCol b c C) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists Q, (BetS b Q R /\ BetS C Q A)) by (conclude postulate_Pasch_inner);destruct Tf as [Q];spliter.
assert (BetS b Q D) by (conclude lemma_3_6b).
assert (Col C D B) by (conclude_def Col ).
assert (Col B C D) by (forward_using lemma_collinearorder).
assert (Par c b D C) by (conclude lemma_collinearparallel).
assert (Par D C c b) by (conclude lemma_parallelsymmetric).
assert (Col c A b) by (conclude_def Col ).
assert (Col c b A) by (forward_using lemma_collinearorder).
assert (neq A b) by (forward_using lemma_betweennotequal).
assert (Par D C A b) by (conclude lemma_collinearparallel).
assert (Par A b D C) by (conclude lemma_parallelsymmetric).
assert (Par b A C D) by (forward_using lemma_parallelflip).
assert (Cong B D D B) by (conclude cn_equalityreverse).
assert (Cong A b D B) by (conclude lemma_congruencetransitive).
assert (Cong A b C D) by (conclude lemma_congruencetransitive).
assert (Cong b A C D) by (forward_using lemma_congruenceflip).
assert (BetS A Q C) by (conclude axiom_betweennesssymmetry).
assert ((Par b C A D /\ Cong b C A D)) by (conclude proposition_33).
assert (Par A b C D) by (forward_using lemma_parallelflip).
assert (Par A D b C) by (conclude lemma_parallelsymmetric).
assert (PG A b C D) by (conclude_def PG ).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col E F E) by (conclude_def Col ).
assert (Col E F b).
by cases on (eq A F \/ neq A F).
{
 assert (neq F E) by (conclude lemma_inequalitysymmetric).
 assert (neq A E) by (conclude cn_equalitysub).
 assert (Par D C A E) by (conclude lemma_collinearparallel2).
 assert (Col A b E) by (conclude lemma_Playfair).
 assert (Col F b E) by (conclude cn_equalitysub).
 assert (Col E F b) by (forward_using lemma_collinearorder).
 close.
 }
{
 assert (Par D C A F) by (conclude lemma_collinearparallel).
 assert (Col A b F) by (conclude lemma_Playfair).
 assert (Col A F b) by (forward_using lemma_collinearorder).
 assert (Col A F E) by (forward_using lemma_collinearorder).
 assert (Col F b E) by (conclude lemma_collinear4).
 assert (Col E F b) by (forward_using lemma_collinearorder).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


