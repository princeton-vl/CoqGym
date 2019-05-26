Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29C : 
   forall B D E G H, 
   Par G B H D -> OS B D G H -> BetS E G H ->
   CongA E G B G H D /\ RT B G H G H D.
Proof.
intros.
assert (nCol G B H) by (forward_using lemma_parallelNC).
assert (~ eq G B).
 {
 intro.
 assert (Col G B H) by (conclude_def Col ).
 contradict.
 }
assert (neq B G) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists A, (BetS B G A /\ Cong G A B G)) by (conclude lemma_extension);destruct Tf as [A];spliter.
assert (BetS A G B) by (conclude axiom_betweennesssymmetry).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (Col A B G) by (conclude_def Col ).
assert (Col G B A) by (forward_using lemma_collinearorder).
assert (Par H D G B) by (conclude lemma_parallelsymmetric).
assert (Par H D A B) by (conclude lemma_collinearparallel).
assert (Par H D B A) by (forward_using lemma_parallelflip).
assert (Col B A G) by (forward_using lemma_collinearorder).
assert (neq G A) by (forward_using lemma_betweennotequal).
assert (Par H D G A) by (conclude lemma_collinearparallel).
assert (Par H D A G) by (forward_using lemma_parallelflip).
assert (Par A G H D) by (conclude lemma_parallelsymmetric).
let Tf:=fresh in
assert (Tf:exists a g h d m, (neq A G /\ neq H D /\ Col A G a /\ Col A G g /\ neq a g /\ Col H D h /\ Col H D d /\ neq h d /\ ~ Meet A G H D /\ BetS a m d /\ BetS h m g)) by (conclude_def Par );destruct Tf as [a[g[h[d[m]]]]];spliter.
assert (neq D H) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists C, (BetS D H C /\ Cong H C D H)) by (conclude lemma_extension);destruct Tf as [C];spliter.
assert (BetS H G E) by (conclude axiom_betweennesssymmetry).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq D C) by (forward_using lemma_betweennotequal).
assert (neq C D) by (conclude lemma_inequalitysymmetric).
assert (Col A G B) by (conclude_def Col ).
assert (Col G A B) by (forward_using lemma_collinearorder).
assert (Col G A a) by (forward_using lemma_collinearorder).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (Col A B a) by (conclude lemma_collinear4).
assert (Col G A g) by (forward_using lemma_collinearorder).
assert (Col A B g) by (conclude lemma_collinear4).
assert (Col D H C) by (conclude_def Col ).
assert (Col H D C) by (forward_using lemma_collinearorder).
assert (Col D C h) by (conclude lemma_collinear4).
assert (Col C D h) by (forward_using lemma_collinearorder).
assert (Col D d C) by (conclude lemma_collinear4).
assert (Col C D d) by (forward_using lemma_collinearorder).
assert (~ Meet A B C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists M, (neq A B /\ neq C D /\ Col A B M /\ Col C D M)) by (conclude_def Meet );destruct Tf as [M];spliter.
 assert (Col B A G) by (forward_using lemma_collinearorder).
 assert (Col B A M) by (forward_using lemma_collinearorder).
 assert (Col A G M) by (conclude lemma_collinear4).
 assert (Col C D H) by (forward_using lemma_collinearorder).
 assert (Col D H M) by (conclude lemma_collinear4).
 assert (Col H D M) by (forward_using lemma_collinearorder).
 assert (Meet A G H D) by (conclude_def Meet ).
 contradict.
 }
assert (Par A B C D) by (conclude_def Par ).
assert (BetS C H D) by (conclude axiom_betweennesssymmetry).
assert (BetS E G H) by (conclude axiom_betweennesssymmetry).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G H G) by (conclude_def Col ).
assert (nCol G B H) by (forward_using lemma_parallelNC).
assert (nCol G H B) by (forward_using lemma_NCorder).
assert (OS D B G H) by (forward_using lemma_samesidesymmetric).
assert (TS B G H A) by (conclude_def TS ).
assert (TS D G H A) by (conclude lemma_planeseparation).
assert (TS A G H D) by (conclude lemma_oppositesidesymmetric).
assert ((CongA A G H G H D /\ CongA E G B G H D /\ RT B G H G H D)) by (conclude proposition_29).
close.
Qed.

End Euclid.


