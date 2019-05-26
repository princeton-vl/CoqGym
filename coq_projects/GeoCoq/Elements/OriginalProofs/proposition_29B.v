Require Export GeoCoq.Elements.OriginalProofs.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_29B : 
   forall A D G H, 
   Par A G H D -> TS A G H D ->
   CongA A G H G H D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a d g h m, (neq A G /\ neq H D /\ Col A G a /\ Col A G g /\ neq a g /\ Col H D h /\ Col H D d /\ neq h d /\ ~ Meet A G H D /\ BetS a m d /\ BetS h m g)) by (conclude_def Par );destruct Tf as [a[d[g[h[m]]]]];spliter.
assert (neq D H) by (conclude lemma_inequalitysymmetric).
assert (~ eq H G).
 {
 intro.
 assert (eq H H) by (conclude cn_equalityreflexive).
 assert (Col H D H) by (conclude_def Col ).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Col A G G) by (conclude_def Col ).
 assert (Col A G H) by (conclude cn_equalitysub).
 assert (Meet A G H D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists B, (BetS A G B /\ Cong G B A G)) by (conclude lemma_extension);destruct Tf as [B];spliter.
let Tf:=fresh in
assert (Tf:exists C, (BetS D H C /\ Cong H C D H)) by (conclude lemma_extension);destruct Tf as [C];spliter.
let Tf:=fresh in
assert (Tf:exists E, (BetS H G E /\ Cong G E H G)) by (conclude lemma_extension);destruct Tf as [E];spliter.
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
assert ((CongA A G H G H D /\ CongA E G B G H D /\ RT B G H G H D)) by (conclude proposition_29).
close.
Qed.

End Euclid.


