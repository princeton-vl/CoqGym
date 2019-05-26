Require Export GeoCoq.Elements.OriginalProofs.proposition_47B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_squareflip.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_47 : 
   forall A B C D E F G H K, 
   Triangle A B C -> Per B A C -> SQ A B F G -> TS G B A C -> SQ A C K H -> TS H C A B -> SQ B C E D -> TS D C B A ->
   exists X Y, PG B X Y D /\ BetS B X C /\ PG X C E Y /\ BetS D Y E /\ EF A B F G B X Y D /\ EF A C K H X C E Y.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M L, (PG B M L D /\ BetS B M C /\ PG M C E L /\ BetS D L E /\ BetS L M A /\ Per D L A /\ EF A B F G B M L D)) by (conclude proposition_47B);destruct Tf as [M[L]];spliter.
assert (nCol A B C) by (conclude_def Triangle ).
assert (nCol A C B) by (forward_using lemma_NCorder).
assert (Triangle A C B) by (conclude_def Triangle ).
assert (Per C A B) by (conclude lemma_8_2).
assert (SQ C B D E) by (conclude lemma_squareflip).
assert (TS D B C A) by (conclude lemma_oppositesideflip).
assert (PG B C E D) by (conclude lemma_squareparallelogram).
assert (Par B C E D) by (conclude_def PG ).
assert (TP B C E D) by (conclude lemma_paralleldef2B).
assert (OS E D B C) by (conclude_def TP ).
assert (TS E B C A) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists m l, (PG C m l E /\ BetS C m B /\ PG m B D l /\ BetS E l D /\ BetS l m A /\ Per E l A /\ EF A C K H C m l E)) by (conclude proposition_47B);destruct Tf as [m[l]];spliter.
assert (neq E D) by (forward_using lemma_betweennotequal).
assert (neq D E) by (conclude lemma_inequalitysymmetric).
assert (Col E l D) by (conclude_def Col ).
assert (Col D L E) by (conclude_def Col ).
assert (Col D E L) by (forward_using lemma_collinearorder).
assert (Col D E l) by (forward_using lemma_collinearorder).
assert (Col E l L) by (conclude lemma_collinear4).
assert (neq L E) by (forward_using lemma_betweennotequal).
assert (neq E L) by (conclude lemma_inequalitysymmetric).
assert (Per E L A) by (conclude lemma_collinearright).
assert (eq l L) by (conclude lemma_droppedperpendicularunique).
assert (eq L l) by (conclude lemma_equalitysymmetric).
assert (BetS L m A) by (conclude cn_equalitysub).
assert (BetS C M B) by (conclude axiom_betweennesssymmetry).
assert (Col L m A) by (conclude_def Col ).
assert (Col L M A) by (conclude_def Col ).
assert (Col L A m) by (forward_using lemma_collinearorder).
assert (Col L A M) by (forward_using lemma_collinearorder).
assert (neq L A) by (forward_using lemma_betweennotequal).
assert (Col A m M) by (conclude lemma_collinear4).
assert (Col M m A) by (forward_using lemma_collinearorder).
assert (Col B M C) by (conclude_def Col ).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (Col C m B) by (conclude_def Col ).
assert (Col C B m) by (forward_using lemma_collinearorder).
assert (neq C B) by (forward_using lemma_betweennotequal).
assert (Col B M m) by (conclude lemma_collinear4).
assert (Col M m B) by (forward_using lemma_collinearorder).
assert (~ neq M m).
 {
 intro.
 assert (Col m M A) by (forward_using lemma_collinearorder).
 assert (Col m M B) by (forward_using lemma_collinearorder).
 assert (neq m M) by (conclude lemma_inequalitysymmetric).
 assert (Col M A B) by (conclude lemma_collinear4).
 assert (Col M B A) by (forward_using lemma_collinearorder).
 assert (Col M B C) by (forward_using lemma_collinearorder).
 assert (neq M B) by (forward_using lemma_betweennotequal).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (EF A C K H C M l E) by (conclude cn_equalitysub).
assert (EF A C K H C M L E) by (conclude cn_equalitysub).
assert (EF A C K H M C E L) by (forward_using axiom_EFpermutation).
close.
Qed.

End Euclid.


