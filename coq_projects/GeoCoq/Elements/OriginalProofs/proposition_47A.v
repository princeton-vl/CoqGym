Require Export GeoCoq.Elements.OriginalProofs.lemma_squareparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesideflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_erectedperpendicularunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_twoperpsparallel.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_altitudeofrighttriangle.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_47A : 
   forall A B C D E, 
   Triangle A B C -> Per B A C -> SQ B C E D -> TS D C B A ->
   exists X Y, PG B X Y D /\ BetS B X C /\ PG X C E Y /\ BetS D Y E /\ BetS Y X A /\ Per D Y A.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists N, (BetS D N A /\ Col C B N /\ nCol C B D)) by (conclude_def TS );destruct Tf as [N];spliter.
assert (Per C A B) by (conclude lemma_8_2).
assert (nCol C A B) by (conclude lemma_rightangleNC).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (Cong B C E D) by (conclude_def SQ ).
assert (neq E D) by (conclude axiom_nocollapse).
assert (neq D E) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists q, (BetS D q A /\ Col C B q /\ nCol C B D)) by (conclude_def TS );destruct Tf as [q];spliter.
assert (PG B C E D) by (conclude lemma_squareparallelogram).
assert (Par B C E D) by (conclude_def PG ).
assert (~ Meet B C E D) by (conclude_def Par ).
assert (~ eq A E).
 {
 intro.
 assert (BetS D q E) by (conclude cn_equalitysub).
 assert (Col D q E) by (conclude_def Col ).
 assert (Col E D q) by (forward_using lemma_collinearorder).
 assert (Col B C q) by (forward_using lemma_collinearorder).
 assert (Meet B C E D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col D E A).
 {
 intro.
 assert (Col D A E) by (forward_using lemma_collinearorder).
 assert (Col D q A) by (conclude_def Col ).
 assert (Col D A q) by (forward_using lemma_collinearorder).
 assert (neq D A) by (forward_using lemma_betweennotequal).
 assert (Col A E q) by (conclude lemma_collinear4).
 assert (Col q A E) by (forward_using lemma_collinearorder).
 assert (Col q A D) by (forward_using lemma_collinearorder).
 assert (neq q A) by (forward_using lemma_betweennotequal).
 assert (Col A E D) by (conclude lemma_collinear4).
 assert (Col A E q) by (forward_using lemma_collinearorder).
 assert (Col E D q) by (conclude lemma_collinear4).
 assert (Col B C q) by (forward_using lemma_collinearorder).
 assert (Meet B C E D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists L, Perp_at A L D E L) by (conclude proposition_12);destruct Tf as [L];spliter.
let Tf:=fresh in
assert (Tf:exists p, (Col A L L /\ Col D E L /\ Col D E p /\ Per p L A)) by (conclude_def Perp_at );destruct Tf as [p];spliter.
assert (Per A L p) by (conclude lemma_8_2).
assert (~ eq B N).
 {
 intro.
 assert (BetS D B A) by (conclude cn_equalitysub).
 assert (Col D B A) by (conclude_def Col ).
  assert (Per D B C) by (conclude_def SQ ).
 assert (Per A B C) by (conclude lemma_collinearright).
 assert (~ Per C A B) by (conclude lemma_8_7).
 assert (Per C A B) by (conclude lemma_8_2).
 contradict.
 }
assert (Par B C E D) by (conclude_def PG ).
assert (Par B C D E) by (forward_using lemma_parallelflip).
assert (Par D E B C) by (conclude lemma_parallelsymmetric).
assert (Par D E C B) by (forward_using lemma_parallelflip).
assert (neq N B) by (conclude lemma_inequalitysymmetric).
assert (Par D E N B) by (conclude lemma_collinearparallel).
assert (Par D E B N) by (forward_using lemma_parallelflip).
assert (TP D E B N) by (conclude lemma_paralleldef2B).
assert (OS B N D E) by (conclude_def TP ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col D D E) by (conclude_def Col ).
assert (neq D N) by (forward_using lemma_betweennotequal).
assert (Out D N A) by (conclude lemma_ray4).
assert (OS B A D E) by (conclude lemma_sameside2).
assert (OS B A E D) by (conclude lemma_samesideflip).
assert (OS A B E D) by (forward_using lemma_samesidesymmetric).
assert (~ eq D L).
 {
 intro.
 assert (Per A D p) by (conclude cn_equalitysub).
 assert (Per p D A) by (conclude lemma_8_2).
 assert (Col p D E) by (forward_using lemma_collinearorder).
 assert (Per E D A) by (conclude lemma_collinearright).
 assert (Per E D B) by (conclude_def SQ ).
 assert (Out D A B) by (conclude lemma_erectedperpendicularunique).
 assert (Col D A B) by (conclude lemma_rayimpliescollinear).
 assert (Col A D B) by (forward_using lemma_collinearorder).
 assert (Col D N A) by (conclude_def Col ).
 assert (Col A D N) by (forward_using lemma_collinearorder).
 assert (neq D A) by (forward_using lemma_betweennotequal).
 assert (neq A D) by (conclude lemma_inequalitysymmetric).
 assert (Col D B N) by (conclude lemma_collinear4).
 assert (Col N B C) by (forward_using lemma_collinearorder).
 assert (Col N B D) by (forward_using lemma_collinearorder).
 assert (Col B C D) by (conclude lemma_collinear4).
 assert (nCol B C D) by (forward_using lemma_NCorder).
 contradict.
 }
assert (neq L D) by (conclude lemma_inequalitysymmetric).
assert (Par B C E D) by (forward_using lemma_parallelflip).
assert (Col E D L) by (forward_using lemma_collinearorder).
assert (Par B C L D) by (conclude lemma_collinearparallel).
assert (Par L D B C) by (conclude lemma_parallelsymmetric).
assert (TP B C L D) by (conclude lemma_paralleldef2B).
assert (OS L D B C) by (conclude_def TP ).
assert (nCol B C D) by (forward_using lemma_parallelNC).
assert (Col B C N) by (forward_using lemma_collinearorder).
assert (TS D B C A) by (conclude_def TS ).
assert (TS L B C A) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists M, (BetS L M A /\ Col B C M /\ nCol B C L)) by (conclude_def TS );destruct Tf as [M];spliter.
assert (neq D E) by (forward_using lemma_NCdistinct).
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (neq L M) by (forward_using lemma_betweennotequal).
assert (Out L M A) by (conclude lemma_ray4).
assert (Out L A M) by (conclude lemma_ray5).
assert (Per E D B) by (conclude_def SQ ).
assert (Col E D p) by (forward_using lemma_collinearorder).
assert (Col E D L) by (forward_using lemma_collinearorder).
assert (Col D p L) by (conclude lemma_collinear4).
assert (Col p L D) by (forward_using lemma_collinearorder).
assert (Per D L A) by (conclude lemma_collinearright).
assert (Per D L M) by (conclude lemma_8_3).
assert (~ eq B M).
 {
 intro.
 assert (Per D L B) by (conclude cn_equalitysub).
 assert (Per L D B) by (conclude lemma_collinearright).
 assert (Per B D L) by (conclude lemma_8_2).
 assert (~ Per B D L) by (conclude lemma_8_7).
 contradict.
 }
assert (neq M B) by (conclude lemma_inequalitysymmetric).
assert (Par L D C B) by (forward_using lemma_parallelflip).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (Par L D M B) by (conclude lemma_collinearparallel).
assert (Par L D B M) by (forward_using lemma_parallelflip).
assert (Par B M L D) by (conclude lemma_parallelsymmetric).
assert (Par B M D L) by (forward_using lemma_parallelflip).
assert (Par D L B M) by (conclude lemma_parallelsymmetric).
assert (TP D L B M) by (conclude lemma_paralleldef2B).
assert (OS B M D L) by (conclude_def TP ).
assert (Par B M L D) by (conclude lemma_parallelsymmetric).
assert (Per L D B) by (conclude lemma_collinearright).
assert (Per B D L) by (conclude lemma_8_2).
assert (Par B D L M) by (conclude lemma_twoperpsparallel).
assert (Par B D M L) by (forward_using lemma_parallelflip).
assert (PG B M L D) by (conclude_def PG ).
assert (Par M L B D) by (conclude lemma_parallelsymmetric).
assert (TP M L B D) by (conclude lemma_paralleldef2B).
assert (OS B D M L) by (conclude_def TP ).
assert (BetS A M L) by (conclude axiom_betweennesssymmetry).
assert (Par M B L D) by (forward_using lemma_parallelflip).
assert (CongA A M B M L D) by (conclude proposition_29C).
assert (Per M L D) by (conclude lemma_8_2).
assert (Per A M B) by (conclude lemma_equaltorightisright).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B C B) by (conclude_def Col ).
assert (BetS B M C) by (conclude lemma_altitudeofrighttriangle).
assert (~ eq M C).
 {
 intro.
 assert (Per A C B) by (conclude cn_equalitysub).
 assert (~ Per B A C) by (conclude lemma_8_7).
 contradict.
 }
assert (~ eq L E).
 {
 intro.
 assert (Par B D C E) by (conclude_def PG ).
 assert (Par C E B D) by (conclude lemma_parallelsymmetric).
 assert (Par M E B D) by (conclude cn_equalitysub).
 assert (Par B D M E) by (conclude lemma_parallelsymmetric).
 assert (Par B D C E) by (conclude lemma_parallelsymmetric).
 assert (Par B D E C) by (forward_using lemma_parallelflip).
 assert (Par B D E M) by (forward_using lemma_parallelflip).
 assert (Col E C M) by (conclude lemma_Playfair).
 assert (Col M C E) by (forward_using lemma_collinearorder).
 assert (Col M C B) by (forward_using lemma_collinearorder).
 assert (Col C E B) by (conclude lemma_collinear4).
 assert (Col B C E) by (forward_using lemma_collinearorder).
 assert (nCol B C E) by (forward_using lemma_parallelNC).
 contradict.
 }
assert (Par B M L D) by (conclude_def PG ).
assert (Par B M D L) by (forward_using lemma_parallelflip).
assert (Col D L E) by (forward_using lemma_collinearorder).
assert (neq E L) by (conclude lemma_inequalitysymmetric).
assert (Par B M E L) by (conclude lemma_collinearparallel).
assert (Par E L B M) by (conclude lemma_parallelsymmetric).
assert (Col B M C) by (forward_using lemma_collinearorder).
assert (neq C M) by (conclude lemma_inequalitysymmetric).
assert (Par E L C M) by (conclude lemma_collinearparallel).
assert (Par C M E L) by (conclude lemma_parallelsymmetric).
assert (Par M C E L) by (forward_using lemma_parallelflip).
assert (Col D L E) by (forward_using lemma_collinearorder).
assert (Per E L M) by (conclude lemma_collinearright).
assert (Per M L E) by (conclude lemma_8_2).
assert (Per C E D) by (conclude_def SQ ).
assert (Per D E C) by (conclude lemma_8_2).
assert (Per L E C) by (conclude lemma_collinearright).
assert (Par M C L E) by (forward_using lemma_parallelflip).
assert (Par L E M C) by (conclude lemma_parallelsymmetric).
assert (TP L E M C) by (conclude lemma_paralleldef2B).
assert (OS M C L E) by (conclude_def TP ).
assert (Par M L E C) by (conclude lemma_twoperpsparallel).
assert (Par M L C E) by (forward_using lemma_parallelflip).
assert (PG M C E L) by (conclude_def PG ).
assert (Cong B M D L) by (forward_using proposition_34).
assert (Cong M C L E) by (forward_using proposition_34).
assert (Cong B C D E) by (forward_using proposition_34).
assert (BetS D L E) by (conclude lemma_betweennesspreserved).
close.
Qed.

End Euclid.


