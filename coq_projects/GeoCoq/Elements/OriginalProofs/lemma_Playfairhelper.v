Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidetransitive.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfairhelper : 
   forall A B C D E, 
   Par A B C D -> Par A B C E -> CR A D B C -> CR A E B C ->
   Col C D E.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M, (BetS A M D /\ BetS B M C)) by (conclude_def CR );destruct Tf as [M];spliter.
let Tf:=fresh in
assert (Tf:exists m, (BetS A m E /\ BetS B m C)) by (conclude_def CR );destruct Tf as [m];spliter.
assert (neq B C) by (forward_using lemma_betweennotequal).
assert (BetS E m A) by (conclude axiom_betweennesssymmetry).
assert (BetS D M A) by (conclude axiom_betweennesssymmetry).
assert (Col B M C) by (conclude_def Col ).
assert (Col B m C) by (conclude_def Col ).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (Col C B m) by (forward_using lemma_collinearorder).
assert (nCol B C E) by (forward_using lemma_parallelNC).
assert (nCol C B E) by (forward_using lemma_NCorder).
assert (nCol B C D) by (forward_using lemma_parallelNC).
assert (nCol C B D) by (forward_using lemma_NCorder).
assert (TS E C B A) by (conclude_def TS ).
assert (TS D C B A) by (conclude_def TS ).
assert (Par C D A B) by (conclude lemma_parallelsymmetric).
assert (Par C E A B) by (conclude lemma_parallelsymmetric).
assert (Par E C B A) by (forward_using lemma_parallelflip).
assert (Par D C B A) by (forward_using lemma_parallelflip).
assert (CongA E C B C B A) by (conclude proposition_29B).
assert (CongA D C B C B A) by (conclude proposition_29B).
assert (CongA C B A D C B) by (conclude lemma_equalanglessymmetric).
assert (CongA E C B D C B) by (conclude lemma_equalanglestransitive).
assert (neq C E) by (forward_using lemma_NCdistinct).
assert (neq C D) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists e, (Out C E e /\ Cong C e C D)) by (conclude lemma_layoff);destruct Tf as [e];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Out C B B) by (conclude lemma_ray4).
assert (Cong C B C B) by (conclude cn_congruencereflexive).
assert (nCol E C B) by (forward_using lemma_NCorder).
assert (CongA E C B E C B) by (conclude lemma_equalanglesreflexive).
assert (CongA E C B e C B) by (conclude lemma_equalangleshelper).
assert (CongA e C B E C B) by (conclude lemma_equalanglessymmetric).
assert (CongA e C B D C B) by (conclude lemma_equalanglestransitive).
assert (Col C E e) by (conclude lemma_rayimpliescollinear).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C E C) by (conclude_def Col ).
assert (nCol C E B) by (forward_using lemma_NCorder).
assert (neq C e) by (conclude lemma_raystrict).
assert (nCol C e B) by (conclude lemma_NChelper).
assert (nCol e C B) by (forward_using lemma_NCorder).
assert (Triangle e C B) by (conclude_def Triangle ).
assert (nCol D C B) by (forward_using lemma_NCorder).
assert (Triangle D C B) by (conclude_def Triangle ).
assert (Cong e B D B) by (conclude proposition_04).
assert (nCol B C E) by (forward_using lemma_parallelNC).
assert (nCol C B E) by (forward_using lemma_NCorder).
assert (nCol B C D) by (forward_using lemma_parallelNC).
assert (nCol C B D) by (forward_using lemma_NCorder).
assert (OS E D C B) by (conclude_def OS ).
assert (nCol C B e) by (forward_using lemma_NCorder).
assert (Col C C B) by (conclude_def Col ).
assert (Out C e E) by (conclude lemma_ray5).
assert (OS e e C B) by (conclude lemma_samesidereflexive).
assert (OS e E C B) by (conclude lemma_sameside2).
assert (OS e D C B) by (conclude lemma_samesidetransitive).
assert (Cong e C D C) by (forward_using lemma_congruenceflip).
assert (eq e D) by (conclude proposition_07).
assert (Col C E D) by (conclude cn_equalitysub).
assert (Col C D E) by (forward_using lemma_collinearorder).
close.
Qed.

End Euclid.


