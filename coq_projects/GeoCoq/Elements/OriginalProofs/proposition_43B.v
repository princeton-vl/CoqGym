Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleldef2B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesideflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidecollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidetransitive.
Require Export GeoCoq.Elements.OriginalProofs.proposition_28D.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_43B : 
   forall A B C D E F G H K, 
   PG A B C D -> BetS A H D -> BetS A E B -> BetS D F C -> BetS B G C -> PG E A H K -> PG G K F C ->
   PG E K G B.
Proof.
intros.
assert (Par A D B C) by (conclude_def PG ).
assert (Par A B C D) by (conclude_def PG ).
assert (Par E A H K) by (conclude_def PG ).
assert (Par E K A H) by (conclude_def PG ).
assert (Par G K F C) by (conclude_def PG ).
assert (Par F C G K) by (conclude lemma_parallelsymmetric).
assert (Par C F G K) by (forward_using lemma_parallelflip).
assert (Par G C K F) by (conclude_def PG ).
assert (Par B C A D) by (conclude lemma_parallelsymmetric).
assert (Par C D A B) by (conclude lemma_parallelsymmetric).
assert (Par A H E K) by (conclude lemma_parallelsymmetric).
assert (TP A B C D) by (conclude lemma_paralleldef2B).
assert (TP E A H K) by (conclude lemma_paralleldef2B).
assert (TP G C K F) by (conclude lemma_paralleldef2B).
assert (TP B C A D) by (conclude lemma_paralleldef2B).
assert (OS A D B C) by (conclude_def TP ).
assert (OS A D C B) by (conclude lemma_samesideflip).
assert (OS D A C B) by (forward_using lemma_samesidesymmetric).
assert (OS C D A B) by (conclude_def TP ).
assert (OS H K E A) by (conclude_def TP ).
assert (OS K F G C) by (conclude_def TP ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq A H) by (forward_using lemma_betweennotequal).
assert (neq B G) by (forward_using lemma_betweennotequal).
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists e, (BetS B A e /\ Cong A e B A)) by (conclude lemma_extension);destruct Tf as [e];spliter.
assert (BetS e A B) by (conclude axiom_betweennesssymmetry).
assert (OS D C A B) by (forward_using lemma_samesidesymmetric).
assert (RT D A B A B C) by (conclude proposition_29C).
assert (BetS B E A) by (conclude axiom_betweennesssymmetry).
assert (BetS E A e) by (conclude lemma_3_6a).
assert (BetS e A E) by (conclude axiom_betweennesssymmetry).
assert (OS H K A E) by (forward_using lemma_samesidesymmetric).
assert (RT H A E A E K) by (conclude proposition_29C).
assert (Out A E B) by (conclude lemma_ray4).
assert (Out A H D) by (conclude lemma_ray4).
assert (nCol A H E) by (forward_using lemma_parallelNC).
assert (nCol E A H) by (forward_using lemma_NCorder).
assert (CongA E A H E A H) by (conclude lemma_equalanglesreflexive).
assert (CongA E A H B A D) by (conclude lemma_equalangleshelper).
assert (CongA H A E D A B) by (conclude lemma_equalanglesflip).
assert (CongA A E K A B C)  by (apply (lemma_supplements2 H A E A B C D A B A E K);eauto).
assert (OS C D B A) by (conclude lemma_samesideflip).
assert (Col A E B) by (conclude_def Col ).
assert (Col B A E) by (forward_using lemma_collinearorder).
assert (neq E B) by (forward_using lemma_betweennotequal).
assert (neq B E) by (conclude lemma_inequalitysymmetric).
assert (OS C D B E) by (conclude lemma_samesidecollinear).
assert (Out A H D) by (conclude lemma_ray4).
assert (Out A D H) by (conclude lemma_ray5).
assert (OS C H B E) by (conclude lemma_sameside2).
assert (Col E A B) by (forward_using lemma_collinearorder).
assert (OS H K E B) by (conclude lemma_samesidecollinear).
assert (OS H K B E) by (conclude lemma_samesideflip).
assert (OS C K B E) by (conclude lemma_samesidetransitive).
assert (OS K C B E) by (forward_using lemma_samesidesymmetric).
assert (Out B G C) by (conclude lemma_ray4).
assert (Out B C G) by (conclude lemma_ray5).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B B E) by (conclude_def Col ).
assert (OS K G B E) by (conclude lemma_sameside2).
assert (OS K G E B) by (conclude lemma_samesideflip).
assert (Out B E A) by (conclude lemma_ray4).
assert (Out B A E) by (conclude lemma_ray5).
assert (CongA A E K E B G) by (conclude lemma_equalangleshelper).
assert (Par E K B G) by (conclude proposition_28D).
assert (Par E K G B) by (forward_using lemma_parallelflip).
assert (neq B C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists c, (BetS B C c /\ Cong C c B C)) by (conclude lemma_extension);destruct Tf as [c];spliter.
assert (BetS c C B) by (conclude axiom_betweennesssymmetry).
assert (Par C D B A) by (forward_using lemma_parallelflip).
assert (RT D C B C B A) by (conclude proposition_29C).
assert (OS K F C G) by (conclude lemma_samesideflip).
assert (OS F K C G) by (forward_using lemma_samesidesymmetric).
assert (BetS C G B) by (conclude axiom_betweennesssymmetry).
assert (BetS c C G) by (conclude axiom_innertransitivity).
assert (RT F C G C G K) by (conclude proposition_29C).
assert (nCol D B C) by (forward_using lemma_parallelNC).
assert (nCol D C B) by (forward_using lemma_NCorder).
assert (CongA D C B D C B) by (conclude lemma_equalanglesreflexive).
assert (BetS C F D) by (conclude axiom_betweennesssymmetry).
assert (neq C F) by (forward_using lemma_betweennotequal).
assert (Out C F D) by (conclude lemma_ray4).
assert (Out C D F) by (conclude lemma_ray5).
assert (BetS C G B) by (conclude axiom_betweennesssymmetry).
assert (neq C G) by (forward_using lemma_betweennotequal).
assert (Out C G B) by (conclude lemma_ray4).
assert (Out C B G) by (conclude lemma_ray5).
assert (CongA D C B F C G) by (conclude lemma_equalangleshelper).
assert (CongA C B A C G K) by (conclude (lemma_supplements2 D C B C G K F C G C B A)).
assert (CongA C G K C B A) by (conclude lemma_equalanglessymmetric).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out B A A) by (conclude lemma_ray4).
assert (neq B G) by (forward_using lemma_betweennotequal).
assert (Out B G C) by (conclude lemma_ray4).
assert (Out B C G) by (conclude lemma_ray5).
assert (CongA C G K G B A) by (conclude lemma_equalangleshelper).
assert (Col B G C) by (conclude_def Col ).
assert (Col C B G) by (forward_using lemma_collinearorder).
assert (BetS C F D) by (conclude axiom_betweennesssymmetry).
assert (neq C F) by (forward_using lemma_betweennotequal).
assert (Out C F D) by (conclude lemma_ray4).
assert (Out C D F) by (conclude lemma_ray5).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col B C C) by (conclude_def Col ).
assert (OS A F B C) by (conclude lemma_sameside2).
assert (TP G C K F) by (conclude lemma_paralleldef2B).
assert (OS K F G C) by (conclude_def TP ).
assert (Col C G B) by (forward_using lemma_collinearorder).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (OS K F C G) by (conclude lemma_samesideflip).
assert (OS K F C B) by (conclude lemma_samesidecollinear).
assert (OS K F B C) by (conclude lemma_samesideflip).
assert (OS F K B C) by (forward_using lemma_samesidesymmetric).
assert (OS A K B C) by (conclude lemma_samesidetransitive).
assert (OS K A B C) by (forward_using lemma_samesidesymmetric).
assert (Col B C G) by (forward_using lemma_collinearorder).
assert (OS K A B G) by (conclude lemma_samesidecollinear).
assert (OS K A G B) by (conclude lemma_samesideflip).
assert (Par G K B A) by (conclude proposition_28D).
assert (Par G K A B) by (forward_using lemma_parallelflip).
assert (Col A B E) by (forward_using lemma_collinearorder).
assert (Par G K E B) by (conclude lemma_collinearparallel).
assert (Par E B G K) by (conclude lemma_parallelsymmetric).
assert (Par E B K G) by (forward_using lemma_parallelflip).
assert (PG E K G B) by (conclude_def PG ).
close.
Qed.

End Euclid.


