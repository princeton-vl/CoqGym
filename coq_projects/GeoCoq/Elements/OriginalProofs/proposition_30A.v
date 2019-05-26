Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_30A : 
   forall A B C D E F G H K, 
   Par A B E F -> Par C D E F -> BetS G H K -> BetS A G B -> BetS E H F -> BetS C K D -> TS A G H F -> TS F H K C ->
   Par A B C D.
Proof.
intros.
assert (Par E F C D) by (conclude lemma_parallelsymmetric).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (neq H G) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists P, (BetS H G P /\ Cong G P G H)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (BetS P G H) by (conclude axiom_betweennesssymmetry).
assert (BetS P G K) by (conclude lemma_3_7b).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M F /\ Col G H M /\ nCol G H A)) by (conclude_def TS );destruct Tf as [M];spliter.
let Tf:=fresh in
assert (Tf:exists N, (BetS F N C /\ Col H K N /\ nCol H K F)) by (conclude_def TS );destruct Tf as [N];spliter.
assert (~ Meet C D E F) by (conclude_def Par ).
assert (nCol G H A) by (conclude_def TS ).
assert (neq A G) by (forward_using lemma_betweennotequal).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (nCol A G H) by (forward_using lemma_NCorder).
assert (CongA A G H G H F) by (conclude (proposition_29 A B E F P G H)).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out G A A) by (conclude lemma_ray4).
assert (Out G H K) by (conclude lemma_ray4).
assert (CongA A G H A G H) by (conclude lemma_equalanglesreflexive).
assert (CongA A G H A G K) by (conclude lemma_equalangleshelper).
assert (CongA A G K A G H) by (conclude lemma_equalanglessymmetric).
assert (CongA A G K G H F) by (conclude lemma_equalanglestransitive).
assert (BetS C N F) by (conclude axiom_betweennesssymmetry).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (nCol F H K) by (forward_using lemma_NCorder).
assert (Col E H F) by (conclude_def Col ).
assert (Col F H E) by (forward_using lemma_collinearorder).
assert (Col F H H) by (conclude_def Col ).
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (nCol E H K) by (conclude lemma_NChelper).
assert (Col E H F) by (conclude_def Col ).
assert (Col E H H) by (conclude_def Col ).
assert (neq H F) by (forward_using lemma_betweennotequal).
assert (neq F H) by (conclude lemma_inequalitysymmetric).
assert (nCol F H K) by (conclude lemma_NChelper).
assert (nCol H K F) by (forward_using lemma_NCorder).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col H K H) by (conclude_def Col ).
assert (Col K H N) by (forward_using lemma_collinearorder).
assert (Col C K D) by (conclude_def Col ).
assert (Col E H F) by (conclude_def Col ).
assert (neq C K) by (forward_using lemma_betweennotequal).
assert (neq C D) by (forward_using lemma_betweennotequal).
assert (neq H F) by (forward_using lemma_betweennotequal).
assert (neq E F) by (forward_using lemma_betweennotequal).
assert (BetS K N H) by (conclude lemma_collinearbetween).
assert (neq N H) by (forward_using lemma_betweennotequal).
assert (neq H N) by (conclude lemma_inequalitysymmetric).
assert (nCol H N F) by (conclude lemma_NChelper).
assert (nCol F N H) by (forward_using lemma_NCorder).
assert (BetS F N C) by (conclude axiom_betweennesssymmetry).
assert (Col F N C) by (conclude_def Col ).
assert (eq N N) by (conclude cn_equalityreflexive).
assert (Col F N N) by (conclude_def Col ).
assert (neq C N) by (forward_using lemma_betweennotequal).
assert (nCol C N H) by (conclude lemma_NChelper).
assert (nCol H N C) by (forward_using lemma_NCorder).
assert (BetS H N K) by (conclude axiom_betweennesssymmetry).
assert (Col H N K) by (conclude_def Col ).
assert (Col H N H) by (conclude_def Col ).
assert (neq H K) by (forward_using lemma_betweennotequal).
assert (nCol H K C) by (conclude lemma_NChelper).
assert (nCol H K E) by (forward_using lemma_NCorder).
assert (OS E C H K) by (conclude_def OS ).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (Col H K K) by (conclude_def Col ).
assert (TS C H K D) by (conclude_def TS ).
assert (TS E H K D) by (conclude lemma_planeseparation).
assert (CongA G H F H K D) by (conclude proposition_29).
assert (nCol C K H) by (forward_using lemma_NCorder).
assert (Col C K D) by (conclude_def Col ).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (Col C K K) by (conclude_def Col ).
assert (neq K D) by (forward_using lemma_betweennotequal).
assert (neq D K) by (conclude lemma_inequalitysymmetric).
assert (nCol D K H) by (conclude lemma_NChelper).
assert (nCol H K D) by (forward_using lemma_NCorder).
assert (CongA H K D H K D) by (conclude lemma_equalanglesreflexive).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Out K D D) by (conclude lemma_ray4).
assert (BetS K H G) by (conclude axiom_betweennesssymmetry).
assert (neq K H) by (forward_using lemma_betweennotequal).
assert (Out K H G) by (conclude lemma_ray4).
assert (CongA H K D G K D) by (conclude lemma_equalangleshelper).
assert (CongA G H F G K D) by (conclude lemma_equalanglestransitive).
assert (CongA A G K G K D) by (conclude lemma_equalanglestransitive).
assert (Col G H K) by (conclude_def Col ).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (Col H M K) by (conclude lemma_collinear4).
assert (Col H K M) by (forward_using lemma_collinearorder).
assert (Col H K G) by (forward_using lemma_collinearorder).
assert (neq H K) by (forward_using lemma_betweennotequal).
assert (Col K M G) by (conclude lemma_collinear4).
assert (Col G K M) by (forward_using lemma_collinearorder).
assert (Col H K G) by (forward_using lemma_collinearorder).
assert (Col K N G) by (conclude lemma_collinear4).
assert (Col G K N) by (forward_using lemma_collinearorder).
assert (nCol A G K) by (conclude lemma_equalanglesNC).
assert (nCol G K A) by (forward_using lemma_NCorder).
assert (nCol H K C) by (forward_using lemma_NCorder).
assert (Col H K G) by (forward_using lemma_collinearorder).
assert (Col H K K) by (conclude_def Col ).
assert (neq G K) by (forward_using lemma_betweennotequal).
assert (nCol G K C) by (conclude lemma_NChelper).
assert (OS A C G K) by (conclude_def OS ).
assert (Col G K K) by (conclude_def Col ).
assert (TS C G K D) by (conclude_def TS ).
assert (TS A G K D) by (conclude lemma_planeseparation).
assert (Par A B C D) by (conclude proposition_27).
close.
Qed.

End Euclid.


