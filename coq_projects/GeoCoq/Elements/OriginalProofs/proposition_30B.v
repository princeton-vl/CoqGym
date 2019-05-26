Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29.
Require Export GeoCoq.Elements.OriginalProofs.proposition_28A.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_30B : 
   forall A B C D E F G H K, 
   Par A B E F -> Par C D E F -> BetS G K H -> BetS A G B -> BetS E H F -> BetS C K D -> TS A G H F -> TS C K H F ->
   Par A B C D.
Proof.
intros.
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (neq H G) by (conclude lemma_inequalitysymmetric).
assert (neq K H) by (forward_using lemma_betweennotequal).
assert (neq H K) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists P, (BetS H G P /\ Cong G P G H)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (BetS P G H) by (conclude axiom_betweennesssymmetry).
assert (CongA A G H G H F)
 by (apply (proposition_29 A B E F P G H);auto).
assert (BetS P K H) by (conclude lemma_3_5b).
assert (CongA C K H K H F) by (conclude (proposition_29 C D E F P  )).
assert (BetS H K G) by (conclude axiom_betweennesssymmetry).
assert (Out H K G) by (conclude lemma_ray4).
assert (Out H G K) by (conclude lemma_ray5).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (neq H F) by (forward_using lemma_betweennotequal).
assert (Out H F F) by (conclude lemma_ray4).
assert (CongA A G H K H F) by (conclude lemma_equalangleshelper).
assert (CongA K H F A G H) by (conclude lemma_equalanglessymmetric).
assert (CongA C K H A G H) by (conclude lemma_equalanglestransitive).
assert (neq G H) by (forward_using lemma_betweennotequal).
assert (Out G H K) by (conclude lemma_ray4).
assert (neq A G) by (forward_using lemma_betweennotequal).
assert (neq G A) by (conclude lemma_inequalitysymmetric).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Out G A A) by (conclude lemma_ray4).
assert (CongA C K H A G K) by (conclude lemma_equalangleshelper).
assert (CongA H K C K G A) by (conclude lemma_equalanglesflip).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M F /\ Col G H M /\ nCol G H A)) by (conclude_def TS );destruct Tf as [M];spliter.
let Tf:=fresh in
assert (Tf:exists m, (BetS C m F /\ Col K H m /\ nCol K H C)) by (conclude_def TS );destruct Tf as [m];spliter.
assert (Col G K H) by (conclude_def Col ).
assert (Col H G K) by (forward_using lemma_collinearorder).
assert (Col H G M) by (forward_using lemma_collinearorder).
assert (neq H G) by (forward_using lemma_betweennotequal).
assert (Col G K M) by (conclude lemma_collinear4).
assert (Col K G M) by (forward_using lemma_collinearorder).
assert (Col H K m) by (forward_using lemma_collinearorder).
assert (Col H K G) by (forward_using lemma_collinearorder).
assert (neq H K) by (forward_using lemma_betweennotequal).
assert (Col K m G) by (conclude lemma_collinear4).
assert (Col K G m) by (forward_using lemma_collinearorder).
assert (Col G H K) by (forward_using lemma_collinearorder).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Col G H G) by (conclude_def Col ).
assert (neq G K) by (forward_using lemma_betweennotequal).
assert (nCol G K A) by (conclude lemma_NChelper).
assert (nCol K G A) by (forward_using lemma_NCorder).
assert (Col K H G) by (forward_using lemma_collinearorder).
assert (eq K K) by (conclude cn_equalityreflexive).
assert (Col K H K) by (conclude_def Col ).
assert (neq G K) by (forward_using lemma_betweennotequal).
assert (neq K G) by (conclude lemma_inequalitysymmetric).
assert (nCol K G C) by (conclude lemma_NChelper).
assert (OS A C K G) by (conclude_def OS ).
assert (OS C A K G) by (forward_using lemma_samesidesymmetric).
assert (BetS D K C) by (conclude axiom_betweennesssymmetry).
assert (BetS B G A) by (conclude axiom_betweennesssymmetry).
assert (Par D C B A) by (conclude proposition_28A).
assert (Par C D A B) by (forward_using lemma_parallelflip).
assert (Par A B C D) by (conclude lemma_parallelsymmetric).
close.
Qed.

End Euclid.


