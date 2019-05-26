Require Export GeoCoq.Elements.OriginalProofs.proposition_47.
Require Export GeoCoq.Elements.OriginalProofs.lemma_squaresequal.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rectanglerotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paste5.
Require Export GeoCoq.Elements.OriginalProofs.proposition_48A.
Require Export GeoCoq.Elements.OriginalProofs.proposition_08.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_48 : 
   forall A B C D E F G H K L M, 
   Triangle A B C -> SQ A B F G -> SQ A C K H -> SQ B C E D -> BetS B M C -> BetS E L D -> EF A B F G B M L D -> EF A C K H M C E L -> RE M C E L ->
   Per B A C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq A C) by (forward_using lemma_NCdistinct).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists R, (BetS B A R /\ Cong A R A B)) by (conclude lemma_extension);destruct Tf as [R];spliter.
assert (Col B A R) by (conclude_def Col ).
assert (Col A B R) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (neq B R) by (forward_using lemma_betweennotequal).
assert (neq R B) by (conclude lemma_inequalitysymmetric).
assert (nCol R B C) by (conclude lemma_NChelper).
assert (nCol B R C) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists Q, (Per B A Q /\ TS Q B R C)) by (conclude proposition_11B);destruct Tf as [Q];spliter.
assert (nCol B A Q) by (conclude lemma_rightangleNC).
assert (neq A Q) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists c, (Out A Q c /\ Cong A c A C)) by (conclude lemma_layoff);destruct Tf as [c];spliter.
assert (Per B A c) by (conclude lemma_8_3).
assert (nCol B A c) by (conclude lemma_rightangleNC).
assert (nCol A B c) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists f g, (SQ A B f g /\ TS g A B c /\ PG A B f g)) by (conclude proposition_46);destruct Tf as [f[g]];spliter.
assert (neq A c) by (forward_using lemma_NCdistinct).
assert (nCol A c B) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists k h, (SQ A c k h /\ TS h A c B /\ PG A c k h)) by (conclude proposition_46);destruct Tf as [k[h]];spliter.
assert (neq B c) by (forward_using lemma_NCdistinct).
assert (nCol B c A) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists e d, (SQ B c e d /\ TS d B c A /\ PG B c e d)) by (conclude proposition_46);destruct Tf as [e[d]];spliter.
assert (Triangle A B c) by (conclude_def Triangle ).
assert (TS g B A c) by (conclude lemma_oppositesideflip).
assert (TS h c A B) by (conclude lemma_oppositesideflip).
assert (TS d c B A) by (conclude lemma_oppositesideflip).
let Tf:=fresh in
assert (Tf:exists m l, (PG B m l d /\ BetS B m c /\ PG m c e l /\ BetS d l e /\ EF A B f g B m l d /\ EF A c k h m c e l)) by (conclude proposition_47);destruct Tf as [m[l]];spliter.
assert (Cong A C A c) by (conclude lemma_congruencesymmetric).
assert (EF A C K H A c k h) by (conclude lemma_squaresequal).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (EF A B F G A B f g) by (conclude lemma_squaresequal).
assert (EF A B F G B m l d) by (conclude axiom_EFtransitive).
assert (EF B M L D A B F G) by (conclude axiom_EFsymmetric).
assert (EF B M L D B m l d) by (conclude axiom_EFtransitive).
assert (EF M C E L A C K H) by (conclude axiom_EFsymmetric).
assert (EF M C E L A c k h) by (conclude axiom_EFtransitive).
assert (EF M C E L m c e l) by (conclude axiom_EFtransitive).
assert (BetS e l d) by (conclude axiom_betweennesssymmetry).
assert (Per B c e) by (conclude_def SQ ).
assert (neq m c) by (forward_using lemma_betweennotequal).
assert (Col B m c) by (conclude_def Col ).
assert (Col B c m) by (forward_using lemma_collinearorder).
assert (Per m c e) by (conclude lemma_collinearright).
assert (PG c e l m) by (conclude lemma_PGrotate).
assert (RE c e l m) by (conclude lemma_PGrectangle).
assert (RE e l m c) by (conclude lemma_rectanglerotate).
assert (RE l m c e) by (conclude lemma_rectanglerotate).
assert (RE m c e l) by (conclude lemma_rectanglerotate).
assert (EF B C E D B c e d) by (conclude lemma_paste5).
assert (Cong B C B c) by (conclude proposition_48A).
assert (Cong A C A c) by (conclude lemma_congruencesymmetric).
assert (Triangle A B c) by (conclude_def Triangle ).
assert (CongA B A C B A c) by (apply (proposition_08 A B C A B c);auto).
assert (Per B A C) by (conclude lemma_equaltorightisright).
close.
Qed.

End Euclid.


