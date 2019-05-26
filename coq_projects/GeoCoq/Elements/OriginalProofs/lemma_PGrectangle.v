Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equaltorightisright.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplementofright.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_PGrectangle : 
   forall A B C D, 
   PG A C D B -> Per B A C ->
   RE A C D B.
Proof.
intros.
assert ((Cong A B C D /\ Cong A C B D /\ CongA C A B B D C /\ CongA A B D D C A /\ Cong_3 C A B B D C)) by (conclude proposition_34).
assert (Par A C D B) by (conclude_def PG ).
assert (nCol A C B) by (forward_using lemma_parallelNC).
assert (nCol A B C) by (forward_using lemma_NCorder).
assert (nCol C A B) by (forward_using lemma_NCorder).
assert (CongA C A B B A C) by (conclude lemma_ABCequalsCBA).
assert (Per C A B) by (conclude lemma_8_2).
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (CongA B A C C A B) by (conclude lemma_equalanglessymmetric).
assert (CongA B A C B D C) by (conclude lemma_equalanglestransitive).
assert (CongA B D C B A C) by (conclude lemma_equalanglessymmetric).
assert (Per B D C) by (conclude lemma_equaltorightisright).
assert (Per C D B) by (conclude lemma_8_2).
assert (Par A C B D) by (forward_using lemma_parallelflip).
assert (Par A B C D) by (conclude_def PG ).
assert (TP A B C D) by (conclude lemma_paralleldef2B).
assert (OS C D A B) by (conclude_def TP ).
assert (neq C A) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists E, (BetS B A E /\ Cong A E A B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (BetS E A B) by (conclude axiom_betweennesssymmetry).
assert (RT C A B A B D) by (conclude proposition_29C).
let Tf:=fresh in
assert (Tf:exists p q r s t, (Supp p q r s t /\ CongA C A B p q r /\ CongA A B D s q t)) by (conclude_def RT );destruct Tf as [p[q[r[s[t]]]]];spliter.
assert (CongA p q r C A B) by (conclude lemma_equalanglessymmetric).
assert (Per p q r) by (conclude lemma_equaltorightisright).
assert (Per s q t) by (conclude lemma_supplementofright).
assert (CongA s q t A B D) by (conclude lemma_equalanglessymmetric).
assert (Per A B D) by (conclude lemma_equaltorightisright).
assert (Per D B A) by (conclude lemma_8_2).
assert (CongA D C A A B D) by (conclude lemma_equalanglessymmetric).
assert (Per D C A) by (conclude lemma_equaltorightisright).
assert (Per A C D) by (conclude lemma_8_2).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M D /\ BetS C M B)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (neq C B) by (forward_using lemma_betweennotequal).
assert (CR A D C B) by (conclude_def CR ).
assert (RE A C D B) by (conclude_def RE ).
close.
Qed.

End Euclid.


