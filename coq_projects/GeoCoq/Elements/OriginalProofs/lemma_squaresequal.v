Require Export GeoCoq.Elements.OriginalProofs.lemma_squarerectangle.

Section Euclid.

Context `{Ax1:area}.


Lemma lemma_squaresequal : 
   forall A B C D a b c d, 
   Cong A B a b -> SQ A B C D -> SQ a b c d ->
   EF A B C D a b c d.
Proof.
intros.
assert (Per D A B) by (conclude_def SQ ).
assert (Per d a b) by (conclude_def SQ ).
assert (CongA D A B d a b) by (conclude lemma_Euclid4).
assert (Cong A B D A) by (conclude_def SQ ).
assert (Cong a b d a) by (conclude_def SQ ).
assert (Cong D A A B) by (conclude lemma_congruencesymmetric).
assert (Cong D A a b) by (conclude lemma_congruencetransitive).
assert (Cong D A d a) by (conclude lemma_congruencetransitive).
assert (PG A B C D) by (conclude lemma_squareparallelogram).
assert (PG a b c d) by (conclude lemma_squareparallelogram).
assert (Par A B C D) by (conclude_def PG ).
assert (Par a b c d) by (conclude_def PG ).
assert (nCol A B D) by (forward_using lemma_parallelNC).
assert (nCol a b d) by (forward_using lemma_parallelNC).
assert (Cong A D a d) by (forward_using lemma_congruenceflip).
assert (Cong D B d b) by (conclude proposition_04).
assert (Cong B D b d) by (forward_using lemma_congruenceflip).
assert (Triangle A B D) by (conclude_def Triangle ).
assert (Cong_3 A B D a b d) by (conclude_def Cong_3 ).
assert (ET A B D a b d) by (conclude axiom_congruentequal).
assert (ET A B D b d a) by (forward_using axiom_ETpermutation).
assert (ET b d a A B D) by (conclude axiom_ETsymmetric).
assert (ET b d a B D A) by (forward_using axiom_ETpermutation).
assert (ET B D A b d a) by (conclude axiom_ETsymmetric).
assert (Cong A B B C) by (conclude_def SQ ).
assert (Cong a b b c) by (conclude_def SQ ).
assert (Cong A B C D) by (conclude_def SQ ).
assert (Cong a b c d) by (conclude_def SQ ).
assert (Cong B C A B) by (conclude lemma_congruencesymmetric).
assert (Cong B C a b) by (conclude lemma_congruencetransitive).
assert (Cong B C b c) by (conclude lemma_congruencetransitive).
assert (Cong C D A B) by (conclude lemma_congruencesymmetric).
assert (Cong C D a b) by (conclude lemma_congruencetransitive).
assert (Cong C D c d) by (conclude lemma_congruencetransitive).
assert (nCol B C D) by (forward_using lemma_parallelNC).
assert (Triangle B C D) by (conclude_def Triangle ).
assert (Cong_3 B C D b c d) by (conclude_def Cong_3 ).
assert (ET B C D b c d) by (conclude axiom_congruentequal).
assert (ET B C D b d c) by (forward_using axiom_ETpermutation).
assert (ET b d c B C D) by (conclude axiom_ETsymmetric).
assert (ET b d c B D C) by (forward_using axiom_ETpermutation).
assert (ET B D C b d c) by (conclude axiom_ETsymmetric).
assert (RE A B C D) by (conclude lemma_squarerectangle).
assert (CR A C B D) by (conclude_def RE ).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (RE a b c d) by (conclude lemma_squarerectangle).
assert (CR a c b d) by (conclude_def RE ).
let Tf:=fresh in
assert (Tf:exists m, (BetS a m c /\ BetS b m d)) by (conclude_def CR );destruct Tf as [m];spliter.
assert (EF B A D C b a d c) by (conclude axiom_paste3).
assert (EF B A D C a b c d) by (forward_using axiom_EFpermutation).
assert (EF a b c d B A D C) by (conclude axiom_EFsymmetric).
assert (EF a b c d A B C D) by (forward_using axiom_EFpermutation).
assert (EF A B C D a b c d) by (conclude axiom_EFsymmetric).
close.
Qed.

End Euclid.


