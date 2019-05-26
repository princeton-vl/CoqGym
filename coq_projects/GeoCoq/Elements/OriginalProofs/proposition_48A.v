Require Export GeoCoq.Elements.OriginalProofs.lemma_squarerectangle.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_48A : 
   forall A B C D a b c d, 
   SQ A B C D -> SQ a b c d -> EF A B C D a b c d ->
   Cong A B a b.
Proof.
intros.
assert (PG A B C D) by (conclude lemma_squareparallelogram).
assert (PG a b c d) by (conclude lemma_squareparallelogram).
assert (Cong_3 B A D D C B) by (conclude proposition_34).
assert (Cong_3 b a d d c b) by (conclude proposition_34).
assert (ET B A D D C B) by (conclude axiom_congruentequal).
assert (ET b a d d c b) by (conclude axiom_congruentequal).
assert (ET B A D B D C) by (forward_using axiom_ETpermutation).
assert (ET B D C B A D) by (conclude axiom_ETsymmetric).
assert (ET B D C A B D) by (forward_using axiom_ETpermutation).
assert (ET A B D B D C) by (conclude axiom_ETsymmetric).
assert (ET b a d b d c) by (forward_using axiom_ETpermutation).
assert (ET b d c b a d) by (conclude axiom_ETsymmetric).
assert (ET b d c a b d) by (forward_using axiom_ETpermutation).
assert (ET a b d b d c) by (conclude axiom_ETsymmetric).
assert (RE A B C D) by (conclude lemma_squarerectangle).
assert (RE a b c d) by (conclude lemma_squarerectangle).
assert (CR A C B D) by (conclude_def RE ).
assert (CR a c b d) by (conclude_def RE ).
assert (Par A B C D) by (conclude_def PG ).
assert (nCol A B D) by (forward_using lemma_parallelNC).
assert (Par a b c d) by (conclude_def PG ).
assert (nCol a b d) by (forward_using lemma_parallelNC).
assert (TS A B D C) by (forward_using lemma_crossimpliesopposite).
assert (TS a b d c) by (forward_using lemma_crossimpliesopposite).
assert (ET A B D a b d) by (conclude axiom_halvesofequals).
assert (Cong a b d a) by (conclude_def SQ ).
assert (Cong A B D A) by (conclude_def SQ ).
assert (Cong a b a d) by (forward_using lemma_congruenceflip).
assert (Cong A B A D) by (forward_using lemma_congruenceflip).
assert (~ Lt a b A B).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists E, (BetS A E B /\ Cong A E a b)) by (conclude_def Lt );destruct Tf as [E];spliter.
 assert (Lt a d A B) by (conclude lemma_lessthancongruence2).
 assert (Lt a d A D) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS A F D /\ Cong A F a d)) by (conclude_def Lt );destruct Tf as [F];spliter.
 assert (Per D A B) by (conclude_def SQ ).
 assert (Per d a b) by (conclude_def SQ ).
 assert (neq A D) by (forward_using lemma_betweennotequal).
 assert (neq A B) by (forward_using lemma_betweennotequal).
 assert (Out A D F) by (conclude lemma_ray4).
 assert (Out A B E) by (conclude lemma_ray4).
 assert (nCol D A B) by (forward_using lemma_NCorder).
 assert (CongA D A B D A B) by (conclude lemma_equalanglesreflexive).
 assert (CongA D A B F A E) by (conclude lemma_equalangleshelper).
 assert (CongA F A E D A B) by (conclude lemma_equalanglessymmetric).
 assert (Per F A E) by (conclude lemma_equaltorightisright).
 assert (CongA F A E d a b) by (conclude lemma_Euclid4).
 assert (Cong F E d b) by (conclude proposition_04).
 assert (Cong F A d a) by (forward_using lemma_congruenceflip).
 assert (Cong_3 F A E d a b) by (conclude_def Cong_3 ).
 assert (ET F A E d a b) by (conclude axiom_congruentequal).
 assert (ET F A E a b d) by (forward_using axiom_ETpermutation).
 assert (ET a b d A B D) by (conclude axiom_ETsymmetric).
 assert (ET F A E A B D) by (conclude axiom_ETtransitive).
 assert (ET F A E D A B) by (forward_using axiom_ETpermutation).
 assert (ET D A B F A E) by (conclude axiom_ETsymmetric).
 assert (Triangle D A B) by (conclude_def Triangle ).
 assert (~ ET D A B F A E) by (conclude axiom_deZolt2).
 contradict.
 }
assert (~ Lt A B a b).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists e, (BetS a e b /\ Cong a e A B)) by (conclude_def Lt );destruct Tf as [e];spliter.
 assert (Lt A D a b) by (conclude lemma_lessthancongruence2).
 assert (Lt A D a d) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists f, (BetS a f d /\ Cong a f A D)) by (conclude_def Lt );destruct Tf as [f];spliter.
 assert (Per d a b) by (conclude_def SQ ).
 assert (Per D A B) by (conclude_def SQ ).
 assert (neq a d) by (forward_using lemma_betweennotequal).
 assert (neq a b) by (forward_using lemma_betweennotequal).
 assert (Out a d f) by (conclude lemma_ray4).
 assert (Out a b e) by (conclude lemma_ray4).
 assert (nCol d a b) by (forward_using lemma_NCorder).
 assert (CongA d a b d a b) by (conclude lemma_equalanglesreflexive).
 assert (CongA d a b f a e) by (conclude lemma_equalangleshelper).
 assert (CongA f a e d a b) by (conclude lemma_equalanglessymmetric).
 assert (Per f a e) by (conclude lemma_equaltorightisright).
 assert (CongA f a e D A B) by (conclude lemma_Euclid4).
 assert (Cong f e D B) by (conclude proposition_04).
 assert (Cong f a D A) by (forward_using lemma_congruenceflip).
 assert (Cong_3 f a e D A B) by (conclude_def Cong_3 ).
 assert (ET f a e D A B) by (conclude axiom_congruentequal).
 assert (ET f a e A B D) by (forward_using axiom_ETpermutation).
 assert (ET A B D f a e) by (conclude axiom_ETsymmetric).
 assert (ET f a e a b d) by (conclude axiom_ETtransitive).
 assert (ET f a e d a b) by (forward_using axiom_ETpermutation).
 assert (ET d a b f a e) by (conclude axiom_ETsymmetric).
 assert (Triangle d a b) by (conclude_def Triangle ).
 assert (~ ET d a b f a e) by (conclude axiom_deZolt2).
 contradict.
 }
assert (neq A B) by (forward_using lemma_NCdistinct).
assert (neq a b) by (forward_using lemma_NCdistinct).
assert (Cong A B a b) by (conclude lemma_trichotomy1).
close.
Qed.

End Euclid.

