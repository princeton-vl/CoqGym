Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angleorderrespectscongruence2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_supplementinequality : 
   forall A B C D F a b c d f, 
   Supp A B C D F -> Supp a b c d f -> LtA a b c A B C ->
   LtA D B F d b f.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists P Q R, (BetS P R Q /\ Out B A P /\ Out B C Q /\ CongA a b c A B R)) by (conclude_def LtA );destruct Tf as [P[Q[R]]];spliter.
assert (nCol A B R) by (conclude lemma_equalanglesNC).
assert ((Out B C D /\ BetS A B F)) by (conclude_def Supp ).
assert (BetS Q R P) by (conclude axiom_betweennesssymmetry).
assert (BetS F B A) by (conclude axiom_betweennesssymmetry).
assert ((BetS B P A \/ eq A P \/ BetS B A P)) by (conclude lemma_ray1).
assert (BetS F B P).
by cases on (BetS B P A \/ eq A P \/ BetS B A P).
{
 assert (BetS F B P) by (conclude axiom_innertransitivity).
 close.
 }
{
 assert (BetS F B P) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS F B P) by (conclude lemma_3_7b).
 close.
 }
(** cases *)
assert (~ Col F P Q).
 {
 intro.
 assert (Col B A P) by (conclude lemma_rayimpliescollinear).
 assert (Col A B F) by (conclude_def Col ).
 assert (neq A B) by (forward_using lemma_betweennotequal).
 assert (Col A B P) by (forward_using lemma_collinearorder).
 assert (Col B F P) by (conclude lemma_collinear4).
 assert (Col F P B) by (forward_using lemma_collinearorder).
 assert (neq F P) by (forward_using lemma_betweennotequal).
 assert (Col P Q B) by (conclude lemma_collinear4).
 assert (Col P B Q) by (forward_using lemma_collinearorder).
 assert (Col P B A) by (forward_using lemma_collinearorder).
 assert (neq B P) by (forward_using lemma_betweennotequal).
 assert (neq P B) by (conclude lemma_inequalitysymmetric).
 assert (Col B Q A) by (conclude lemma_collinear4).
 assert (Col P R Q) by (conclude_def Col ).
 assert (Col P Q R) by (forward_using lemma_collinearorder).
 assert (Col P Q B) by (forward_using lemma_collinearorder).
 assert (neq P Q) by (forward_using lemma_betweennotequal).
 assert (Col Q R B) by (conclude lemma_collinear4).
 assert (Col Q B R) by (forward_using lemma_collinearorder).
 assert (Col Q B A) by (forward_using lemma_collinearorder).
 assert (neq B Q) by (conclude lemma_raystrict).
 assert (neq Q B) by (conclude lemma_inequalitysymmetric).
 assert (Col B R A) by (conclude lemma_collinear4).
 assert (Col A B R) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS F M R /\ BetS Q M B)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
assert (eq R R) by (conclude cn_equalityreflexive).
assert (~ eq B R).
 {
 intro.
 assert (Col A B R) by (conclude_def Col ).
 contradict.
 }
assert (Out B R R) by (conclude lemma_ray4).
assert (Supp A B R R F) by (conclude_def Supp ).
assert (CongA A B R a b c) by (conclude lemma_equalanglessymmetric).
assert (CongA R B F d b f) by (conclude lemma_supplements).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (eq F F) by (conclude cn_equalityreflexive).
assert (Out B F F) by (conclude lemma_ray4).
assert (CongA d b f R B F) by (conclude lemma_equalanglessymmetric).
assert (nCol R B F) by (conclude lemma_equalanglesNC).
assert (~ Col F B Q).
 {
 intro.
 assert (Col Q B F) by (forward_using lemma_collinearorder).
 assert (Col Q M B) by (conclude_def Col ).
 assert (Col Q B M) by (forward_using lemma_collinearorder).
 assert (neq Q B) by (forward_using lemma_betweennotequal).
 assert (Col B F M) by (conclude lemma_collinear4).
 assert (Col F M R) by (conclude_def Col ).
 assert (Col M F B) by (forward_using lemma_collinearorder).
 assert (Col M F R) by (forward_using lemma_collinearorder).
 assert (neq F M) by (forward_using lemma_betweennotequal).
 assert (neq M F) by (conclude lemma_inequalitysymmetric).
 assert (Col F B R) by (conclude lemma_collinear4).
 assert (Col R B F) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA F B Q F B Q) by (conclude lemma_equalanglesreflexive).
assert (BetS B M Q) by (conclude axiom_betweennesssymmetry).
assert (neq B M) by (forward_using lemma_betweennotequal).
assert (Out B M Q) by (conclude lemma_ray4).
assert (Out B Q M) by (conclude lemma_ray5).
assert (CongA F B Q F B M) by (conclude lemma_equalangleshelper).
assert (BetS R M F) by (conclude axiom_betweennesssymmetry).
assert (LtA F B Q F B R) by (conclude_def LtA ).
assert (CongA f b d F B R) by (conclude lemma_equalanglesflip).
assert (CongA F B R f b d) by (conclude lemma_equalanglessymmetric).
assert (LtA F B Q f b d) by (conclude lemma_angleorderrespectscongruence).
assert (Out B Q D) by (conclude lemma_ray3).
assert (CongA F B Q F B D) by (conclude lemma_equalangleshelper).
assert (~ Col F B D).
 {
 intro.
 assert (Col B Q D) by (conclude lemma_rayimpliescollinear).
 assert (Col D B Q) by (forward_using lemma_collinearorder).
 assert (Col D B F) by (forward_using lemma_collinearorder).
 assert (neq B D) by (conclude lemma_raystrict).
 assert (neq D B) by (conclude lemma_inequalitysymmetric).
 assert (Col B Q F) by (conclude lemma_collinear4).
 assert (Col F B Q) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA F B D D B F) by (conclude lemma_ABCequalsCBA).
assert (CongA F B Q D B F) by (conclude lemma_equalanglestransitive).
assert (CongA D B F F B Q) by (conclude lemma_equalanglessymmetric).
assert (LtA D B F f b d) by (conclude lemma_angleorderrespectscongruence2).
assert (nCol f b d) by (conclude lemma_equalanglesNC).
assert (~ Col d b f).
 {
 intro.
 assert (Col f b d) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA d b f f b d) by (conclude lemma_ABCequalsCBA).
assert (LtA D B F d b f) by (conclude lemma_angleorderrespectscongruence).
close.
Qed.

End Euclid.


