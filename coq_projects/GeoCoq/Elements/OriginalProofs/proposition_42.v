Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidecollinear.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_41.
Require Export GeoCoq.Elements.OriginalProofs.proposition_38.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_42 : 
   forall A B C D E J K, 
   Triangle A B C -> nCol J D K -> Midpoint B E C ->
   exists X Z, PG X E C Z /\ EF A B E C X E C Z /\ CongA C E X J D K /\ Col X Z A.
Proof.
intros.
assert ((BetS B E C /\ Cong B E E C)) by (conclude_def Midpoint ).
assert (Cong E B E C) by (forward_using lemma_congruenceflip).
assert (nCol A B C) by (conclude_def Triangle ).
assert (Col B E C) by (conclude_def Col ).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (Col B C E) by (forward_using lemma_collinearorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col B C C) by (conclude_def Col ).
assert (neq E C) by (forward_using lemma_betweennotequal).
assert (nCol E C A) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists f c, (Out E C c /\ CongA f E c J D K /\ OS f A E C)) by (conclude proposition_23C);destruct Tf as [f[c]];spliter.
assert (nCol B C A) by (forward_using lemma_NCorder).
let Tf:=fresh in
assert (Tf:exists P Q M, (BetS P A Q /\ CongA Q A E A E B /\ CongA Q A E B E A /\ CongA E A Q B E A /\ CongA P A E A E C /\ CongA P A E C E A /\ CongA E A P C E A /\ Par P Q B C /\ Cong P A E C /\ Cong A Q B E /\ Cong A M M E /\ Cong P M M C /\ Cong B M M Q /\ BetS P M C /\ BetS B M Q /\ BetS A M E)) by (conclude proposition_31);destruct Tf as [P[Q[M]]];spliter.
assert (CongA A E C P A E) by (conclude lemma_equalanglessymmetric).
assert (nCol P A E) by (conclude lemma_equalanglesNC).
assert (nCol E A P) by (forward_using lemma_NCorder).
assert (OS A f E C) by (forward_using lemma_samesidesymmetric).
assert (nCol B C A) by (forward_using lemma_NCorder).
assert (Col B C E) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col B C B) by (conclude_def Col ).
assert (neq B E) by (forward_using lemma_betweennotequal).
assert (nCol B E A) by (conclude lemma_NChelper).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col B C C) by (conclude_def Col ).
assert (neq E C) by (forward_using lemma_betweennotequal).
assert (neq C E) by (conclude lemma_inequalitysymmetric).
assert (nCol C E A) by (conclude lemma_NChelper).
assert (neq E A) by (forward_using lemma_NCdistinct).
assert (~ ~ Meet E f P Q).
 {
 intro.
 assert (~ LtA C E f C E A).
  {
  intro.
  assert (Out E C C) by (conclude lemma_ray4).
  assert (Out E A A) by (conclude lemma_ray4).
  let Tf:=fresh in
  assert (Tf:exists m, (BetS A m C /\ Out E f m)) by (conclude lemma_crossbar2);destruct Tf as [m];spliter.
  assert (BetS C m A) by (conclude axiom_betweennesssymmetry).
  assert (BetS C M P) by (conclude axiom_betweennesssymmetry).
  assert (BetS E M A) by (conclude axiom_betweennesssymmetry).
  assert (Cong M E A M) by (conclude lemma_congruencesymmetric).
  assert (Cong E M A M) by (forward_using lemma_congruenceflip).
  assert (Cong M C P M) by (conclude lemma_congruencesymmetric).
  assert (Cong M C M P) by (forward_using lemma_congruenceflip).
  let Tf:=fresh in
  assert (Tf:exists F, (BetS E m F /\ BetS P A F)) by (conclude postulate_Euclid5);destruct Tf as [F];spliter.
  assert (Col E m F) by (conclude_def Col ).
  assert (Col m E F) by (forward_using lemma_collinearorder).
  assert (Col E f m) by (conclude lemma_rayimpliescollinear).
  assert (Col m E f) by (forward_using lemma_collinearorder).
  assert (neq E m) by (forward_using lemma_betweennotequal).
  assert (neq m E) by (conclude lemma_inequalitysymmetric).
  assert (Col E f F) by (conclude lemma_collinear4).
  assert (Col P A F) by (conclude_def Col ).
  assert (Col P A Q) by (conclude_def Col ).
  assert (neq P A) by (forward_using lemma_betweennotequal).
  assert (neq A P) by (conclude lemma_inequalitysymmetric).
  assert (Col A P F) by (forward_using lemma_collinearorder).
  assert (Col A P Q) by (forward_using lemma_collinearorder).
  assert (Col P F Q) by (conclude lemma_collinear4).
  assert (Col P Q F) by (forward_using lemma_collinearorder).
  assert (neq E f) by (conclude lemma_ray2).
  assert (neq P Q) by (forward_using lemma_betweennotequal).
  assert (Meet E f P Q) by (conclude_def Meet ).
  contradict.
  }
 assert (Col E C B) by (forward_using lemma_collinearorder).
 assert (neq B E) by (forward_using lemma_betweennotequal).
 assert (neq E B) by (conclude lemma_inequalitysymmetric).
 assert (OS A f E B) by (conclude lemma_samesidecollinear).
 assert (OS f A E B) by (forward_using lemma_samesidesymmetric).
 assert (BetS C E B) by (conclude axiom_betweennesssymmetry).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (eq f f) by (conclude cn_equalityreflexive).
 assert (nCol E B f) by (conclude_def OS ).
 assert (neq E f) by (forward_using lemma_NCdistinct).
 assert (Col B E C) by (conclude_def Col ).
 assert (Col E B C) by (forward_using lemma_collinearorder).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Col E B E) by (conclude_def Col ).
 assert (nCol E C f) by (conclude lemma_NChelper).
 assert (nCol C E f) by (forward_using lemma_NCorder).
 assert (~ LtA C E A C E f).
  {
  intro.
  assert (Out E A A) by (conclude lemma_ray4).
  assert (Out E f f) by (conclude lemma_ray4).
  assert (Supp C E A A B) by (conclude_def Supp ).
  assert (Supp C E f f B) by (conclude_def Supp ).
  assert (LtA f E B A E B) by (conclude lemma_supplementinequality).
  assert (nCol B E f) by (forward_using lemma_NCorder).
  assert (CongA B E f f E B) by (conclude lemma_ABCequalsCBA).
  assert (LtA B E f A E B) by (conclude lemma_angleorderrespectscongruence2).
  assert (CongA B E A A E B) by (conclude lemma_ABCequalsCBA).
  assert (LtA B E f B E A) by (conclude lemma_angleorderrespectscongruence).
  assert (Out E B B) by (conclude lemma_ray4).
  assert (Out E A A) by (conclude lemma_ray4).
  let Tf:=fresh in
  assert (Tf:exists m, (BetS A m B /\ Out E f m)) by (conclude lemma_crossbar2);destruct Tf as [m];spliter.
  assert (BetS B m A) by (conclude axiom_betweennesssymmetry).
  assert (BetS E M A) by (conclude axiom_betweennesssymmetry).
  assert (Cong M E A M) by (conclude lemma_congruencesymmetric).
  assert (Cong E M A M) by (forward_using lemma_congruenceflip).
  assert (Cong M B M Q) by (forward_using lemma_congruenceflip).
  assert (nCol P A E) by (forward_using lemma_NCorder).
  assert (Col P A Q) by (conclude_def Col ).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (Col P A A) by (conclude_def Col ).
  assert (neq A Q) by (forward_using lemma_betweennotequal).
  assert (neq Q A) by (conclude lemma_inequalitysymmetric).
  assert (nCol Q A E) by (conclude lemma_NChelper).
  assert (nCol E A Q) by (forward_using lemma_NCorder).
  let Tf:=fresh in
  assert (Tf:exists F, (BetS E m F /\ BetS Q A F)) by (conclude postulate_Euclid5);destruct Tf as [F];spliter.
  assert (Col E m F) by (conclude_def Col ).
  assert (Col m E F) by (forward_using lemma_collinearorder).
  assert (Col E f m) by (conclude lemma_rayimpliescollinear).
  assert (Col m E f) by (forward_using lemma_collinearorder).
  assert (neq E m) by (forward_using lemma_betweennotequal).
  assert (neq m E) by (conclude lemma_inequalitysymmetric).
  assert (Col E f F) by (conclude lemma_collinear4).
  assert (Col Q A F) by (conclude_def Col ).
  assert (BetS Q A P) by (conclude axiom_betweennesssymmetry).
  assert (Col Q A P) by (conclude_def Col ).
  assert (neq Q A) by (forward_using lemma_betweennotequal).
  assert (neq A Q) by (conclude lemma_inequalitysymmetric).
  assert (Col A Q F) by (forward_using lemma_collinearorder).
  assert (Col A Q P) by (forward_using lemma_collinearorder).
  assert (Col Q F P) by (conclude lemma_collinear4).
  assert (Col P Q F) by (forward_using lemma_collinearorder).
  assert (neq E f) by (conclude lemma_ray2).
  assert (neq Q P) by (forward_using lemma_betweennotequal).
  assert (neq P Q) by (conclude lemma_inequalitysymmetric).
  assert (Meet E f P Q) by (conclude_def Meet ).
  contradict.
  }
 assert (~ ~ CongA C E A C E f).
  {
  intro.
  assert (LtA C E A C E f) by (conclude lemma_angletrichotomy2).
  contradict.
  }
 let Tf:=fresh in
 assert (Tf:exists d a p q, (Out E C d /\ Out E A a /\ Out E C p /\ Out E f q /\ Cong E d E p /\ Cong E a E q /\ Cong d a p q /\ nCol C E A))
  by (remove_double_neg;unfold CongA in *; assumption);destruct Tf as [d[a[p[q]]]];spliter.
 assert (Col P Q A) by (conclude_def Col ).
 assert (eq d p) by (conclude lemma_layoffunique).
 assert (Cong d a d q) by (conclude cn_equalitysub).
 assert (Cong a d q d) by (forward_using lemma_congruenceflip).
 assert (Cong a E q E) by (forward_using lemma_congruenceflip).
 assert (neq E d) by (conclude lemma_raystrict).
 assert (Col E C d) by (conclude lemma_rayimpliescollinear).
 assert (OS A f E d) by (conclude lemma_samesidecollinear).
 assert (Col E d E) by (conclude_def Col ).
 assert (Col E E d) by (forward_using lemma_collinearorder).
 assert (OS A q E d) by (conclude lemma_sameside2).
 assert (OS q A E d) by (forward_using lemma_samesidesymmetric).
 assert (OS q a E d) by (conclude lemma_sameside2).
 assert (OS a q E d) by (forward_using lemma_samesidesymmetric).
 assert (eq a q) by (conclude proposition_07).
 assert (Col E A a) by (conclude lemma_rayimpliescollinear).
 assert (Col E f q) by (conclude lemma_rayimpliescollinear).
 assert (Col E A q) by (conclude cn_equalitysub).
 assert (Col q E A) by (forward_using lemma_collinearorder).
 assert (Col q E f) by (forward_using lemma_collinearorder).
 assert (neq E q) by (conclude lemma_raystrict).
 assert (neq q E) by (conclude lemma_inequalitysymmetric).
 assert (Col E A f) by (conclude lemma_collinear4).
 assert (Col E f A) by (forward_using lemma_collinearorder).
 assert (neq P Q) by (forward_using lemma_betweennotequal).
 assert (Meet E f P Q) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists F, (neq E f /\ neq P Q /\ Col E f F /\ Col P Q F)) by (conclude_def Meet );destruct Tf as [F];spliter.
assert (neq C E) by (conclude lemma_inequalitysymmetric).
assert (Par P Q E C) by (conclude lemma_collinearparallel).
assert (Par E C P Q) by (conclude lemma_parallelsymmetric).
let Tf:=fresh in
assert (Tf:exists G, (PG F G C E /\ Col P Q G)) by (conclude lemma_triangletoparallelogram);destruct Tf as [G];spliter.
assert (PG G F E C) by (conclude lemma_PGflip).
assert (PG F E C G) by (conclude lemma_PGrotate).
assert (Col P A Q) by (conclude_def Col ).
assert (Col P Q A) by (forward_using lemma_collinearorder).
assert (Par F E C G) by (conclude_def PG ).
assert (nCol F E G) by (forward_using lemma_parallelNC).
assert (neq F G) by (forward_using lemma_NCdistinct).
assert (Col F G A) by (conclude lemma_collinear5).
assert (ET F E C A E C) by (conclude proposition_41).
assert (Par P Q C B) by (forward_using lemma_parallelflip).
assert (Col C B E) by (forward_using lemma_collinearorder).
assert (neq E B) by (conclude lemma_inequalitysymmetric).
assert (Par P Q E B) by (conclude lemma_collinearparallel).
assert (Par P Q B E) by (forward_using lemma_parallelflip).
assert (Cong B E E C) by (forward_using lemma_congruenceflip).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col B E E) by (conclude_def Col ).
assert (ET A B E A E C) by (conclude proposition_38).
assert (ET A E C A B E) by (conclude axiom_ETsymmetric).
assert (ET A E C A E B) by (forward_using axiom_ETpermutation).
assert (ET A E B A E C) by (conclude axiom_ETsymmetric).
assert (eq E E) by (conclude cn_equalityreflexive).
assert (Col A E E) by (conclude_def Col ).
assert (nCol A E B) by (forward_using lemma_NCorder).
assert (TS B A E C) by (conclude_def TS ).
assert (PG E F G C) by (conclude lemma_PGflip).
assert (Cong_3 F E C C G F) by (conclude proposition_34).
assert (ET F E C C G F) by (conclude axiom_congruentequal).
assert (ET F E C F C G) by (forward_using axiom_ETpermutation).
assert (ET F C G F E C) by (conclude axiom_ETsymmetric).
assert (ET F C G F C E) by (forward_using axiom_ETpermutation).
assert (ET F C E F C G) by (conclude axiom_ETsymmetric).
let Tf:=fresh in
assert (Tf:exists m, (BetS E m G /\ BetS F m C)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
assert (Col F m C) by (conclude_def Col ).
assert (Col F C m) by (forward_using lemma_collinearorder).
assert (Par F E C G) by (conclude_def PG ).
assert (nCol F E C) by (forward_using lemma_parallelNC).
assert (nCol F C E) by (forward_using lemma_NCorder).
assert (TS E F C G) by (conclude_def TS ).
assert (ET A E C F E C) by (conclude axiom_ETsymmetric).
assert (ET A E B F E C) by (conclude axiom_ETtransitive).
assert (ET A E B F C E) by (forward_using axiom_ETpermutation).
assert (ET A E C F E C) by (conclude axiom_ETsymmetric).
assert (ET F C G F C E) by (conclude axiom_ETsymmetric).
assert (ET F C G F E C) by (forward_using axiom_ETpermutation).
assert (ET F E C F C G) by (conclude axiom_ETsymmetric).
assert (ET A E C F C G) by (conclude axiom_ETtransitive).
assert (EF A B E C F E C G) by (conclude axiom_paste3).
assert (nCol F E C) by (forward_using lemma_parallelNC).
assert (nCol C E F) by (forward_using lemma_NCorder).
assert (CongA C E F C E F) by (conclude lemma_equalanglesreflexive).
assert ((eq E f \/ eq E F \/ eq f F \/ BetS f E F \/ BetS E f F \/ BetS E F f)) by (conclude_def Col ).
assert (neq F E) by (forward_using lemma_NCdistinct).
assert (neq E F) by (conclude lemma_inequalitysymmetric).
assert (Out E F f).
by cases on (eq E f \/ eq E F \/ eq f F \/ BetS f E F \/ BetS E f F \/ BetS E F f).
{
 assert (~ ~ Out E F f).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out E F f).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (eq F F) by (conclude cn_equalityreflexive).
 assert (Out E F F) by (conclude lemma_ray4).
 assert (Out E F f) by (conclude cn_equalitysub).
 close.
 }
{
 assert (~ ~ Out E F f).
  {
  intro.
  assert (eq E E) by (conclude cn_equalityreflexive).
  assert (Col E C E) by (conclude_def Col ).
  assert (BetS F E f) by (conclude axiom_betweennesssymmetry).
  assert (nCol E C F) by (forward_using lemma_NCorder).
  assert (TS F E C f) by (conclude_def TS ).
  assert (TS f E C F) by (conclude lemma_oppositesidesymmetric).
  assert (OS A f E C) by (forward_using lemma_samesidesymmetric).
  assert (TS A E C F) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists j, (BetS A j F /\ Col E C j /\ nCol E C A)) by (conclude_def TS );destruct Tf as [j];spliter.
  assert (Col A j F) by (conclude_def Col ).
  assert (neq P Q) by (forward_using lemma_betweennotequal).
  assert (neq Q P) by (conclude lemma_inequalitysymmetric).
  assert (Col Q A F) by (conclude lemma_collinear4).
  assert (Col A F Q) by (forward_using lemma_collinearorder).
  assert (Col Q P A) by (forward_using lemma_collinearorder).
  assert (Col Q P F) by (forward_using lemma_collinearorder).
  assert (Col P A F) by (conclude lemma_collinear4).
  assert (Col A F P) by (forward_using lemma_collinearorder).
  assert (Col A F j) by (forward_using lemma_collinearorder).
  assert (neq P Q) by (forward_using lemma_betweennotequal).
  assert (neq A F) by (forward_using lemma_betweennotequal).
  assert (Col P Q j) by (conclude lemma_collinear5).
  assert (Meet P Q E C) by (conclude_def Meet ).
  assert (~ Meet P Q E C) by (conclude_def Par ).
  contradict.
  }
 close.
 }
{
 assert (Out E F f) by (conclude lemma_ray4).
 close.
 }
{
 assert (Out E F f) by (conclude lemma_ray4).
 close.
 }
(** cases *)
assert (CongA C E F c E f) by (conclude lemma_equalangleshelper).
assert (CongA F E C f E c) by (conclude lemma_equalanglesflip).
assert (CongA F E C J D K) by (conclude lemma_equalanglestransitive).
assert (CongA C E F F E C) by (conclude lemma_ABCequalsCBA).
assert (CongA C E F J D K) by (conclude lemma_equalanglestransitive).
close.
Qed.

End Euclid.


