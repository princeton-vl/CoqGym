Require Export GeoCoq.Elements.OriginalProofs.proposition_31short.
Require Export GeoCoq.Elements.OriginalProofs.lemma_triangletoparallelogram.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equaltorightisright.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samenotopposite.
Require Export GeoCoq.Elements.OriginalProofs.proposition_34.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGflip.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_46 : 
   forall A B R, 
   neq A B -> nCol A B R ->
   exists X Y, SQ A B X Y /\ TS Y A B R /\ PG A B X Y.
Proof.
intros.
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists F, (BetS B A F /\ Cong A F A B)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (nCol B A R) by (forward_using lemma_NCorder).
assert (Col B A F) by (conclude_def Col ).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B A B) by (conclude_def Col ).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (nCol B F R) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists C, (Per B A C /\ TS C B F R)) by (conclude proposition_11B);destruct Tf as [C];spliter.
assert (nCol B F C) by (conclude_def TS ).
assert (Col B F A) by (forward_using lemma_collinearorder).
assert (Col B F B) by (conclude_def Col ).
assert (nCol B A C) by (conclude lemma_NChelper).
assert (neq A C) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists D, (Out A C D /\ Cong A D A B)) by (conclude lemma_layoff);destruct Tf as [D];spliter.
assert (Out A D C) by (conclude lemma_ray5).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
let Tf:=fresh in
assert (Tf:exists q, (BetS C q R /\ Col B F q /\ nCol B F C)) by (conclude_def TS );destruct Tf as [q];spliter.
assert (Col F B q) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (nCol A B C) by (conclude lemma_NChelper).
assert (Col A B F) by (forward_using lemma_collinearorder).
assert (Col F B A) by (forward_using lemma_collinearorder).
assert (neq B F) by (forward_using lemma_betweennotequal).
assert (neq F B) by (conclude lemma_inequalitysymmetric).
assert (Col B A q) by (conclude lemma_collinear4).
assert (Col A B q) by (forward_using lemma_collinearorder).
assert (TS C A B R) by (conclude_def TS ).
assert (TS D A B R) by (conclude lemma_9_5).
assert (nCol C A B) by (forward_using lemma_NCorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col C A A) by (conclude_def Col ).
assert (Col A C D) by (conclude lemma_rayimpliescollinear).
assert (Col C A D) by (forward_using lemma_collinearorder).
assert (neq A D) by (conclude lemma_ray2).
assert (nCol C A B) by (forward_using lemma_NCorder).
assert (nCol A D B) by (conclude lemma_NChelper).
assert (nCol A B D) by (forward_using lemma_NCorder).
assert (BetS F A B) by (conclude axiom_betweennesssymmetry).
assert (Col A B B) by (conclude_def Col ).
assert (nCol F B D) by (conclude lemma_NChelper).
let Tf:=fresh in
assert (Tf:exists G e M, (BetS G D e /\ CongA G D A D A B /\ Par G e F B /\ BetS G M B /\ BetS D M A)) by (conclude proposition_31short);destruct Tf as [G[e[M]]];spliter.
assert (Par G e A B) by (conclude lemma_collinearparallel).
assert (Par A B G e) by (conclude lemma_parallelsymmetric).
assert (Col G D e) by (conclude_def Col ).
assert (Col G e D) by (forward_using lemma_collinearorder).
let Tf:=fresh in
assert (Tf:exists E, (PG D E B A /\ Col G e E)) by (conclude lemma_triangletoparallelogram);destruct Tf as [E];spliter.
assert (Per C A B) by (conclude lemma_8_2).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (Per D A B) by (conclude lemma_collinearright).
assert (Per B A D) by (conclude lemma_8_2).
assert (Per G D A) by (conclude lemma_equaltorightisright).
let Tf:=fresh in
assert (Tf:exists p, (BetS G D p /\ Cong G D p D /\ Cong G A p A /\ neq D A)) by (conclude_def Per );destruct Tf as [p];spliter.
assert (BetS p D G) by (conclude axiom_betweennesssymmetry).
assert (Cong p D G D) by (conclude lemma_congruencesymmetric).
assert (Cong p A G A) by (conclude lemma_congruencesymmetric).
assert (Per p D A) by (conclude_def Per ).
assert (Par D A E B) by (conclude_def PG ).
assert (TP D A E B) by (conclude lemma_paralleldef2B).
assert (OS E B D A) by (conclude_def TP ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col D A D) by (conclude_def Col ).
assert (nCol D A B) by (forward_using lemma_NCorder).
assert (BetS B M G) by (conclude axiom_betweennesssymmetry).
assert (Col D M A) by (conclude_def Col ).
assert (Col D A M) by (forward_using lemma_collinearorder).
assert (TS B D A G) by (conclude_def TS ).
assert (TS E D A G) by (conclude lemma_planeseparation).
assert (nCol D A E) by (conclude_def TS ).
assert (TS G D A E) by (conclude lemma_oppositesidesymmetric).
assert (nCol D A G) by (conclude_def TS ).
let Tf:=fresh in
assert (Tf:exists d, (BetS E d G /\ Col D A d /\ nCol D A E)) by (conclude_def TS );destruct Tf as [d];spliter.
assert (neq E G) by (forward_using lemma_betweennotequal).
assert (neq G E) by (conclude lemma_inequalitysymmetric).
assert (neq G D) by (forward_using lemma_NCdistinct).
assert (neq D E) by (forward_using lemma_NCdistinct).
assert (~ OS E G D A).
 {
 intro.
 assert (~ TS E D A G) by (conclude lemma_samenotopposite).
 contradict.
 }
assert (~ BetS D G E).
 {
 intro.
 assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
 assert (BetS E D e) by (conclude lemma_3_7a).
 assert (OS E G D A) by (conclude_def OS ).
 contradict.
 }
assert (~ BetS G E D).
 {
 intro.
 assert (BetS E D e) by (conclude lemma_3_6a).
 assert (OS E G D A) by (conclude_def OS ).
 contradict.
 }
assert (Col e G D) by (forward_using lemma_collinearorder).
assert (Col e G E) by (forward_using lemma_collinearorder).
assert (nCol G e F) by (forward_using lemma_parallelNC).
assert (neq G e) by (forward_using lemma_NCdistinct).
assert (neq e G) by (conclude lemma_inequalitysymmetric).
assert (Col G D E) by (conclude lemma_collinear4).
assert ((eq G D \/ eq G E \/ eq D E \/ BetS D G E \/ BetS G D E \/ BetS G E D)) by (conclude_def Col ).
assert (BetS G D E).
by cases on (eq G D \/ eq G E \/ eq D E \/ BetS D G E \/ BetS G D E \/ BetS G E D).
{
 assert (~ ~ BetS G D E).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS G D E).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS G D E).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ BetS G D E).
  {
  intro.
  contradict.
  }
 close.
 }
{
 close.
 }
{
 assert (~ ~ BetS G D E).
  {
  intro.
  contradict.
  }
 close.
 }
(** cases *)
assert (Col G D E) by (conclude_def Col ).
assert (neq E D) by (conclude lemma_inequalitysymmetric).
assert (Per E D A) by (conclude lemma_collinearright).
assert ((Cong D A E B /\ Cong D E A B /\ CongA E D A A B E /\ CongA D A B B E D /\ Cong_3 E D A A B E)) by (conclude proposition_34).
assert (Cong A B D E) by (conclude lemma_congruencesymmetric).
assert (Cong A B E D) by (forward_using lemma_congruenceflip).
assert (Cong A B A D) by (conclude lemma_congruencesymmetric).
assert (Cong A D E B) by (forward_using lemma_congruenceflip).
assert (Cong A B E B) by (conclude lemma_congruencetransitive).
assert (Cong A B B E) by (forward_using lemma_congruenceflip).
assert (Cong A B D A) by (forward_using lemma_congruenceflip).
assert (CongA B E D D A B) by (conclude lemma_equalanglessymmetric).
assert (CongA A B E E D A) by (conclude lemma_equalanglessymmetric).
assert (Per B E D) by (conclude lemma_equaltorightisright).
assert (Per A B E) by (conclude lemma_equaltorightisright).
assert (SQ A B E D) by (conclude_def SQ ).
assert (PG B A D E) by (conclude lemma_PGsymmetric).
assert (PG A B E D) by (conclude lemma_PGflip).
close.
Qed.

End Euclid.


