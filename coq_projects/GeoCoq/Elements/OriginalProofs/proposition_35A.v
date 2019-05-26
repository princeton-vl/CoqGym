Require Export GeoCoq.Elements.OriginalProofs.lemma_35helper.
Require Export GeoCoq.Elements.OriginalProofs.proposition_29C.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ETreflexive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGrotate.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_PGflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trapezoiddiagonals.
Require Export GeoCoq.Elements.OriginalProofs.lemma_EFreflexive.

Section Euclid.

Context `{Ax:area}.


Lemma proposition_35A : 
   forall A B C D E F, 
   PG A B C D -> PG E B C F -> BetS A D F -> Col A E F ->
   EF A B C D E B C F.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (Cong A D B C) by (forward_using proposition_34).
assert (Cong E F B C) by (forward_using proposition_34).
assert (Cong B C E F) by (conclude lemma_congruencesymmetric).
assert (Cong A D E F) by (conclude lemma_congruencetransitive).
assert (Cong E F F E) by (conclude cn_equalityreverse).
assert (Cong A D F E) by (conclude lemma_congruencetransitive).
assert (Cong A D A D) by (conclude cn_congruencereflexive).
assert (Lt A D A F) by (conclude_def Lt ).
assert (Lt F E A F) by (conclude lemma_lessthancongruence2).
assert (Cong A F F A) by (conclude cn_equalityreverse).
assert (Lt F E F A) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists e, (BetS F e A /\ Cong F e F E)) by (conclude_def Lt );destruct Tf as [e];spliter.
assert (neq F A) by (forward_using lemma_betweennotequal).
assert (Out F A e) by (conclude lemma_ray4).
assert (BetS A E F) by (conclude lemma_35helper).
assert (BetS F E A) by (conclude axiom_betweennesssymmetry).
assert (Out F A E) by (conclude lemma_ray4).
assert (eq e E) by (conclude lemma_layoffunique).
assert (BetS F E A) by (conclude cn_equalitysub).
assert (BetS A E F) by (conclude axiom_betweennesssymmetry).
assert (Par D C A B) by (conclude lemma_parallelsymmetric).
assert (BetS F D A) by (conclude axiom_betweennesssymmetry).
assert (TP A D B C) by (conclude lemma_paralleldef2B).
assert (OS B C A D) by (conclude_def TP ).
assert (OS C B D A) by (forward_using lemma_samesidesymmetric).
assert (CongA F D C D A B) by (conclude proposition_29C).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (nCol A D C) by (forward_using lemma_parallelNC).
assert (~ eq A D).
 {
 intro.
 assert (Col A D C) by (conclude_def Col ).
 contradict.
 }
assert (neq A D) by (forward_using lemma_betweennotequal).
assert (nCol A B C) by (forward_using lemma_parallelNC).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (Out A B B) by (conclude lemma_ray4).
assert (~ ~ (BetS A D E \/ BetS A E D \/ eq D E)).
 {
 intro.
 assert (eq D E) by (eapply ( axiom_connectivity) with A F;auto).
 contradict.
 }
assert (Out A D E).
by cases on (BetS A D E \/ BetS A E D \/ eq D E).
{
 assert (Out A D E) by (conclude lemma_ray4).
 close.
 }
{
 assert (Out A D E) by (conclude lemma_ray4).
 close.
 }
{
 assert (Out A D D) by (conclude lemma_ray4).
 assert (Out A D E) by (conclude cn_equalitysub).
 close.
 }
(** cases *)
assert (nCol A D B) by (forward_using lemma_parallelNC).
assert (nCol D A B) by (forward_using lemma_NCorder).
assert (CongA D A B D A B) by (conclude lemma_equalanglesreflexive).
assert (CongA D A B E A B) by (conclude lemma_equalangleshelper).
assert (CongA F D C E A B) by (conclude lemma_equalanglestransitive).
assert (Cong A B D C) by (forward_using proposition_34).
assert (Cong D E E D) by (conclude cn_equalityreverse).
assert (Cong A E D F).
by cases on (BetS A D E \/ BetS A E D \/ eq D E).
{
 assert (BetS D E F) by (conclude lemma_3_6a).
 assert (BetS F E D) by (conclude axiom_betweennesssymmetry).
 assert (Cong A E F D) by (conclude cn_sumofparts).
 assert (Cong A E D F) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (BetS D E A) by (conclude axiom_betweennesssymmetry).
 assert (BetS E D F) by (conclude lemma_3_6a).
 assert (Cong D A E F) by (forward_using lemma_congruenceflip).
 assert (Cong E A D F) by (conclude lemma_differenceofparts).
 assert (Cong A E D F) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (Cong A E E F) by (conclude cn_equalitysub).
 assert (Cong A E D F) by (conclude cn_equalitysub).
 close.
 }
(** cases *)
assert (Cong D F A E) by (conclude lemma_congruencesymmetric).
assert (Cong D C A B) by (conclude lemma_congruencesymmetric).
assert ((Cong F C E B /\ CongA D F C A E B /\ CongA D C F A B E)) by (conclude proposition_04).
assert (Cong F D E A) by (forward_using lemma_congruenceflip).
assert (CongA A B E D C F) by (conclude lemma_equalanglessymmetric).
assert (nCol D C F) by (conclude lemma_equalanglesNC).
assert (nCol F D C) by (forward_using lemma_NCorder).
assert (Triangle F D C) by (conclude_def Triangle ).
assert (Cong_3 F D C E A B) by (conclude_def Cong_3 ).
assert (ET F D C E A B) by (conclude axiom_congruentequal).
assert (EF A B C D E B C F).
by cases on (BetS A D E \/ BetS A E D \/ eq D E).
{
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
 assert (BetS D M B) by (conclude axiom_betweennesssymmetry).
 assert (nCol A D B) by (forward_using lemma_parallelNC).
 assert (Col A D E) by (conclude_def Col ).
 assert (Col A D A) by (conclude_def Col ).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (nCol A E B) by (conclude lemma_NChelper).
 assert (BetS B M D) by (conclude axiom_betweennesssymmetry).
 rename_H H;
  let Tf:=fresh in
 assert (Tf:exists H, (BetS B H E /\ BetS A M H)) by (conclude postulate_Pasch_outer);destruct Tf as [H];spliter.
 assert (Col A M H) by (conclude_def Col ).
 assert (Col A M C) by (conclude_def Col ).
 assert (neq A M) by (forward_using lemma_betweennotequal).
 assert (neq M A) by (conclude lemma_inequalitysymmetric).
 assert (Col M A H) by (forward_using lemma_collinearorder).
 assert (Col M A C) by (forward_using lemma_collinearorder).
 assert (Col A H C) by (conclude lemma_collinear4).
 assert (BetS E H B) by (conclude axiom_betweennesssymmetry).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (~ eq B C).
  {
  intro.
  assert (Col A B C) by (conclude_def Col ).
  contradict.
  }
 assert (~ Meet A D B C) by (conclude_def Par ).
 assert (~ Meet E A C B).
  {
  intro.
  let Tf:=fresh in
  assert (Tf:exists q, (neq E A /\ neq C B /\ Col E A q /\ Col C B q)) by (conclude_def Meet );destruct Tf as [q];spliter.
  assert (neq B C) by (conclude lemma_inequalitysymmetric).
  assert (Col B C q) by (forward_using lemma_collinearorder).
  assert (Col A E q) by (forward_using lemma_collinearorder).
  assert (Col A D E) by (conclude_def Col ).
  assert (Col E A D) by (forward_using lemma_collinearorder).
  assert (Col E A q) by (forward_using lemma_collinearorder).
  assert (neq A D) by (forward_using lemma_betweennotequal).
  assert (Col A D q) by (conclude lemma_collinear4).
  assert (Meet A D B C) by (conclude_def Meet ).
  contradict.
  }
 assert (Col A C H) by (forward_using lemma_collinearorder).
 assert (Col E A A) by (conclude_def Col ).
 assert (Col C C B) by (conclude_def Col ).
 assert (neq C B) by (conclude lemma_inequalitysymmetric).
 assert (BetS A H C) by (conclude lemma_collinearbetween).
 assert (BetS C H A) by (conclude axiom_betweennesssymmetry).
 assert (BetS E D A) by (conclude axiom_betweennesssymmetry).
 assert (nCol A D C) by (forward_using lemma_parallelNC).
 assert (Col A D E) by (conclude_def Col ).
 assert (nCol A E C) by (conclude lemma_NChelper).
 assert (nCol C A E) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists G, (BetS C G D /\ BetS E G H)) by (conclude postulate_Pasch_inner);destruct Tf as [G];spliter.
 assert (BetS E G B) by (conclude lemma_3_6b).
 assert (BetS E G B) by (conclude lemma_3_6b).
 assert (Col E G B) by (conclude_def Col ).
 assert (~ Col D E G).
  {
  intro.
  assert (Col G E D) by (forward_using lemma_collinearorder).
  assert (Col G E B) by (forward_using lemma_collinearorder).
  assert (neq E G) by (forward_using lemma_betweennotequal).
  assert (neq G E) by (conclude lemma_inequalitysymmetric).
  assert (Col E D B) by (conclude lemma_collinear4).
  assert (Col B C B) by (conclude_def Col ).
  assert (Col E D A) by (forward_using lemma_collinearorder).
  assert (Col E D D) by (conclude_def Col ).
  assert (neq D E) by (forward_using lemma_betweennotequal).
  assert (neq E D) by (conclude lemma_inequalitysymmetric).
  assert (Col A D B) by (conclude lemma_collinear5).
  assert (Meet A D B C) by (conclude_def Meet ).
  contradict.
  }
 assert (Triangle D E G) by (conclude_def Triangle ).
 assert (ET D E G D E G) by (conclude lemma_ETreflexive).
 assert (ET D E G E D G) by (forward_using axiom_ETpermutation).
 assert (ET F D C A E B) by (forward_using axiom_ETpermutation).
 assert (ET A E B F D C) by (conclude axiom_ETsymmetric).
 assert (BetS B G E) by (conclude axiom_betweennesssymmetry).
 assert (BetS D E F) by (conclude lemma_3_6a).
 assert (BetS F E D) by (conclude axiom_betweennesssymmetry).
 assert (EF A D G B F E G C) by (conclude axiom_cutoff1).
 assert (nCol E G D) by (forward_using lemma_NCorder).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Col E G G) by (conclude_def Col ).
 assert (neq G B) by (forward_using lemma_betweennotequal).
 assert (neq B G) by (conclude lemma_inequalitysymmetric).
 assert (nCol B G D) by (conclude lemma_NChelper).
 assert (nCol D G B) by (forward_using lemma_NCorder).
 assert (Col C G D) by (conclude_def Col ).
 assert (Col D G C) by (forward_using lemma_collinearorder).
 assert (Col D G G) by (conclude_def Col ).
 assert (neq C G) by (forward_using lemma_betweennotequal).
 assert (nCol C G B) by (conclude lemma_NChelper).
 assert (nCol G C B) by (forward_using lemma_NCorder).
 assert (Triangle G C B) by (conclude_def Triangle ).
 assert (ET G C B G C B) by (conclude lemma_ETreflexive).
 assert (ET G C B G B C) by (forward_using axiom_ETpermutation).
 assert (BetS D G C) by (conclude axiom_betweennesssymmetry).
 assert (PG B C D A) by (conclude lemma_PGrotate).
 assert (PG D A B C) by (conclude lemma_PGsymmetric).
 assert (PG A D C B) by (conclude lemma_PGflip).
 let Tf:=fresh in
 assert (Tf:exists q, (BetS A q C /\ BetS D q B)) by (conclude lemma_diagonalsmeet);destruct Tf as [q];spliter.
 assert (PG B C F E) by (conclude lemma_PGrotate).
 assert (PG C F E B) by (conclude lemma_PGrotate).
 assert (PG F E B C) by (conclude lemma_PGrotate).
 let Tf:=fresh in
 assert (Tf:exists m, (BetS F m B /\ BetS E m C)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
 assert (EF A D C B F E B C) by (conclude axiom_paste2).
 assert (EF A D C B E B C F) by (forward_using axiom_EFpermutation).
 assert (EF E B C F A D C B) by (conclude axiom_EFsymmetric).
 assert (EF E B C F A B C D) by (forward_using axiom_EFpermutation).
 assert (EF A B C D E B C F) by (conclude axiom_EFsymmetric).
 close.
 }
{
 assert (ET E A B F D C) by (conclude axiom_ETsymmetric).
 assert (ET E A B D F C) by (forward_using axiom_ETpermutation).
 rename_H H;
 let Tf:=fresh in
 assert (Tf:exists H, (BetS B H D /\ BetS C H E)) by (conclude lemma_trapezoiddiagonals);destruct Tf as [H];spliter.
 assert (BetS E H C) by (conclude axiom_betweennesssymmetry).
 assert (~ Col B E D).
  {
  intro.
  assert (Col A E D) by (conclude_def Col ).
  assert (Col E D A) by (forward_using lemma_collinearorder).
  assert (Col E D B) by (forward_using lemma_collinearorder).
  assert (neq E D) by (forward_using lemma_betweennotequal).
  assert (Col D A B) by (conclude lemma_collinear4).
  assert (Col A D B) by (forward_using lemma_collinearorder).
  assert (eq B B) by (conclude cn_equalityreflexive).
  assert (Col B C B) by (conclude_def Col ).
  assert (neq A D) by (conclude_def Par ).
  assert (neq B C) by (conclude_def Par ).
  assert (Meet A D B C) by (conclude_def Meet ).
  assert (~ Meet A D B C) by (conclude_def Par ).
  contradict.
  }
 assert (EF B E D C B E D C) by (conclude lemma_EFreflexive).
 assert (EF B E D C C D E B) by (forward_using axiom_EFpermutation).
 assert (EF C D E B B E D C) by (conclude axiom_EFsymmetric).
 assert (BetS D E A) by (conclude axiom_betweennesssymmetry).
 assert (BetS E D F) by (conclude lemma_3_6a).
 assert (PG C D A B) by (conclude lemma_PGsymmetric).
 let Tf:=fresh in
 assert (Tf:exists p, (BetS C p A /\ BetS D p B)) by (conclude lemma_diagonalsmeet);destruct Tf as [p];spliter.
 assert (PG B E F C) by (conclude lemma_PGflip).
 let Tf:=fresh in
 assert (Tf:exists m, (BetS B m F /\ BetS E m C)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
 assert (EF C D A B B E F C) by (conclude axiom_paste2).
 assert (EF C D A B E B C F) by (forward_using axiom_EFpermutation).
 assert (EF E B C F C D A B) by (conclude axiom_EFsymmetric).
 assert (EF E B C F A B C D) by (forward_using axiom_EFpermutation).
 assert (EF A B C D E B C F) by (conclude axiom_EFsymmetric).
 close.
 }
{
 assert (ET F D C B E A) by (forward_using axiom_ETpermutation).
 assert (ET B E A F D C) by (conclude axiom_ETsymmetric).
 assert (ET B E A C D F) by (forward_using axiom_ETpermutation).
 assert (nCol D B C) by (forward_using lemma_parallelNC).
 assert (nCol E B C) by (conclude cn_equalitysub).
 assert (nCol B E C) by (forward_using lemma_NCorder).
 assert (Triangle B E C) by (conclude_def Triangle ).
 assert (ET B E C B E C) by (conclude lemma_ETreflexive).
 assert (ET B E C C E B) by (forward_using axiom_ETpermutation).
 assert (ET B E C C D B) by (conclude cn_equalitysub).
 assert (PG A B C E) by (conclude cn_equalitysub).
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M C /\ BetS B M E)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
 assert (BetS E M B) by (conclude axiom_betweennesssymmetry).
 assert (Col E M B) by (conclude_def Col ).
 assert (Col B E M) by (forward_using lemma_collinearorder).
 assert (Par A E B C) by (conclude_def PG ).
 assert (nCol A E B) by (forward_using lemma_parallelNC).
 assert (nCol B E A) by (forward_using lemma_NCorder).
 assert (TS A B E C) by (conclude_def TS ).
 assert (PG D B C F) by (conclude cn_equalitysub).
 assert (nCol C D F) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists m, (BetS D m C /\ BetS B m F)) by (conclude lemma_diagonalsmeet);destruct Tf as [m];spliter.
 assert (BetS F m B) by (conclude axiom_betweennesssymmetry).
 assert (Col D m C) by (conclude_def Col ).
 assert (Col C D m) by (forward_using lemma_collinearorder).
 assert (TS F C D B) by (conclude_def TS ).
 let Tf:=fresh in
 assert (Tf:exists J, (BetS A J C /\ BetS B J D)) by (conclude lemma_diagonalsmeet);destruct Tf as [J];spliter.
 assert (BetS B J E) by (conclude cn_equalitysub).
 let Tf:=fresh in
 assert (Tf:exists j, (BetS E j C /\ BetS B j F)) by (conclude lemma_diagonalsmeet);destruct Tf as [j];spliter.
 assert (BetS D j C) by (conclude cn_equalitysub).
 assert (BetS C j D) by (conclude axiom_betweennesssymmetry).
 assert (BetS F j B) by (conclude axiom_betweennesssymmetry).
 assert (EF B A E C C F D B) by (conclude axiom_paste3).
 assert (EF B A E C D B C F) by (forward_using axiom_EFpermutation).
 assert (EF B A E C E B C F) by (conclude cn_equalitysub).
 assert (EF E B C F B A E C) by (conclude axiom_EFsymmetric).
 assert (EF E B C F A B C E) by (forward_using axiom_EFpermutation).
 assert (EF E B C F A B C D) by (conclude cn_equalitysub).
 assert (EF A B C D E B C F) by (conclude axiom_EFsymmetric).
 close.
 }
(** cases *)
close.
Qed.


End Euclid.



