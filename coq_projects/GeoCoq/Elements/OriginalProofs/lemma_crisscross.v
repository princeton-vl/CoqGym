Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_paralleldef2B.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearparallel.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crisscross : 
   forall A B C D, 
   Par A C B D -> ~ CR A B C D ->
   CR A D B C.
Proof.
intros.
assert (Par B D A C) by (conclude lemma_parallelsymmetric).
assert (TP B D A C) by (conclude lemma_paralleldef2B).
assert (OS A C B D) by (conclude_def TP ).
assert (nCol A C B) by (forward_using lemma_parallelNC).
assert (neq A B) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists E, (BetS A B E /\ Cong B E A B)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col B D B) by (conclude_def Col ).
assert (nCol A B D) by (forward_using lemma_parallelNC).
assert (nCol B D A) by (forward_using lemma_NCorder).
assert (OS C A B D) by (forward_using lemma_samesidesymmetric).
assert (TS A B D E) by (conclude_def TS ).
assert (TS C B D E) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists F, (BetS C F E /\ Col B D F /\ nCol B D C)) by (conclude_def TS );destruct Tf as [F];spliter.
assert (neq B D) by (forward_using lemma_NCdistinct).
assert (nCol A B D) by (forward_using lemma_parallelNC).
assert (neq A D) by (forward_using lemma_NCdistinct).
assert (nCol A C D) by (forward_using lemma_parallelNC).
assert (neq A C) by (forward_using lemma_NCdistinct).
assert (neq C D) by (forward_using lemma_NCdistinct).
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (nCol A C B) by (forward_using lemma_parallelNC).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (neq B C) by (conclude lemma_inequalitysymmetric).
assert ((eq B D \/ eq B F \/ eq D F \/ BetS D B F \/ BetS B D F \/ BetS B F D)) by (conclude_def Col ).
assert (CR A D B C).
by cases on (eq B D \/ eq B F \/ eq D F \/ BetS D B F \/ BetS B D F \/ BetS B F D).
{
 assert (~ ~ CR A D B C).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ CR A D B C).
  {
  intro.
  assert (Col C F E) by (conclude_def Col ).
  assert (Col E F C) by (forward_using lemma_collinearorder).
  assert (neq B E) by (forward_using lemma_betweennotequal).
  assert (Col A B E) by (conclude_def Col ).
  assert (Col E B A) by (forward_using lemma_collinearorder).
  assert (Col E F C) by (forward_using lemma_collinearorder).
  assert (Col E B C) by (conclude cn_equalitysub).
  assert (neq E B) by (conclude lemma_inequalitysymmetric).
  assert (Col B A C) by (conclude lemma_collinear4).
  assert (Col A C B) by (forward_using lemma_collinearorder).
  assert (nCol A C B) by (forward_using lemma_parallelNC).
  contradict.
  }
 close.
 }
{
 assert (nCol A C B) by (forward_using lemma_parallelNC).
 assert (nCol A C F) by (conclude cn_equalitysub).
 assert (nCol C F A) by (forward_using lemma_NCorder).
 assert (Col C F E) by (conclude_def Col ).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (Col C F C) by (conclude_def Col ).
 assert (neq C E) by (forward_using lemma_betweennotequal).
 assert (nCol C E A) by (conclude lemma_NChelper).
 assert (nCol A E C) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M F /\ BetS C M B)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
 assert (BetS A M D) by (conclude cn_equalitysub).
 assert (BetS B M C) by (conclude axiom_betweennesssymmetry).
 assert (CR A D B C) by (conclude_def CR ).
 close.
 }
{
 assert (~ ~ CR A D B C).
  {
  intro.
  assert (nCol D B C) by (forward_using lemma_NCorder).
  assert (eq D D) by (conclude cn_equalityreflexive).
  assert (Col D B D) by (conclude_def Col ).
  assert (Col D B F) by (forward_using lemma_collinearorder).
  assert (neq D F) by (forward_using lemma_betweennotequal).
  assert (nCol D F C) by (conclude lemma_NChelper).
  assert (nCol C F D) by (forward_using lemma_NCorder).
  assert (Col C F E) by (conclude_def Col ).
  assert (eq C C) by (conclude cn_equalityreflexive).
  assert (Col C F C) by (conclude_def Col ).
  assert (neq C E) by (forward_using lemma_betweennotequal).
  assert (nCol C E D) by (conclude lemma_NChelper).
  assert (nCol E C D) by (forward_using lemma_NCorder).
  assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
  let Tf:=fresh in
  assert (Tf:exists M, (BetS D M C /\ BetS E B M)) by (conclude postulate_Pasch_outer);destruct Tf as [M];spliter.
  assert (BetS C M D) by (conclude axiom_betweennesssymmetry).
  assert (BetS M B E) by (conclude axiom_betweennesssymmetry).
  assert (Col A B E) by (conclude_def Col ).
  assert (Col E B M) by (conclude_def Col ).
  assert (Col E B A) by (forward_using lemma_collinearorder).
  assert (neq B E) by (forward_using lemma_betweennotequal).
  assert (neq E B) by (conclude lemma_inequalitysymmetric).
  assert (Col B M A) by (conclude lemma_collinear4).
  assert (Col A B M) by (forward_using lemma_collinearorder).
  assert (Par C A B D) by (forward_using lemma_parallelflip).
  assert (~ Meet C A B D) by (conclude_def Par ).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (Col C A A) by (conclude_def Col ).
  assert (eq B B) by (conclude cn_equalityreflexive).
  assert (Col B B D) by (conclude_def Col ).
  assert (BetS A M B) by (conclude lemma_collinearbetween).
  assert (CR A B C D) by (conclude_def CR ).
  contradict.
  }
 close.
 }
{
 assert (nCol A C B) by (forward_using lemma_parallelNC).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (Col A B E) by (conclude_def Col ).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (nCol A B C) by (forward_using lemma_NCorder).
 assert (nCol A E C) by (conclude lemma_NChelper).
 assert (Col A E B) by (forward_using lemma_collinearorder).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Col A E E) by (conclude_def Col ).
 assert (neq B E) by (forward_using lemma_betweennotequal).
 assert (nCol B E C) by (conclude lemma_NChelper).
 assert (nCol C E B) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists J, (BetS B J E /\ BetS C D J)) by (conclude postulate_Pasch_outer);destruct Tf as [J];spliter.
 assert (BetS A J E) by (conclude lemma_3_5b).
 assert (nCol A C B) by (forward_using lemma_parallelNC).
 assert (nCol A B C) by (forward_using lemma_NCorder).
 assert (Col A J E) by (conclude_def Col ).
 assert (Col E A B) by (forward_using lemma_collinearorder).
 assert (Col E A J) by (forward_using lemma_collinearorder).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (neq E A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B J) by (conclude lemma_collinear4).
 assert (neq A J) by (forward_using lemma_betweennotequal).
 assert (nCol A J C) by (conclude lemma_NChelper).
 assert (BetS A B J) by (conclude axiom_innertransitivity).
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M D /\ BetS C M B)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
 assert (BetS B M C) by (conclude axiom_betweennesssymmetry).
 assert (CR A D B C) by (conclude_def CR ).
 close.
 }
{
 assert (BetS D F B) by (conclude axiom_betweennesssymmetry).
 assert (BetS E B A) by (conclude axiom_betweennesssymmetry).
 assert (nCol A B D) by (forward_using lemma_parallelNC).
 assert (Col A B E) by (conclude_def Col ).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col A B A) by (conclude_def Col ).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (nCol A E D) by (conclude lemma_NChelper).
 assert (nCol E A D) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists Q, (BetS D Q A /\ BetS E F Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
 assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
 assert (Col E F Q) by (conclude_def Col ).
 assert (Col E F C) by (conclude_def Col ).
 assert (neq F E) by (forward_using lemma_betweennotequal).
 assert (neq E F) by (conclude lemma_inequalitysymmetric).
 assert (Col F Q C) by (conclude lemma_collinear4).
 assert (Col F C Q) by (forward_using lemma_collinearorder).
 assert (BetS A Q D) by (conclude axiom_betweennesssymmetry).
 assert (Col B F D) by (conclude_def Col ).
 assert (Col B D F) by (forward_using lemma_collinearorder).
 assert (neq F D) by (forward_using lemma_betweennotequal).
 assert (Par A C F D) by (conclude lemma_collinearparallel).
 assert (~ Meet A C F D) by (conclude_def Par ).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (eq F F) by (conclude cn_equalityreflexive).
 assert (Col A C C) by (conclude_def Col ).
 assert (Col F F D) by (conclude_def Col ).
 assert (Col C F Q) by (forward_using lemma_collinearorder).
 assert (BetS C Q F) by (conclude lemma_collinearbetween).
 assert (nCol A C B) by (forward_using lemma_parallelNC).
 assert (nCol A B C) by (forward_using lemma_NCorder).
 assert (Col A B A) by (conclude_def Col ).
 assert (Col A B E) by (conclude_def Col ).
 assert (neq A E) by (forward_using lemma_betweennotequal).
 assert (nCol A E C) by (conclude lemma_NChelper).
 assert (BetS C Q E) by (conclude lemma_3_6b).
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M Q /\ BetS C M B)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
 assert (BetS A M D) by (conclude lemma_3_6b).
 assert (BetS B M C) by (conclude axiom_betweennesssymmetry).
 assert (CR A D B C) by (conclude_def CR ).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


