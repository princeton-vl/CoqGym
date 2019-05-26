Require Export GeoCoq.Elements.OriginalProofs.proposition_37.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_39A : 
   forall A B C D M, 
   Triangle A B C -> ET A B C D B C -> BetS A M C -> Out B D M ->
   Par A D B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (neq A B) by (forward_using lemma_NCdistinct).
let Tf:=fresh in
assert (Tf:exists m, (BetS A m B /\ Cong m A m B)) by (conclude proposition_10);destruct Tf as [m];spliter.
assert (Col A m B) by (conclude_def Col ).
assert (Col A B m) by (forward_using lemma_collinearorder).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (neq A m) by (forward_using lemma_betweennotequal).
assert (nCol A m C) by (conclude lemma_NChelper).
assert (neq m C) by (forward_using lemma_NCdistinct).
assert (neq C m) by (conclude lemma_inequalitysymmetric).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS C m H /\ Cong m H m C)) by (conclude lemma_extension);destruct Tf as [H];spliter.
assert (BetS B m A) by (conclude axiom_betweennesssymmetry).
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (Cong m B m A) by (conclude lemma_congruencesymmetric).
assert (Cong B m A m) by (forward_using lemma_congruenceflip).
assert (Cong m C m H) by (conclude lemma_congruencesymmetric).
assert (~ Col B A H).
 {
 intro.
 assert (Col A m B) by (conclude_def Col ).
 assert (Col B A m) by (forward_using lemma_collinearorder).
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Col A H m) by (conclude lemma_collinear4).
 assert (Col H m A) by (forward_using lemma_collinearorder).
 assert (Col C m H) by (conclude_def Col ).
 assert (Col H m C) by (forward_using lemma_collinearorder).
 assert (neq m H) by (forward_using lemma_betweennotequal).
 assert (neq H m) by (conclude lemma_inequalitysymmetric).
 assert (Col m A C) by (conclude lemma_collinear4).
 assert (Col m A B) by (forward_using lemma_collinearorder).
 assert (neq A m) by (forward_using lemma_betweennotequal).
 assert (neq m A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS B M E /\ BetS H A E)) by (conclude postulate_Euclid5);destruct Tf as [E];spliter.
assert (BetS H m C) by (conclude axiom_betweennesssymmetry).
assert (Col C m H) by (conclude_def Col ).
assert (Col m C H) by (forward_using lemma_collinearorder).
assert (eq m m) by (conclude cn_equalityreflexive).
assert (Col m C m) by (conclude_def Col ).
assert (nCol m C A) by (forward_using lemma_NCorder).
assert (neq m H) by (forward_using lemma_betweennotequal).
assert (nCol m H A) by (conclude lemma_NChelper).
assert (nCol A m H) by (forward_using lemma_NCorder).
assert (CongA A m H C m B) by (conclude proposition_15a).
assert (nCol H m A) by (forward_using lemma_NCorder).
assert (Col A m B) by (conclude_def Col ).
assert (Col A B m) by (forward_using lemma_collinearorder).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Col A B B) by (conclude_def Col ).
assert (neq m B) by (forward_using lemma_betweennotequal).
assert (nCol m B C) by (conclude lemma_NChelper).
assert (CongA H m A A m H) by (conclude lemma_ABCequalsCBA).
assert (CongA H m A C m B) by (conclude lemma_equalanglestransitive).
assert (Cong m A m B) by (conclude lemma_congruencesymmetric).
assert (CongA m H A m C B) by (apply (proposition_04 m H A m C B);auto).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (neq B C) by (forward_using lemma_NCdistinct).
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert (Out C B B) by (conclude lemma_ray4).
assert (Out C m H) by (conclude lemma_ray4).
assert (CongA m H A H C B) by (conclude lemma_equalangleshelper).
assert (CongA H C B m H A) by (conclude lemma_equalanglessymmetric).
assert (eq A A) by (conclude cn_equalityreflexive).
assert (neq H A) by (forward_using lemma_NCdistinct).
assert (Out H A A) by (conclude lemma_ray4).
assert (BetS H m C) by (conclude axiom_betweennesssymmetry).
assert (neq H m) by (forward_using lemma_betweennotequal).
assert (Out H m C) by (conclude lemma_ray4).
assert (CongA H C B C H A) by (conclude lemma_equalangleshelper).
assert (CongA C H A H C B) by (conclude lemma_equalanglessymmetric).
assert (CongA A H C B C H) by (conclude lemma_equalanglesflip).
assert (nCol B C H) by (conclude lemma_equalanglesNC).
assert (CongA B C H H C B) by (conclude lemma_ABCequalsCBA).
assert (CongA A H C H C B) by (conclude lemma_equalanglestransitive).
assert (Col C m H) by (conclude_def Col ).
assert (Col H C m) by (forward_using lemma_collinearorder).
assert (Col H m C) by (forward_using lemma_collinearorder).
assert (eq H H) by (conclude cn_equalityreflexive).
assert (Col H m H) by (conclude_def Col ).
assert (neq H C) by (forward_using lemma_betweennotequal).
assert (nCol H C A) by (conclude lemma_NChelper).
assert (TS A H C B) by (conclude_def TS ).
assert (Par A H C B) by (conclude proposition_27B).
assert (Col H A E) by (conclude_def Col ).
assert (Col A H E) by (forward_using lemma_collinearorder).
assert (Col A H A) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (Par C B A H) by (conclude lemma_parallelsymmetric).
assert (Par C B A E) by (conclude lemma_collinearparallel2).
assert (Par A E C B) by (conclude lemma_parallelsymmetric).
assert (Par A E B C) by (forward_using lemma_parallelflip).
assert (ET A B C E B C) by (conclude proposition_37).
assert (ET D B C A B C) by (conclude axiom_ETsymmetric).
assert (ET D B C E B C) by (conclude axiom_ETtransitive).
assert (Out B M D) by (conclude lemma_ray5).
assert (neq B M) by (forward_using lemma_betweennotequal).
assert (Out B M E) by (conclude lemma_ray4).
assert (Out B D E) by (conclude lemma_ray3).
assert ((BetS B E D \/ eq D E \/ BetS B D E)) by (conclude lemma_ray1).
assert (Par A D B C).
by cases on (BetS B E D \/ eq D E \/ BetS B D E).
{
 assert (~ ~ Par A D B C).
  {
  intro.
  assert (~ ET D B C E B C) by (conclude axiom_deZolt1).
  contradict.
  }
 close.
 }
{
 assert (Par A D B C) by (conclude cn_equalitysub).
 close.
 }
{
 assert (~ ~ Par A D B C).
  {
  intro.
  assert (~ ET E B C D B C) by (conclude axiom_deZolt1).
  assert (ET E B C D B C) by (conclude axiom_ETsymmetric).
  contradict.
  }
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


