Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_19.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma proposition_24 : 
   forall A B C D E F, 
   Triangle A B C -> Triangle D E F -> Cong A B D E -> Cong A C D F -> LtA E D F B A C ->
   Lt E F B C.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists P Q T, (BetS P T Q /\ Out A B P /\ Out A C Q /\ CongA E D F B A T)) by (conclude_def LtA );destruct Tf as [P[Q[T]]];spliter.
assert (nCol B A T) by (conclude lemma_equalanglesNC).
assert (~ eq A T).
 {
 intro.
 assert (Col B A T) by (conclude_def Col ).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (Out A T H /\ Cong A H A C)) by (conclude lemma_layoff);destruct Tf as [H];spliter.
assert (Cong A H D F) by (conclude lemma_congruencetransitive).
assert (~ Col H A B).
 {
 intro.
 assert (Col A T H) by (conclude lemma_rayimpliescollinear).
 assert (Col H A T) by (forward_using lemma_collinearorder).
 assert (neq A H) by (conclude lemma_raystrict).
 assert (neq H A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B T) by (conclude lemma_collinear4).
 assert (Col B A T) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq H B).
 {
 intro.
 assert (Col H A B) by (conclude_def Col ).
 contradict.
 }
assert (eq B B) by (conclude cn_equalityreflexive).
assert (Out A B B) by (conclude lemma_ray4).
assert (CongA E D F B A H) by (conclude lemma_equalangleshelper).
assert (CongA B A H E D F) by (conclude lemma_equalanglessymmetric).
assert (CongA H A B F D E) by (conclude lemma_equalanglesflip).
assert ((Cong H B F E /\ CongA A H B D F E /\ CongA A B H D E F)) by (conclude proposition_04).
assert (Out A Q C) by (conclude lemma_ray5).
assert (Out A P B) by (conclude lemma_ray5).
assert (Col A Q C) by (conclude lemma_rayimpliescollinear).
assert (Col A P B) by (conclude lemma_rayimpliescollinear).
assert (~ Col Q A P).
 {
 intro.
 assert (Col A P Q) by (forward_using lemma_collinearorder).
 assert (Col Q A C) by (forward_using lemma_collinearorder).
 assert (Col Q A P) by (forward_using lemma_collinearorder).
 assert (neq A Q) by (conclude lemma_ray2).
 assert (neq Q A) by (conclude lemma_inequalitysymmetric).
 assert (Col A C P) by (conclude lemma_collinear4).
 assert (Col P A B) by (forward_using lemma_collinearorder).
 assert (Col P A C) by (forward_using lemma_collinearorder).
 assert (neq A P) by (conclude lemma_raystrict).
 assert (neq P A) by (conclude lemma_inequalitysymmetric).
 assert (Col A B C) by (conclude lemma_collinear4).
 contradict.
 }
assert (Triangle Q A P) by (conclude_def Triangle ).
assert (BetS Q T P) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists J, (Out A T J /\ BetS C J B)) by (conclude lemma_crossbar);destruct Tf as [J];spliter.
assert (Out A J H) by (conclude lemma_ray3).
assert (Cong A C A H) by (conclude lemma_congruencesymmetric).
assert (~ Col A C H).
 {
 intro.
 assert (Col H A C) by (forward_using lemma_collinearorder).
 assert (neq A H) by (conclude lemma_raystrict).
 assert (neq H A) by (conclude lemma_inequalitysymmetric).
 assert (Col A J H) by (conclude lemma_rayimpliescollinear).
 assert (Col H A J) by (forward_using lemma_collinearorder).
 assert (Col A C J) by (conclude lemma_collinear4).
 assert (Col C J B) by (conclude_def Col ).
 assert (Col C J A) by (forward_using lemma_collinearorder).
 assert (neq C J) by (forward_using lemma_betweennotequal).
 assert (Col J B A) by (conclude lemma_collinear4).
 assert (Col A T J) by (conclude lemma_rayimpliescollinear).
 assert (Col J A T) by (forward_using lemma_collinearorder).
 assert (Col J A B) by (forward_using lemma_collinearorder).
 assert (neq A J) by (conclude lemma_raystrict).
 assert (neq J A) by (conclude lemma_inequalitysymmetric).
 assert (Col A T B) by (conclude lemma_collinear4).
 assert (Col B A T) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (Triangle A C H) by (conclude_def Triangle ).
assert (isosceles A C H) by (conclude_def isosceles ).
assert (CongA A C H A H C) by (conclude proposition_05).
assert ((BetS A H J \/ eq J H \/ BetS A J H)) by (conclude lemma_ray1).
assert (Lt H B C B).
by cases on (BetS A H J \/ eq J H \/ BetS A J H).
{
 assert (~ Col C J H).
  {
  intro.
  assert (Col A H J) by (conclude_def Col ).
  assert (Col J H A) by (forward_using lemma_collinearorder).
  assert (Col J H C) by (forward_using lemma_collinearorder).
  assert (neq H J) by (forward_using lemma_betweennotequal).
  assert (neq J H) by (conclude lemma_inequalitysymmetric).
  assert (Col H A C) by (conclude lemma_collinear4).
  assert (Col A C H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Triangle C J H) by (conclude_def Triangle ).
 assert (BetS J H A) by (conclude axiom_betweennesssymmetry).
 assert (LtA J C H C H A) by (conclude proposition_16).
 assert (~ Col H C J).
  {
  intro.
  assert (Col C J H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA H C J J C H) by (conclude lemma_ABCequalsCBA).
 assert (LtA H C J C H A) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ Col A H C).
  {
  intro.
  assert (Col A C H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA A H C C H A) by (conclude lemma_ABCequalsCBA).
 assert (LtA H C J A H C) by (conclude lemma_angleorderrespectscongruence).
 assert (Out H B B) by (conclude lemma_ray4).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (~ Col C H J).
  {
  intro.
  assert (Col C J H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (~ eq C H).
  {
  intro.
  assert (Col C H J) by (conclude_def Col ).
  contradict.
  }
 assert (neq H C) by (conclude lemma_inequalitysymmetric).
 assert (Out H C C) by (conclude lemma_ray4).
 assert (CongA C H J C H J) by (conclude lemma_equalanglesreflexive).
 assert (neq C J) by (forward_using lemma_angledistinct).
 assert (neq C H) by (forward_using lemma_angledistinct).
 assert (LtA C H J C H B) by (conclude_def LtA ).
 assert (~ Col C A H).
  {
  intro.
  assert (Col A C H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Triangle C A H) by (conclude_def Triangle ).
 assert (LtA A C H C H J) by (conclude proposition_16).
 assert (LtA H C J A C H) by (conclude lemma_angleorderrespectscongruence).
 assert (LtA H C J C H J) by (conclude lemma_angleordertransitive).
 assert (LtA H C J C H B) by (conclude lemma_angleordertransitive).
 assert (eq H H) by (conclude cn_equalityreflexive).
 assert (Out C H H) by (conclude lemma_ray4).
 assert (Out C J B) by (conclude lemma_ray4).
 assert (CongA H C J H C J) by (conclude lemma_equalanglesreflexive).
 assert (CongA H C J H C B) by (conclude lemma_equalangleshelper).
 assert (CongA H C B H C J) by (conclude lemma_equalanglessymmetric).
 assert (LtA H C B C H B) by (conclude lemma_angleorderrespectscongruence2).
 assert (~ Col B H C).
  {
  intro.
  assert (Col C J B) by (conclude_def Col ).
  assert (Col B C H) by (forward_using lemma_collinearorder).
  assert (Col B C J) by (forward_using lemma_collinearorder).
  assert (neq C B) by (forward_using lemma_betweennotequal).
  assert (neq B C) by (conclude lemma_inequalitysymmetric).
  assert (Col C H J) by (conclude lemma_collinear4).
  contradict.
  }
 assert (Triangle B H C) by (conclude_def Triangle ).
 assert (CongA B H C C H B) by (conclude lemma_ABCequalsCBA).
 assert (LtA H C B B H C) by (conclude lemma_angleorderrespectscongruence).
 assert (Lt B H B C) by (conclude proposition_19).
 assert (Cong B H H B) by (conclude cn_equalityreverse).
 assert (Lt H B B C) by (conclude lemma_lessthancongruence2).
 assert (Cong B C C B) by (conclude cn_equalityreverse).
 assert (Lt H B C B) by (conclude lemma_lessthancongruence).
 close.
 }
{
 assert (BetS C H B) by (conclude cn_equalitysub).
 assert (BetS B H C) by (conclude axiom_betweennesssymmetry).
 assert (Cong B H H B) by (conclude cn_equalityreverse).
 assert (Lt H B B C) by (conclude_def Lt ).
 assert (Cong B C C B) by (conclude cn_equalityreverse).
 assert (Lt H B C B) by (conclude lemma_lessthancongruence).
 close.
 }
{
 assert (BetS H J A) by (conclude axiom_betweennesssymmetry).
 assert (~ Col C J H).
  {
  intro.
  assert (Col A H J) by (conclude_def Col ).
  assert (Col J H A) by (forward_using lemma_collinearorder).
  assert (Col J H C) by (forward_using lemma_collinearorder).
  assert (neq H J) by (forward_using lemma_betweennotequal).
  assert (neq J H) by (conclude lemma_inequalitysymmetric).
  assert (Col H A C) by (conclude lemma_collinear4).
  assert (Col A C H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (~ Col H C B).
  {
  intro.
  assert (Col C J B) by (conclude_def Col ).
  assert (Col B C J) by (forward_using lemma_collinearorder).
  assert (Col B C H) by (forward_using lemma_collinearorder).
  assert (neq C B) by (forward_using lemma_betweennotequal).
  assert (neq B C) by (conclude lemma_inequalitysymmetric).
  assert (Col C H J) by (conclude lemma_collinear4).
  assert (Col C J H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (eq H H) by (conclude cn_equalityreflexive).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (~ eq C H).
  {
  intro.
  assert (Col C H B) by (conclude_def Col ).
  assert (Col H C B) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Out C A A) by (conclude lemma_ray4).
 assert (CongA H C B H C B) by (conclude lemma_equalanglesreflexive).
 assert (Out C B J) by (conclude lemma_ray4).
 assert (Out C H H) by (conclude lemma_ray4).
 assert (CongA H C B H C J) by (conclude lemma_equalangleshelper).
 assert (BetS H J A) by (conclude axiom_betweennesssymmetry).
 assert (LtA H C B H C A) by (conclude_def LtA ).
 assert (~ Col B C H).
  {
  intro.
  assert (Col H C B) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA B C H H C B) by (conclude lemma_ABCequalsCBA).
 assert (LtA B C H H C A) by (conclude lemma_angleorderrespectscongruence2).
 assert (CongA A C H H C A) by (conclude lemma_ABCequalsCBA).
 assert (LtA B C H A C H) by (conclude lemma_angleorderrespectscongruence).
 assert (CongA A H C A C H) by (conclude lemma_equalanglessymmetric).
 assert (LtA B C H A H C) by (conclude lemma_angleorderrespectscongruence).
 assert (~ Col A H C).
  {
  intro.
  assert (Col A C H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA A H C C H A) by (conclude lemma_ABCequalsCBA).
 assert (eq C C) by (conclude cn_equalityreflexive).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (neq H B) by (forward_using lemma_angledistinct).
 assert (neq H C) by (forward_using lemma_angledistinct).
 assert (neq H A) by (forward_using lemma_angledistinct).
 assert (Out H C C) by (conclude lemma_ray4).
 assert (Out H B B) by (conclude lemma_ray4).
 assert (Out H A J) by (conclude lemma_ray4).
 assert (CongA A H C C H J) by (conclude lemma_equalangleshelper).
 assert (LtA A H C C H B) by (conclude_def LtA ).
 assert (~ Col B H C).
  {
  intro.
  assert (Col H C B) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA B H C C H B) by (conclude lemma_ABCequalsCBA).
 assert (LtA A H C B H C) by (conclude lemma_angleorderrespectscongruence).
 assert (LtA B C H B H C) by (conclude lemma_angleordertransitive).
 assert (~ Col H C B).
  {
  intro.
  assert (Col B H C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA H C B B C H) by (conclude lemma_ABCequalsCBA).
 assert (LtA H C B B H C) by (conclude lemma_angleorderrespectscongruence2).
 assert (Triangle B H C) by (conclude_def Triangle ).
 assert (Lt B H B C) by (conclude proposition_19).
 assert (Cong B H H B) by (conclude cn_equalityreverse).
 assert (Lt H B B C) by (conclude lemma_lessthancongruence2).
 assert (Cong B C C B) by (conclude cn_equalityreverse).
 assert (Lt H B C B) by (conclude lemma_lessthancongruence).
 close.
 }
(** cases *)
assert (Cong F E E F) by (conclude cn_equalityreverse).
assert (Cong H B E F) by (conclude lemma_congruencetransitive).
assert (Lt E F C B) by (conclude lemma_lessthancongruence2).
assert (Cong C B B C) by (conclude cn_equalityreverse).
assert (Lt E F B C) by (conclude lemma_lessthancongruence).
close.
Qed.

End Euclid.
