Require Export GeoCoq.Elements.OriginalProofs.proposition_23C.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angletrichotomy2 : 
   forall A B C D E F, 
   nCol A B C -> nCol D E F -> ~ CongA A B C D E F -> ~ LtA D E F A B C ->
   LtA A B C D E F.
Proof.
intros.
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ Col B A C).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists G J, (Out B A J /\ CongA G B J D E F /\ OS G C B A)) by (conclude proposition_23C);destruct Tf as [G[J]];spliter.
assert (nCol B A G) by (conclude_def OS ).
assert (~ eq B G).
 {
 intro.
 assert (Col B A G) by (conclude_def Col ).
 contradict.
 }
assert (~ eq A G).
 {
 intro.
 assert (Col B A G) by (conclude_def Col ).
 contradict.
 }
assert (CongA D E F G B J) by (conclude lemma_equalanglessymmetric).
assert (Out B J A) by (conclude lemma_ray5).
assert (eq G G) by (conclude cn_equalityreflexive).
assert (Out B G G) by (conclude lemma_ray4).
assert (CongA D E F G B A) by (conclude lemma_equalangleshelper).
assert (nCol G B A) by (conclude lemma_equalanglesNC).
assert (~ Col A B G).
 {
 intro.
 assert (Col B A G) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA G B A D E F) by (conclude lemma_equalanglessymmetric).
assert (CongA A B G G B A) by (conclude lemma_ABCequalsCBA).
assert (CongA A B G D E F) by (conclude lemma_equalanglestransitive).
assert (~ Col A B G).
 {
 intro.
 assert (Col G B A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq G A).
 {
 intro.
 assert (eq A G) by (conclude lemma_equalitysymmetric).
 assert (Col A B G) by (conclude_def Col ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists P, (BetS G A P /\ Cong A P G A)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col B A A) by (conclude_def Col ).
assert (~ Col B A G).
 {
 intro.
 assert (Col G B A) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (OS C G B A) by (forward_using lemma_samesidesymmetric).
assert (TS G B A P) by (conclude_def TS ).
assert (TS C B A P) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists R, (BetS C R P /\ Col B A R /\ nCol B A C)) by (conclude_def TS );destruct Tf as [R];spliter.
assert (BetS P R C) by (conclude axiom_betweennesssymmetry).
assert (LtA A B C D E F).
by cases on (TS G B C A \/ ~ TS G B C A).
{
 rename_H H;let Tf:=fresh in
 assert (Tf:exists H, (BetS G H A /\ Col B C H /\ nCol B C G)) by (conclude_def TS );destruct Tf as [H];spliter.
 assert (BetS A H G) by (conclude axiom_betweennesssymmetry).
 assert (Out B A A) by (conclude lemma_ray4).
 assert (~ Col A B H).
  {
  intro.
  assert (~ eq B H).
   {
   intro.
   assert (BetS A B G) by (conclude cn_equalitysub).
   assert (Col A B G) by (conclude_def Col ).
   assert (Col G B A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (neq H B) by (conclude lemma_inequalitysymmetric).
  assert (Col H B A) by (forward_using lemma_collinearorder).
  assert (Col H B C) by (forward_using lemma_collinearorder).
  assert (Col B A C) by (conclude lemma_collinear4).
  assert (Col A B C) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA A B H A B H) by (conclude lemma_equalanglesreflexive).
 assert (LtA A B H A B G) by (conclude_def LtA ).
 assert (CongA G B A A B G) by (conclude lemma_ABCequalsCBA).
 assert (LtA A B H G B A) by (conclude lemma_angleorderrespectscongruence).
 assert (~ Col H B A).
  {
  intro.
  assert (Col A B H) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (CongA H B A A B H) by (conclude lemma_ABCequalsCBA).
 assert (LtA H B A G B A) by (conclude lemma_angleorderrespectscongruence2).
 assert (LtA H B A D E F) by (conclude lemma_angleorderrespectscongruence).
 assert (CongA A B H H B A) by (conclude lemma_ABCequalsCBA).
 assert (LtA A B H D E F) by (conclude lemma_angleorderrespectscongruence2).
 assert (Out B A A) by (conclude lemma_ray4).
 assert (OS C G B A) by (forward_using lemma_samesidesymmetric).
 assert (Out A G H) by (conclude lemma_ray4).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col B A A) by (conclude_def Col ).
 assert (OS C H B A) by (conclude lemma_sameside2).
 assert (~ BetS C B H).
  {
  intro.
  assert (eq B B) by (conclude cn_equalityreflexive).
  assert (Col B A B) by (conclude_def Col ).
  assert (TS C B A H) by (conclude_def TS ).
  assert (TS H B A C) by (conclude lemma_oppositesidesymmetric).
  assert (TS C B A C) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists M, (BetS C M C /\ Col B A M /\ nCol B A C)) by (conclude_def TS );destruct Tf as [M];spliter.
  assert (~ BetS C M C) by (conclude axiom_betweennessidentity).
  contradict.
  }
 assert ((eq B C \/ eq B H \/ eq C H \/ BetS C B H \/ BetS B C H \/ BetS B H C)) by (conclude_def Col ).
 assert (Out B C H).
 by cases on (eq B C \/ eq B H \/ eq C H \/ BetS C B H \/ BetS B C H \/ BetS B H C).
 {
  assert (Col A B C) by (conclude_def Col ).
  assert (~ ~ Out B C H).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (Col B H A) by (conclude_def Col ).
  assert (~ ~ Out B C H).
   {
   intro.
   assert (~ Col B H A).
    {
    intro.
    assert (Col H B A) by (forward_using lemma_collinearorder).
    contradict.
    }
   contradict.
   }
  close.
  }
 {
  assert (eq H H) by (conclude cn_equalityreflexive).
  assert (Out B C H).
  by cases on (eq B H \/ neq B H).
  {
   assert (Col B H A) by (conclude_def Col ).
   assert (~ ~ Out B C H).
    {
    intro.
    assert (~ Col B H A).
     {
     intro.
     assert (Col H B A) by (forward_using lemma_collinearorder).
     contradict.
     }
    contradict.
    }
   close.
   }
  {
   assert (Out B H H) by (conclude lemma_ray4).
   assert (Out B C H) by (conclude cn_equalitysub).
   close.
   }
(** cases *)
  close.
  }
 {
  assert (~ ~ Out B C H).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (neq B C) by (forward_using lemma_betweennotequal).
  assert (Out B C H) by (conclude lemma_ray4).
  close.
  }
 {
  assert (neq B C) by (forward_using lemma_betweennotequal).
  assert (Out B C H) by (conclude lemma_ray4).
  close.
  }
(** cases *)
 assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
 assert (CongA A B C A B H) by (conclude lemma_equalangleshelper).
 assert (LtA A B C D E F) by (conclude lemma_angleorderrespectscongruence2).
 close.
 }
{
 assert ((eq B A \/ eq B R \/ eq A R \/ BetS A B R \/ BetS B A R \/ BetS B R A)) by (conclude_def Col ).
 assert (LtA A B C D E F).
 by cases on (eq B A \/ eq B R \/ eq A R \/ BetS A B R \/ BetS B A R \/ BetS B R A).
 {
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (eq R B) by (conclude lemma_equalitysymmetric).
  assert (BetS C R P) by (conclude axiom_betweennesssymmetry).
  assert (~ Col C P G).
   {
   intro.
   assert (Col C R P) by (conclude_def Col ).
   assert (Col C B P) by (conclude cn_equalitysub).
   assert (Col G A P) by (conclude_def Col ).
   assert (Col G P A) by (forward_using lemma_collinearorder).
   assert (Col G P C) by (forward_using lemma_collinearorder).
   assert (neq G P) by (forward_using lemma_betweennotequal).
   assert (Col P C A) by (conclude lemma_collinear4).
   assert (Col P C B) by (forward_using lemma_collinearorder).
   assert (neq C P) by (forward_using lemma_betweennotequal).
   assert (neq P C) by (conclude lemma_inequalitysymmetric).
   assert (Col C A B) by (conclude lemma_collinear4).
   assert (Col A B C) by (forward_using lemma_collinearorder).
   contradict.
   }
  let Tf:=fresh in
  assert (Tf:exists Q, (BetS C Q A /\ BetS G Q R)) by (conclude postulate_Pasch_inner);destruct Tf as [Q];spliter.
  assert (BetS G Q B) by (conclude cn_equalitysub).
  assert (BetS B Q G) by (conclude axiom_betweennesssymmetry).
  assert (neq B Q) by (forward_using lemma_betweennotequal).
  assert (neq B G) by (forward_using lemma_betweennotequal).
  assert (Out B Q G) by (conclude lemma_ray4).
  assert (Out B G Q) by (conclude lemma_ray5).
  assert (eq Q Q) by (conclude cn_equalityreflexive).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (eq C C) by (conclude cn_equalityreflexive).
  assert (Out B A A) by (conclude lemma_ray4).
  assert (Out B C C) by (conclude lemma_ray4).
  assert (Out B G G) by (conclude lemma_ray4).
  assert (Out B Q Q) by (conclude lemma_ray4).
  assert (Cong A Q A Q) by (conclude cn_congruencereflexive).
  assert (Cong B Q B Q) by (conclude cn_congruencereflexive).
  assert (Cong B A B A) by (conclude cn_congruencereflexive).
  assert (CongA A B G A B Q) by (conclude_def CongA ).
  assert (BetS A Q C) by (conclude axiom_betweennesssymmetry).
  assert (LtA A B G A B C) by (conclude_def LtA ).
  assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
  assert (LtA D E F A B C) by (conclude lemma_angleorderrespectscongruence2).
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
   assert (BetS P A C) by (conclude cn_equalitysub).
   assert (eq G G) by (conclude cn_equalityreflexive).
   assert (Out B G G) by (conclude lemma_ray4).
   assert (eq A A) by (conclude cn_equalityreflexive).
   assert (Out B A A) by (conclude lemma_ray4).
   assert (eq C C) by (conclude cn_equalityreflexive).
   assert (Out B C C) by (conclude lemma_ray4).
   assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
   assert (~ BetS A G C).
    {
    intro.
    assert (CongA A B G A B G) by (conclude lemma_equalanglesreflexive).
    assert (LtA A B G A B C) by (conclude_def LtA ).
    assert (LtA D E F A B C) by (conclude lemma_angleorderrespectscongruence2).
    contradict.
    }
   assert (~ BetS A C G).
    {
    intro.
    assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
    assert (LtA A B C A B G) by (conclude_def LtA ).
    assert (LtA A B C D E F) by (conclude lemma_angleorderrespectscongruence).
    contradict.
    }
   assert (eq C G) by (conclude lemma_outerconnectivity).
   assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
   assert (CongA A B G A B C) by (conclude cn_equalitysub).
   assert (CongA A B C A B G) by (conclude lemma_equalanglessymmetric).
   assert (CongA A B C D E F) by (conclude lemma_equalanglestransitive).
   contradict.
   }
  close.
  }
 {
  assert (BetS R B A) by (conclude axiom_betweennesssymmetry).
  assert (BetS A B R) by (conclude axiom_betweennesssymmetry).
  assert (~ Col C P A).
   {
   intro.
   assert (Col C R P) by (conclude_def Col ).
   assert (Col C P R) by (forward_using lemma_collinearorder).
   assert (neq C P) by (forward_using lemma_betweennotequal).
   assert (Col P A R) by (conclude lemma_collinear4).
   assert (Col R B A) by (conclude_def Col ).
   assert (Col R A B) by (forward_using lemma_collinearorder).
   assert (Col R A P) by (forward_using lemma_collinearorder).
   assert (neq R A) by (forward_using lemma_betweennotequal).
   assert (Col A B P) by (conclude lemma_collinear4).
   assert (Col P A B) by (forward_using lemma_collinearorder).
   assert (Col G A P) by (conclude_def Col ).
   assert (Col P A G) by (forward_using lemma_collinearorder).
   assert (neq A P) by (forward_using lemma_betweennotequal).
   assert (neq P A) by (conclude lemma_inequalitysymmetric).
   assert (Col A B G) by (conclude lemma_collinear4).
   contradict.
   }
  let Tf:=fresh in
  assert (Tf:exists M, (BetS A M P /\ BetS C B M)) by (conclude postulate_Pasch_outer);destruct Tf as [M];spliter.
  assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
  assert (BetS P M A) by (conclude axiom_betweennesssymmetry).
  assert (BetS M A G) by (conclude lemma_3_6a).
  assert (BetS G A M) by (conclude axiom_betweennesssymmetry).
  assert (~ Col C M G).
   {
   intro.
   assert (BetS P M A) by (conclude axiom_betweennesssymmetry).
   assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
   assert (BetS P M G) by (conclude lemma_3_6b).
   assert (Col P M G) by (conclude_def Col ).
   assert (Col M G P) by (forward_using lemma_collinearorder).
   assert (Col M G C) by (forward_using lemma_collinearorder).
   assert (neq M G) by (forward_using lemma_betweennotequal).
   assert (Col G P C) by (conclude lemma_collinear4).
   assert (Col P A G) by (conclude_def Col ).
   assert (Col G P A) by (forward_using lemma_collinearorder).
   assert (neq P G) by (forward_using lemma_betweennotequal).
   assert (neq G P) by (conclude lemma_inequalitysymmetric).
   assert (Col P C A) by (conclude lemma_collinear4).
   assert (Col C P A) by (forward_using lemma_collinearorder).
   contradict.
   }
  let Tf:=fresh in
  assert (Tf:exists Q, (BetS C Q A /\ BetS G Q B)) by (conclude postulate_Pasch_inner);destruct Tf as [Q];spliter.
  assert (BetS B Q G) by (conclude axiom_betweennesssymmetry).
  assert (neq B Q) by (forward_using lemma_betweennotequal).
  assert (neq B G) by (forward_using lemma_betweennotequal).
  assert (Out B Q G) by (conclude lemma_ray4).
  assert (Out B G Q) by (conclude lemma_ray5).
  assert (eq Q Q) by (conclude cn_equalityreflexive).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (eq C C) by (conclude cn_equalityreflexive).
  assert (Out B A A) by (conclude lemma_ray4).
  assert (Out B C C) by (conclude lemma_ray4).
  assert (Out B G G) by (conclude lemma_ray4).
  assert (Out B Q Q) by (conclude lemma_ray4).
  assert (Cong A Q A Q) by (conclude cn_congruencereflexive).
  assert (Cong B Q B Q) by (conclude cn_congruencereflexive).
  assert (Cong B A B A) by (conclude cn_congruencereflexive).
  assert (CongA A B G A B Q) by (conclude_def CongA ).
  assert (BetS A Q C) by (conclude axiom_betweennesssymmetry).
  assert (LtA A B G A B C) by (conclude_def LtA ).
  assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
  assert (LtA D E F A B C) by (conclude lemma_angleorderrespectscongruence2).
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ Col P C B).
   {
   intro.
   assert (Col B A R) by (conclude_def Col ).
   assert (Col P R C) by (conclude_def Col ).
   assert (Col P C R) by (forward_using lemma_collinearorder).
   assert (neq P C) by (forward_using lemma_betweennotequal).
   assert (Col C B R) by (conclude lemma_collinear4).
   assert (Col R B C) by (forward_using lemma_collinearorder).
   assert (Col R B A) by (forward_using lemma_collinearorder).
   assert (neq B R) by (forward_using lemma_betweennotequal).
   assert (neq R B) by (conclude lemma_inequalitysymmetric).
   assert (Col B C A) by (conclude lemma_collinear4).
   assert (Col A B C) by (forward_using lemma_collinearorder).
   contradict.
   }
  let Tf:=fresh in
  assert (Tf:exists Q, (BetS B Q C /\ BetS P A Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
  assert (Col B C Q) by (conclude_def Col ).
  assert (~ eq G Q).
   {
   intro.
   assert (BetS B G C) by (conclude cn_equalitysub).
   assert (Out B C G) by (conclude lemma_ray4).
   assert (Out B A A) by (conclude lemma_ray4).
   assert (Out B G G) by (conclude lemma_ray4).
   assert (Cong A G A G) by (conclude cn_congruencereflexive).
   assert (Cong B G B G) by (conclude cn_congruencereflexive).
   assert (Cong B A B A) by (conclude cn_congruencereflexive).
   assert (CongA A B G A B C) by (conclude_def CongA ).
   assert (CongA A B C A B G) by (conclude lemma_equalanglessymmetric).
   assert (CongA A B C D E F) by (conclude lemma_equalanglestransitive).
   contradict.
   }
  assert (~ Col B C G).
   {
   intro.
   assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
   assert (Out A G Q) by (conclude_def Out ).
   assert (Col A G Q) by (conclude lemma_rayimpliescollinear).
   assert (Col Q C B) by (forward_using lemma_collinearorder).
   assert (Col C B G) by (forward_using lemma_collinearorder).
   assert (Col C B Q) by (forward_using lemma_collinearorder).
   assert (neq B C) by (forward_using lemma_betweennotequal).
   assert (neq C B) by (conclude lemma_inequalitysymmetric).
   assert (eq B B) by (conclude cn_equalityreflexive).
   assert (Col C B B) by (conclude_def Col ).
   assert (Col G Q B) by (conclude lemma_collinear5).
   assert (Col Q G B) by (forward_using lemma_collinearorder).
   assert (Col Q G A) by (forward_using lemma_collinearorder).
   assert (neq Q G) by (conclude lemma_inequalitysymmetric).
   assert (Col G B A) by (conclude lemma_collinear4).
   assert (Col A B G) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (~ BetS A Q G).
   {
   intro.
   assert (BetS G Q A) by (conclude axiom_betweennesssymmetry).
   assert (TS G B C A) by (conclude_def TS ).
   contradict.
   }
  assert (Out B C Q) by (conclude lemma_ray4).
  assert (Out B A A) by (conclude lemma_ray4).
  assert (~ BetS A G Q).
   {
   intro.
   assert (CongA A B G A B G) by (conclude lemma_equalanglesreflexive).
   assert (LtA A B G A B C) by (conclude_def LtA ).
   assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
   assert (LtA D E F A B C) by (conclude lemma_angleorderrespectscongruence2).
   contradict.
   }
  assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
  assert (eq G Q) by (conclude lemma_outerconnectivity).
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ LtA A B C D E F).
   {
   intro.
   assert (BetS P A G) by (conclude axiom_betweennesssymmetry).
   assert (~ Col P G B).
    {
    intro.
    assert (Col P A G) by (conclude_def Col ).
    assert (Col P G A) by (forward_using lemma_collinearorder).
    assert (neq P G) by (forward_using lemma_betweennotequal).
    assert (Col G B A) by (conclude lemma_collinear4).
    assert (Col A B G) by (forward_using lemma_collinearorder).
    contradict.
    }
   let Tf:=fresh in
   assert (Tf:exists Q, (BetS B Q G /\ BetS P R Q)) by (conclude postulate_Pasch_outer);destruct Tf as [Q];spliter.
   assert (neq Q G) by (forward_using lemma_betweennotequal).
   assert (neq B Q) by (forward_using lemma_betweennotequal).
   assert (Out B A A) by (conclude lemma_ray4).
   assert (Out B G Q) by (conclude lemma_ray4).
   assert (Out B Q G) by (conclude lemma_ray4).
   assert (~ BetS R C Q).
    {
    intro.
    assert (Out B A R) by (conclude lemma_ray4).
    assert (Out B G Q) by (conclude lemma_ray4).
    assert (CongA A B C A B C) by (conclude lemma_equalanglesreflexive).
    assert (LtA A B C A B G) by (conclude_def LtA ).
    assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
    assert (LtA A B C D E F) by (conclude lemma_angleorderrespectscongruence).
    contradict.
    }
   assert (~ BetS R Q C).
    {
    intro.
    assert (eq A A) by (conclude cn_equalityreflexive).
    assert (Out B A A) by (conclude lemma_ray4).
    assert (Out B Q G) by (conclude lemma_ray4).
    assert (eq G G) by (conclude cn_equalityreflexive).
    assert (Out B G G) by (conclude lemma_ray4).
    assert (Cong B A B A) by (conclude cn_congruencereflexive).
    assert (Cong B G B G) by (conclude cn_congruencereflexive).
    assert (Cong A G A G) by (conclude cn_congruencereflexive).
    assert (CongA A B G A B Q) by (conclude_def CongA ).
    assert (Out B A R) by (conclude lemma_ray4).
    assert (eq C C) by (conclude cn_equalityreflexive).
    assert (Out B C C) by (conclude lemma_ray4).
    assert (LtA A B G A B C) by (conclude_def LtA ).
    assert (CongA D E F A B G) by (conclude lemma_equalanglessymmetric).
    assert (LtA D E F A B C) by (conclude lemma_angleorderrespectscongruence2).
    contradict.
    }
   assert (eq Q C) by (conclude lemma_outerconnectivity).
   assert (eq C C) by (conclude cn_equalityreflexive).
   assert (Out B C C) by (conclude lemma_ray4).
   assert (Out B C G) by (conclude cn_equalitysub).
   assert (eq A A) by (conclude cn_equalityreflexive).
   assert (Out B A A) by (conclude lemma_ray4).
   assert (Out B Q G) by (conclude lemma_ray4).
   assert (eq G G) by (conclude cn_equalityreflexive).
   assert (Out B G G) by (conclude lemma_ray4).
   assert (Cong B A B A) by (conclude cn_congruencereflexive).
   assert (Cong B G B G) by (conclude cn_congruencereflexive).
   assert (Cong A G A G) by (conclude cn_congruencereflexive).
   assert (CongA A B G A B Q) by (conclude_def CongA ).
   assert (CongA A B C A B G) by (conclude_def CongA ).
   assert (CongA A B C D E F) by (conclude lemma_equalanglestransitive).
   contradict.
   }
  close.
  }
(** cases *)
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


