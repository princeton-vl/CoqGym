Require Export GeoCoq.Elements.OriginalProofs.lemma_twolines2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5b.
Require Export GeoCoq.Elements.OriginalProofs.lemma_9_5a.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear5.
Require Export GeoCoq.Elements.OriginalProofs.proposition_10.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_planeseparation : 
   forall A B C D E, 
   OS C D A B -> TS D A B E ->
   TS C A B E.
Proof.
intros.
rename_H H;
let Tf:=fresh in
assert (Tf:exists G H Q, (Col A B G /\ Col A B H /\ BetS C G Q /\ BetS D H Q /\ nCol A B C /\ nCol A B D)) by (conclude_def OS );destruct Tf as [G[H[Q]]];spliter.
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists W, (BetS D W E /\ Col A B W /\ nCol A B D)) by (conclude_def TS );destruct Tf as [W];spliter.
assert (neq C G) by (forward_using lemma_betweennotequal).
assert (neq G C) by (conclude lemma_inequalitysymmetric).
assert (neq G Q) by (forward_using lemma_betweennotequal).
assert (TS C A B E).
by cases on (Col C Q D \/ nCol C Q D).
{
 assert (~ ~ TS C A B E).
  {
  intro.
  assert (Col Q C D) by (forward_using lemma_collinearorder).
  assert (~ neq G H).
   {
   intro.
   assert (neq D Q) by (forward_using lemma_betweennotequal).
   assert (Col C G Q) by (conclude_def Col ).
   assert (Col D H Q) by (conclude_def Col ).
   assert (Col Q C G) by (forward_using lemma_collinearorder).
   assert (neq C Q) by (forward_using lemma_betweennotequal).
   assert (neq Q C) by (conclude lemma_inequalitysymmetric).
   assert (Col C G D) by (conclude lemma_collinear4).
   assert (Col D Q H) by (forward_using lemma_collinearorder).
   assert (Col D Q C) by (forward_using lemma_collinearorder).
   assert (Col Q H C) by (conclude lemma_collinear4).
   assert (Col Q C H) by (forward_using lemma_collinearorder).
   assert (~ Col C A B).
    {
    intro.
    assert (Col A B C) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (~ (Col C A B /\ Col D A B)).
    {
    intro.
    contradict.
    }
   assert (Col G A B) by (forward_using lemma_collinearorder).
   assert (Col H A B) by (forward_using lemma_collinearorder).
   assert (Col G C D) by (forward_using lemma_collinearorder).
   assert (Col Q D H) by (forward_using lemma_collinearorder).
   assert (Col Q D C) by (forward_using lemma_collinearorder).
   assert (neq D Q) by (forward_using lemma_betweennotequal).
   assert (neq Q D) by (conclude lemma_inequalitysymmetric).
   assert (Col D C H) by (conclude lemma_collinear4).
   assert (Col H C D) by (forward_using lemma_collinearorder).
   assert (~ eq C D).
    {
    intro.
    assert (TS C A B E) by (conclude cn_equalitysub).
    contradict.
    }
   assert (eq G H) by (conclude lemma_twolines2).
   contradict.
   }
  assert (BetS Q G C) by (conclude axiom_betweennesssymmetry).
  assert (BetS Q H D) by (conclude axiom_betweennesssymmetry).
  assert (BetS Q G D) by (conclude cn_equalitysub).
  assert (~ nCol E D G).
   {
   intro.
   assert (~ nCol E C G).
    {
    intro.
    assert (~ BetS G C D).
     {
     intro.
     assert (TS C A B E) by (conclude lemma_9_5b).
     contradict.
     }
    assert (~ BetS G D C).
     {
     intro.
     assert (~ Col G C E).
      {
      intro.
      assert (Col E C G) by (forward_using lemma_collinearorder).
      contradict.
      }
     assert (TS C A B E) by (conclude lemma_9_5a).
     contradict.
     }
    assert (eq C D) by (conclude lemma_outerconnectivity).
    assert (TS C A B E) by (conclude cn_equalitysub).
    contradict.
    }
   assert (Col C G E) by (forward_using lemma_collinearorder).
   assert (Col Q G D) by (conclude_def Col ).
   assert (Col Q G C) by (conclude_def Col ).
   assert (neq Q G) by (forward_using lemma_betweennotequal).
   assert (Col G D C) by (conclude lemma_collinear4).
   assert (Col C G D) by (forward_using lemma_collinearorder).
   assert (Col C G E) by (forward_using lemma_collinearorder).
   assert (neq G C) by (forward_using lemma_betweennotequal).
   assert (neq C G) by (conclude lemma_inequalitysymmetric).
   assert (Col G D E) by (conclude lemma_collinear4).
   assert (Col E D G) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Col D G E) by (forward_using lemma_collinearorder).
  assert (Col D H Q) by (conclude_def Col ).
  assert (Col D G Q) by (conclude cn_equalitysub).
  assert (neq G D) by (forward_using lemma_betweennotequal).
  assert (neq D G) by (conclude lemma_inequalitysymmetric).
  assert (Col G E Q) by (conclude lemma_collinear4).
  assert (Col G E D) by (forward_using lemma_collinearorder).
  assert (Col D W E) by (conclude_def Col ).
  assert (Col D E W) by (forward_using lemma_collinearorder).
  assert (Col D E G) by (forward_using lemma_collinearorder).
  assert (neq D E) by (forward_using lemma_betweennotequal).
  assert (Col E W G) by (conclude lemma_collinear4).
  assert (Col E W D) by (forward_using lemma_collinearorder).
  assert (neq W E) by (forward_using lemma_betweennotequal).
  assert (neq E W) by (conclude lemma_inequalitysymmetric).
  assert (Col W G D) by (conclude lemma_collinear4).
  assert (Col B W G) by (conclude lemma_collinear4).
  assert (Col W G B) by (forward_using lemma_collinearorder).
  assert (Col B A W) by (forward_using lemma_collinearorder).
  assert (Col B A G) by (forward_using lemma_collinearorder).
  assert (Col A W G) by (conclude lemma_collinear4).
  assert (Col W G A) by (forward_using lemma_collinearorder).
  assert (~ neq W G).
   {
   intro.
   assert (Col G D B) by (conclude lemma_collinear4).
   assert (Col G B D) by (forward_using lemma_collinearorder).
   assert (Col G B A) by (forward_using lemma_collinearorder).
   assert (~ neq G B).
    {
    intro.
    assert (Col B D A) by (conclude lemma_collinear4).
    assert (Col A B D) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (Col G D A) by (conclude lemma_collinear4).
   assert (Col G A D) by (forward_using lemma_collinearorder).
   assert (Col G A B) by (forward_using lemma_collinearorder).
   assert (~ neq G A).
    {
    intro.
    assert (Col A D B) by (conclude lemma_collinear4).
    assert (Col A B D) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (eq A G) by (conclude lemma_equalitysymmetric).
   assert (eq B G) by (conclude lemma_equalitysymmetric).
   assert (eq A B) by (conclude cn_equalitytransitive).
   contradict.
   }
  assert (BetS D G E) by (conclude cn_equalitysub).
  assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
  assert (~ BetS G D C).
   {
   intro.
   assert (BetS E G C) by (conclude lemma_3_7b).
   assert (BetS C G E) by (conclude axiom_betweennesssymmetry).
   assert (TS C A B E) by (conclude_def TS ).
   contradict.
   }
  assert (~ BetS G C D).
   {
   intro.
   assert (BetS E G C) by (conclude axiom_innertransitivity).
   assert (BetS C G E) by (conclude axiom_betweennesssymmetry).
   assert (TS C A B E) by (conclude_def TS ).
   contradict.
   }
  assert (~ BetS C G D).
   {
   intro.
   assert (BetS D G Q) by (conclude cn_equalitysub).
   assert (BetS Q G C) by (conclude axiom_betweennesssymmetry).
   assert (BetS D G C) by (conclude axiom_betweennesssymmetry).
   assert (neq G D) by (forward_using lemma_betweennotequal).
   assert (~ BetS G D C).
    {
    intro.
    assert (BetS C D G) by (conclude axiom_betweennesssymmetry).
    assert (BetS C G C) by (conclude lemma_3_7a).
    assert (neq C C) by (forward_using lemma_betweennotequal).
    assert (eq C C) by (conclude cn_equalityreflexive).
    contradict.
    }
   assert (~ BetS G C D).
    {
    intro.
    assert (BetS D G C) by (conclude axiom_betweennesssymmetry).
    assert (BetS C G C) by (conclude axiom_innertransitivity).
    assert (neq C C) by (forward_using lemma_betweennotequal).
    assert (eq C C) by (conclude cn_equalityreflexive).
    contradict.
    }
   assert (BetS Q G D) by (conclude axiom_betweennesssymmetry).
   assert (BetS Q G C) by (conclude axiom_betweennesssymmetry).
   assert (eq C D) by (conclude lemma_outerconnectivity).
   assert (TS C A B E) by (conclude cn_equalitysub).
   contradict.
   }
  assert (Col Q C D) by (forward_using lemma_collinearorder).
  assert (Col Q G C) by (conclude_def Col ).
  assert (Col Q C G) by (forward_using lemma_collinearorder).
  assert (neq Q C) by (forward_using lemma_betweennotequal).
  assert (Col C D G) by (conclude lemma_collinear4).
  assert (Col G C D) by (forward_using lemma_collinearorder).
  assert ((eq G C \/ eq G D \/ eq C D \/ BetS C G D \/ BetS G C D \/ BetS G D C)) by (conclude_def Col ).
  assert (TS C A B E).
  by cases on (eq G C \/ eq G D \/ eq C D \/ BetS C G D \/ BetS G C D \/ BetS G D C).
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    assert (Col A B C) by (conclude cn_equalitysub).
    contradict.
    }
   close.
   }
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    assert (Col A B D) by (conclude cn_equalitysub).
    contradict.
    }
   close.
   }
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    assert (TS C A B E) by (conclude cn_equalitysub).
    contradict.
    }
   close.
   }
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ ~ TS C A B E).
    {
    intro.
    contradict.
    }
   close.
   }
(** cases *)
  contradict.
  }
 close.
 }
{
 assert (~ ~ TS C A B E).
  {
  intro.
  assert (~ Col Q C D).
   {
   intro.
   assert (Col C Q D) by (forward_using lemma_collinearorder).
   contradict.
   }
  let Tf:=fresh in
  assert (Tf:exists F, (BetS C F H /\ BetS D F G)) by (conclude postulate_Pasch_inner);destruct Tf as [F];spliter.
  assert (BetS H F C) by (conclude axiom_betweennesssymmetry).
  assert (BetS G F D) by (conclude axiom_betweennesssymmetry).
  assert (~ Col E D G).
   {
   intro.
   assert (~ neq W G).
    {
    intro.
    assert (Col D E G) by (forward_using lemma_collinearorder).
    assert (Col D W E) by (conclude_def Col ).
    assert (Col B G W) by (conclude lemma_collinear4).
    assert (Col W B G) by (forward_using lemma_collinearorder).
    assert (Col W B A) by (forward_using lemma_collinearorder).
    assert (Col B G A).
    by cases on (eq W B \/ neq W B).
    {
     assert (Col B A G) by (forward_using lemma_collinearorder).
     assert (Col B A W) by (forward_using lemma_collinearorder).
     assert (Col A G W) by (conclude lemma_collinear4).
     assert (Col A G B) by (conclude cn_equalitysub).
     assert (Col B G A) by (forward_using lemma_collinearorder).
     close.
     }
    {
     assert (Col B G A) by (conclude lemma_collinear4).
     close.
     }
(** cases *)
    assert (Col G A B) by (forward_using lemma_collinearorder).
    assert (Col E D G) by (forward_using lemma_collinearorder).
    assert (Col E D W) by (forward_using lemma_collinearorder).
    assert (neq D E) by (forward_using lemma_betweennotequal).
    assert (neq E D) by (conclude lemma_inequalitysymmetric).
    assert (Col D G W) by (conclude lemma_collinear4).
    assert (Col G W D) by (forward_using lemma_collinearorder).
    assert (eq B B) by (conclude cn_equalityreflexive).
    assert (Col A B B) by (conclude_def Col ).
    assert (neq G W) by (conclude lemma_inequalitysymmetric).
    assert (Col G W B) by (conclude lemma_collinear5).
    assert (Col W D B) by (conclude lemma_collinear4).
    assert (Col W B D) by (forward_using lemma_collinearorder).
    assert (Col B A W) by (forward_using lemma_collinearorder).
    assert (Col B A G) by (forward_using lemma_collinearorder).
    assert (eq A A) by (conclude cn_equalityreflexive).
    assert (Col B A A) by (conclude_def Col ).
    assert (Col G W A) by (conclude lemma_collinear5).
    assert (Col W D A) by (conclude lemma_collinear4).
    assert (neq D W) by (forward_using lemma_betweennotequal).
    assert (neq W D) by (conclude lemma_inequalitysymmetric).
    assert (Col D B A) by (conclude lemma_collinear4).
    assert (Col A B D) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (BetS D G E) by (conclude cn_equalitysub).
   assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
   assert (BetS G F D) by (conclude axiom_betweennesssymmetry).
   assert (BetS E G F) by (conclude axiom_innertransitivity).
   assert (~ Col H C E).
    {
    intro.
    assert (Col H E C) by (forward_using lemma_collinearorder).
    assert (Col E H C) by (forward_using lemma_collinearorder).
    assert (Col C F H) by (conclude_def Col ).
    assert (Col H C F) by (forward_using lemma_collinearorder).
    assert (Col H C E) by (forward_using lemma_collinearorder).
    assert (neq C H) by (forward_using lemma_betweennotequal).
    assert (neq H C) by (conclude lemma_inequalitysymmetric).
    assert (Col C F E) by (conclude lemma_collinear4).
    assert (Col E F C) by (forward_using lemma_collinearorder).
    assert (BetS D F E) by (conclude lemma_3_6b).
    assert (Col D F E) by (conclude_def Col ).
    assert (Col E F D) by (forward_using lemma_collinearorder).
    assert (neq F E) by (forward_using lemma_betweennotequal).
    assert (neq E F) by (conclude lemma_inequalitysymmetric).
    assert (Col F C D) by (conclude lemma_collinear4).
    assert (Col F D C) by (forward_using lemma_collinearorder).
    assert (Col D F G) by (conclude_def Col ).
    assert (Col F D G) by (forward_using lemma_collinearorder).
    assert (neq D F) by (forward_using lemma_betweennotequal).
    assert (neq F D) by (conclude lemma_inequalitysymmetric).
    assert (Col D C G) by (conclude lemma_collinear4).
    assert (Col G C D) by (forward_using lemma_collinearorder).
    assert (Col C G Q) by (conclude_def Col ).
    assert (Col G C Q) by (forward_using lemma_collinearorder).
    assert (neq C G) by (forward_using lemma_betweennotequal).
    assert (neq G C) by (conclude lemma_inequalitysymmetric).
    assert (Col C D Q) by (conclude lemma_collinear4).
    assert (Col Q C D) by (forward_using lemma_collinearorder).
    contradict.
    }
   let Tf:=fresh in
   assert (Tf:exists M, (BetS E M C /\ BetS H G M)) by (conclude postulate_Pasch_outer);destruct Tf as [M];spliter.
   assert (Col H G M) by (conclude_def Col ).
   assert (Col B H G) by (conclude lemma_collinear4).
   assert (Col H G B) by (forward_using lemma_collinearorder).
   assert (neq H G) by (forward_using lemma_betweennotequal).
   assert (Col G M B) by (conclude lemma_collinear4).
   assert (Col G B M) by (forward_using lemma_collinearorder).
   assert (Col G B A) by (forward_using lemma_collinearorder).
   assert (Col A B M).
   by cases on (eq B G \/ neq B G).
   {
    assert (Col B A H) by (forward_using lemma_collinearorder).
    assert (Col B A G) by (forward_using lemma_collinearorder).
    assert (Col A H G) by (conclude lemma_collinear4).
    assert (Col H G A) by (forward_using lemma_collinearorder).
    assert (Col G A M) by (conclude lemma_collinear4).
    assert (Col B A M) by (conclude cn_equalitysub).
    assert (Col A B M) by (forward_using lemma_collinearorder).
    close.
    }
   {
    assert (neq G B) by (conclude lemma_inequalitysymmetric).
    assert (Col B M A) by (conclude lemma_collinear4).
    assert (Col A B M) by (forward_using lemma_collinearorder).
    close.
    }
(** cases *)
   assert (BetS C M E) by (conclude axiom_betweennesssymmetry).
   assert (TS C A B E) by (conclude_def TS ).
   contradict.
   }
  assert (TS F A B E) by (conclude lemma_9_5b).
  assert (~ eq G H).
   {
   intro.
   assert (Col D H Q) by (conclude_def Col ).
   assert (Col C G Q) by (conclude_def Col ).
   assert (Col Q H D) by (forward_using lemma_collinearorder).
   assert (Col Q G C) by (forward_using lemma_collinearorder).
   assert (Col Q H C) by (conclude cn_equalitysub).
   assert (neq H Q) by (forward_using lemma_betweennotequal).
   assert (neq Q H) by (conclude lemma_inequalitysymmetric).
   assert (Col H D C) by (conclude lemma_collinear4).
   assert (Col H D Q) by (forward_using lemma_collinearorder).
   assert (neq D H) by (forward_using lemma_betweennotequal).
   assert (neq H D) by (conclude lemma_inequalitysymmetric).
   assert (Col D C Q) by (conclude lemma_collinear4).
   assert (Col C Q D) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (~ Col H C E).
   {
   intro.
   let Tf:=fresh in
   assert (Tf:exists K, (BetS G K H /\ Cong K G K H)) by (conclude proposition_10);destruct Tf as [K];spliter.
   assert (~ Col G D E).
    {
    intro.
    assert (Col E D G) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (BetS E W D) by (conclude axiom_betweennesssymmetry).
   assert (BetS G F D) by (conclude axiom_betweennesssymmetry).
   let Tf:=fresh in
   assert (Tf:exists J, (BetS E J F /\ BetS G J W)) by (conclude postulate_Pasch_inner);destruct Tf as [J];spliter.
   assert (Col G J W) by (conclude_def Col ).
   assert (Col E F J) by (conclude_def Col ).
   assert (Col E C H) by (forward_using lemma_collinearorder).
   assert (Col F E J) by (forward_using lemma_collinearorder).
   assert (Col C F H) by (conclude_def Col ).
   assert (Col C H F) by (forward_using lemma_collinearorder).
   assert (Col C H E) by (forward_using lemma_collinearorder).
   assert (neq C H) by (forward_using lemma_betweennotequal).
   assert (Col H F E) by (conclude lemma_collinear4).
   assert (Col F E H) by (forward_using lemma_collinearorder).
   assert (neq E F) by (forward_using lemma_betweennotequal).
   assert (neq F E) by (conclude lemma_inequalitysymmetric).
   assert (Col E J H) by (conclude lemma_collinear4).
   assert (Col E H J) by (forward_using lemma_collinearorder).
   assert (Col G W J) by (forward_using lemma_collinearorder).
   assert (eq H H) by (conclude cn_equalityreflexive).
   assert (Col E H H) by (conclude_def Col ).
   assert (Col G H W) by (conclude lemma_collinear5).
   assert (Col G W H) by (forward_using lemma_collinearorder).
   assert (~ eq G W).
    {
    intro.
    assert (Col D W E) by (conclude_def Col ).
    assert (Col D G E) by (conclude cn_equalitysub).
    assert (Col E D G) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (Col E J H) by (conclude lemma_collinear4).
   assert (Col W J H) by (conclude lemma_collinear4).
   assert (Col J H E) by (forward_using lemma_collinearorder).
   assert (Col J H W) by (forward_using lemma_collinearorder).
   assert (~ eq H W).
    {
    intro.
    assert (Col D W E) by (conclude_def Col ).
    assert (Col D H E) by (conclude cn_equalitysub).
    assert (Col D H Q) by (conclude_def Col ).
    assert (neq D H) by (forward_using lemma_betweennotequal).
    assert (Col H E Q) by (conclude lemma_collinear4).
    assert (Col H E C) by (forward_using lemma_collinearorder).
    assert (neq W E) by (forward_using lemma_betweennotequal).
    assert (neq H E) by (conclude cn_equalitysub).
    assert (Col E Q C) by (conclude lemma_collinear4).
    assert (Col E C Q) by (forward_using lemma_collinearorder).
    assert (Col E C H) by (forward_using lemma_collinearorder).
    assert (~ neq E C).
     {
     intro.
     assert (Col C Q H) by (conclude lemma_collinear4).
     assert (Col H Q C) by (forward_using lemma_collinearorder).
     assert (Col H Q D) by (forward_using lemma_collinearorder).
     assert (neq H Q) by (forward_using lemma_betweennotequal).
     assert (Col Q C D) by (conclude lemma_collinear4).
     contradict.
     }
    assert (Col E W D) by (forward_using lemma_collinearorder).
    assert (Col C W D) by (conclude cn_equalitysub).
    assert (Col C H D) by (conclude cn_equalitysub).
    assert (Col D H C) by (forward_using lemma_collinearorder).
    assert (Col D H Q) by (conclude_def Col ).
    assert (neq D H) by (forward_using lemma_betweennotequal).
    assert (Col H C Q) by (conclude lemma_collinear4).
    assert (Col H Q C) by (forward_using lemma_collinearorder).
    assert (Col H Q D) by (forward_using lemma_collinearorder).
    assert (neq H Q) by (forward_using lemma_betweennotequal).
    assert (Col Q C D) by (conclude lemma_collinear4).
    assert (Col C Q D) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (~ neq J H).
    {
    intro.
    assert (Col H E W) by (conclude lemma_collinear4).
    assert (Col H W E) by (forward_using lemma_collinearorder).
    assert (Col H W G) by (forward_using lemma_collinearorder).
    assert (Col W E G) by (conclude lemma_collinear4).
    assert (Col D W E) by (conclude_def Col ).
    assert (Col W E D) by (forward_using lemma_collinearorder).
    assert (neq W E) by (forward_using lemma_betweennotequal).
    assert (Col E G D) by (conclude lemma_collinear4).
    assert (Col E D G) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (BetS E H F) by (conclude cn_equalitysub).
   assert (BetS F H E) by (conclude axiom_betweennesssymmetry).
   assert (BetS C H E) by (conclude lemma_3_7a).
   assert (TS C A B E) by (conclude_def TS ).
   contradict.
   }
  assert (TS C A B E) by (conclude lemma_9_5a).
  contradict.
  }
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


