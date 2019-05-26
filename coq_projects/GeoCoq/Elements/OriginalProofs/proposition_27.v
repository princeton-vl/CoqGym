Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesflip.
Require Export GeoCoq.Elements.OriginalProofs.proposition_16.
Require Export GeoCoq.Elements.OriginalProofs.lemma_angletrichotomy.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearbetween.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_27 : 
   forall A B C D E F, 
   BetS A E B -> BetS C F D -> CongA A E F E F D -> TS A E F D ->
   Par A B C D.
Proof.
intros.
assert (neq A B) by (forward_using lemma_betweennotequal).
assert (neq C D) by (forward_using lemma_betweennotequal).
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS A H D /\ Col E F H /\ nCol E F A)) by (conclude_def TS );destruct Tf as [H];spliter.
assert (Col A E B) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (Col C F D) by (conclude_def Col ).
assert (neq F D) by (forward_using lemma_betweennotequal).
assert (CongA E F D A E F) by (conclude lemma_equalanglessymmetric).
assert (nCol E F D) by (conclude_def CongA ).
assert (neq E F) by (forward_using lemma_angledistinct).
assert (neq F E) by (conclude lemma_inequalitysymmetric).
assert (~ Meet A B C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists G, (neq A B /\ neq C D /\ Col A B G /\ Col C D G)) by (conclude_def Meet );destruct Tf as [G];spliter.
 assert (Col B A G) by (forward_using lemma_collinearorder).
 assert (Col B A E) by (forward_using lemma_collinearorder).
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Col A G E) by (conclude lemma_collinear4).
 assert (Col A E G) by (forward_using lemma_collinearorder).
 assert (eq F F) by (conclude cn_equalityreflexive).
 assert (Out E F F) by (conclude lemma_ray4).
 assert (Supp A E F F B) by (conclude_def Supp ).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Out F E E) by (conclude lemma_ray4).
 assert (BetS D F C) by (conclude axiom_betweennesssymmetry).
 assert (Supp D F E E C) by (conclude_def Supp ).
 assert (CongA E F D D F E) by (conclude lemma_ABCequalsCBA).
 assert (CongA A E F D F E) by (conclude lemma_equalanglestransitive).
 assert (CongA F E B E F C) by (conclude lemma_supplements).
 assert (CongA B E F C F E) by (conclude lemma_equalanglesflip).
 assert (~ BetS A E G).
  {
  intro.
  assert (eq E E) by (conclude cn_equalityreflexive).
  assert (Col E F E) by (conclude_def Col ).
  assert (BetS G E A) by (conclude axiom_betweennesssymmetry).
  assert (Col C F D) by (conclude_def Col ).
  assert (Col C D F) by (forward_using lemma_collinearorder).
  assert (neq C D) by (forward_using lemma_betweennotequal).
  assert (Col D G F) by (conclude lemma_collinear4).
  assert (Col G F D) by (forward_using lemma_collinearorder).
  assert (~ eq F G).
   {
   intro.
   assert (Col A E F) by (conclude cn_equalitysub).
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (neq G F) by (conclude lemma_inequalitysymmetric).
  assert (~ Col E F G).
   {
   intro.
   assert (Col G F E) by (forward_using lemma_collinearorder).
   assert (Col F E D) by (conclude lemma_collinear4).
   assert (Col E F D) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS D H A) by (conclude axiom_betweennesssymmetry).
  assert (OS D G E F) by (unfold OS;exists A;exists H;exists E;splits;auto).
  assert (OS G D E F) by (forward_using lemma_samesidesymmetric).
  assert (eq F F) by (conclude cn_equalityreflexive).
  assert (Col E F F) by (conclude_def Col ).
  assert (BetS D F C) by (conclude axiom_betweennesssymmetry).
  assert (TS D E F C) by (conclude_def TS ).
  assert (TS G E F C) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists R, (BetS G R C /\ Col E F R /\ nCol E F G)) by (conclude_def TS );destruct Tf as [R];spliter.
  assert (~ neq F R).
   {
   intro.
   assert (Col G R C) by (conclude_def Col ).
   assert (Col C G D) by (forward_using lemma_collinearorder).
   assert (Col C G R) by (forward_using lemma_collinearorder).
   assert (neq G C) by (forward_using lemma_betweennotequal).
   assert (neq C G) by (conclude lemma_inequalitysymmetric).
   assert (Col G C R) by (forward_using lemma_collinearorder).
   assert (Col G C D) by (forward_using lemma_collinearorder).
   assert (neq G C) by (conclude lemma_inequalitysymmetric).
   assert (neq R F) by (conclude lemma_inequalitysymmetric).
   assert (Col C G R) by (forward_using lemma_collinearorder).
   assert (Col C D F) by (forward_using lemma_collinearorder).
   assert (Col D F G) by (conclude lemma_collinear4).
   assert (Col D F C) by (forward_using lemma_collinearorder).
   assert (neq F D) by (forward_using lemma_betweennotequal).
   assert (neq D F) by (conclude lemma_inequalitysymmetric).
   assert (Col F G C) by (conclude lemma_collinear4).
   assert (Col C G F) by (forward_using lemma_collinearorder).
   assert (Col C G D) by (forward_using lemma_collinearorder).
   assert (Col R F D) by (conclude lemma_collinear5).
   assert (Col R F E) by (forward_using lemma_collinearorder).
   assert (Col F D E) by (conclude lemma_collinear4).
   assert (Col E F D) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS G F C) by (conclude cn_equalitysub).
  assert (~ Col E G F).
   {
   intro.
   assert (Col E F G) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Triangle E G F) by (conclude_def Triangle ).
  assert (LtA G E F E F C) by (conclude proposition_16).
  assert (LtA G E F F E B) by (conclude lemma_angleorderrespectscongruence).
  assert (eq F F) by (conclude cn_equalityreflexive).
  assert (Out E F F) by (conclude lemma_ray4).
  assert (Out E G B) by (conclude_def Out ).
  assert (~ Col G E F).
   {
   intro.
   assert (Col E G F) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (CongA G E F G E F) by (conclude lemma_equalanglesreflexive).
  assert (CongA G E F B E F) by (conclude lemma_equalangleshelper).
  assert (nCol B E F) by (conclude_def CongA ).
  assert (CongA B E F F E B) by (conclude lemma_ABCequalsCBA).
  assert (CongA G E F F E B) by (conclude lemma_equalanglestransitive).
  assert (CongA F E B G E F) by (conclude lemma_equalanglessymmetric).
  assert (LtA F E B F E B) by (conclude lemma_angleorderrespectscongruence2).
  assert (~ LtA F E B F E B) by (conclude lemma_angletrichotomy).
  contradict.
  }
 assert (~ Out E A G).
  {
  intro.
  assert (eq F F) by (conclude cn_equalityreflexive).
  assert (Out E F F) by (conclude lemma_ray4).
  assert (Out E G A) by (conclude lemma_ray5).
  assert (CongA E F D A E F) by (conclude lemma_equalanglessymmetric).
  assert (CongA E F D G E F) by (conclude lemma_equalangleshelper).
  assert (BetS B E A) by (conclude axiom_betweennesssymmetry).
  assert ((BetS E A G \/ eq G A \/ BetS E G A)) by (conclude lemma_ray1).
  assert (BetS B E G).
  by cases on (BetS E A G \/ eq G A \/ BetS E G A).
  {
   assert (BetS B E G) by (conclude lemma_3_7b).
   close.
   }
  {
   assert (BetS B E G) by (conclude cn_equalitysub).
   close.
   }
  {
   assert (BetS B E G) by (conclude axiom_innertransitivity).
   close.
   }
(** cases *)
  assert (BetS G E B) by (conclude axiom_betweennesssymmetry).
  assert (eq E E) by (conclude cn_equalityreflexive).
  assert (Col E F E) by (conclude_def Col ).
  assert (~ Col E F G).
   {
   intro.
   assert (Col B A G) by (forward_using lemma_collinearorder).
   assert (Col A E B) by (conclude_def Col ).
   assert (Col B A E) by (forward_using lemma_collinearorder).
   assert (Col A G E) by (conclude lemma_collinear4).
   assert (Col G E A) by (forward_using lemma_collinearorder).
   assert (Col G E F) by (forward_using lemma_collinearorder).
   assert (neq E G) by (forward_using lemma_betweennotequal).
   assert (neq G E) by (conclude lemma_inequalitysymmetric).
   assert (Col E A F) by (conclude lemma_collinear4).
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (OS A G E F) by (conclude_def OS ).
  assert (OS G A E F) by (forward_using lemma_samesidesymmetric).
  assert (TS G E F D) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists P, (BetS G P D /\ Col E F P /\ nCol E F G)) by (conclude_def TS );destruct Tf as [P];spliter.
  assert (Col G P D) by (conclude_def Col ).
  assert (~ neq P F).
   {
   intro.
   assert (neq G D) by (forward_using lemma_betweennotequal).
   assert (Col G D P) by (forward_using lemma_collinearorder).
   assert (Col C F D) by (conclude_def Col ).
   assert (Col C D F) by (forward_using lemma_collinearorder).
   assert (Col D G F) by (conclude lemma_collinear4).
   assert (Col G D F) by (forward_using lemma_collinearorder).
   assert (Col D P F) by (conclude lemma_collinear4).
   assert (Col P F D) by (forward_using lemma_collinearorder).
   assert (Col P F E) by (forward_using lemma_collinearorder).
   assert (Col F D E) by (conclude lemma_collinear4).
   assert (~ Col F D E).
    {
    intro.
    assert (Col E F D) by (forward_using lemma_collinearorder).
    contradict.
    }
   contradict.
   }
  assert (BetS G F D) by (conclude cn_equalitysub).
  assert (~ Col F E A).
   {
   intro.
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (CongA F E A F E A) by (conclude lemma_equalanglesreflexive).
  assert (CongA F E A F E G) by (conclude lemma_equalangleshelper).
  assert (CongA F E G F E A) by (conclude lemma_equalanglessymmetric).
  assert (nCol F E G) by (conclude_def CongA ).
  assert (~ Col E G F).
   {
   intro.
   assert (Col F E G) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Triangle E G F) by (conclude_def Triangle ).
  assert (LtA G E F E F D) by (conclude proposition_16).
  assert (LtA E F D E F D) by (conclude lemma_angleorderrespectscongruence2).
  assert (~ LtA E F D E F D) by (conclude lemma_angletrichotomy).
  contradict.
  }
 assert ((eq A E \/ eq A G \/ eq E G \/ BetS E A G \/ BetS A E G \/ BetS A G E)) by (conclude_def Col ).
 assert (~ Meet A B C D).
 by cases on (eq A E \/ eq A G \/ eq E G \/ BetS E A G \/ BetS A E G \/ BetS A G E).
 {
  assert (~ Meet A B C D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ neq H F).
   {
   intro.
   assert (Col C D F) by (forward_using lemma_collinearorder).
   assert (Col D G F) by (conclude lemma_collinear4).
   assert (Col D A F) by (conclude cn_equalitysub).
   assert (Col A H D) by (conclude_def Col ).
   assert (Col D A H) by (forward_using lemma_collinearorder).
   assert (neq A D) by (forward_using lemma_betweennotequal).
   assert (neq D A) by (conclude lemma_inequalitysymmetric).
   assert (Col A F H) by (conclude lemma_collinear4).
   assert (Col H F A) by (forward_using lemma_collinearorder).
   assert (Col H F E) by (forward_using lemma_collinearorder).
   assert (Col F A E) by (conclude lemma_collinear4).
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS A F D) by (conclude cn_equalitysub).
  assert (~ Col E A F).
   {
   intro.
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Triangle E A F) by (conclude_def Triangle ).
  assert (LtA A E F E F D) by (conclude proposition_16).
  assert (CongA E F D A E F) by (conclude lemma_equalanglessymmetric).
  assert (LtA E F D E F D) by (conclude lemma_angleorderrespectscongruence2).
  assert (~ Meet A B C D).
   {
   intro.
   assert (~ LtA E F D E F D) by (conclude lemma_angletrichotomy).
   contradict.
   }
  close.
  }
 {
  assert (Col C D E) by (conclude cn_equalitysub).
  assert (Col C D F) by (forward_using lemma_collinearorder).
  assert (Col D E F) by (conclude lemma_collinear4).
  assert (Col E F D) by (forward_using lemma_collinearorder).
  assert (~ neq E F).
   {
   intro.
   assert (Col F D H) by (conclude lemma_collinear4).
   assert (Col D H F) by (forward_using lemma_collinearorder).
   assert (Col A H D) by (conclude_def Col ).
   assert (Col D H A) by (forward_using lemma_collinearorder).
   assert (neq H D) by (forward_using lemma_betweennotequal).
   assert (neq D H) by (conclude lemma_inequalitysymmetric).
   assert (Col H F A) by (conclude lemma_collinear4).
   assert (Col H F E) by (forward_using lemma_collinearorder).
   assert (~ neq H F).
    {
    intro.
    assert (Col F A E) by (conclude lemma_collinear4).
    assert (Col E F A) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (Col A H D) by (conclude_def Col ).
   assert (Col A F D) by (conclude cn_equalitysub).
   assert (Col D F A) by (forward_using lemma_collinearorder).
   assert (Col D F C) by (forward_using lemma_collinearorder).
   assert (neq H D) by (forward_using lemma_betweennotequal).
   assert (neq D H) by (conclude lemma_inequalitysymmetric).
   assert (neq D F) by (conclude cn_equalitysub).
   assert (Col F A C) by (conclude lemma_collinear4).
   assert (Col C F A) by (forward_using lemma_collinearorder).
   assert (Col D C G) by (forward_using lemma_collinearorder).
   assert (Col C D F) by (forward_using lemma_collinearorder).
   assert (Col D C F) by (forward_using lemma_collinearorder).
   assert (neq D C) by (conclude lemma_inequalitysymmetric).
   assert (Col C G F) by (conclude lemma_collinear4).
   assert (Col C F G) by (forward_using lemma_collinearorder).
   assert (~ neq C F).
    {
    intro.
    assert (Col F A G) by (conclude lemma_collinear4).
    assert (Col F A E) by (conclude cn_equalitysub).
    assert (Col E F A) by (forward_using lemma_collinearorder).
    contradict.
    }
   assert (Col A H D) by (conclude_def Col ).
   assert (Col A C D) by (conclude cn_equalitysub).
   assert (Col C D A) by (forward_using lemma_collinearorder).
   assert (Col F D A) by (conclude cn_equalitysub).
   assert (Col C D E) by (conclude cn_equalitysub).
   assert (Col F D E) by (conclude cn_equalitysub).
   assert (Col D F E) by (forward_using lemma_collinearorder).
   assert (Col D F A) by (forward_using lemma_collinearorder).
   assert (neq D F) by (conclude cn_equalitysub).
   assert (Col F E A) by (conclude lemma_collinear4).
   assert (Col E F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Col E F A) by (conclude_def Col ).
  assert (~ Meet A B C D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (neq E A) by (forward_using lemma_betweennotequal).
  assert (Out E A G) by (conclude lemma_ray4).
  assert (~ Meet A B C D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ Meet A B C D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (BetS E G A) by (conclude axiom_betweennesssymmetry).
  assert (neq E A) by (forward_using lemma_betweennotequal).
  assert (Out E A G) by (conclude lemma_ray4).
  assert (~ Meet A B C D).
   {
   intro.
   contradict.
   }
  close.
  }
(** cases *)
 contradict.
 }
assert (eq A A) by (conclude cn_equalityreflexive).
assert (Col A B A) by (conclude_def Col ).
assert (Col A B E) by (conclude_def Col ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (Col C D D) by (conclude_def Col ).
assert (Col C D F) by (conclude_def Col ).
assert (neq A E) by (forward_using lemma_betweennotequal).
assert (neq F D) by (forward_using lemma_betweennotequal).
assert (BetS E H F) by (conclude lemma_collinearbetween).
assert (BetS F H E) by (conclude axiom_betweennesssymmetry).
assert (Par A B C D) by (conclude_def Par ).
close.
Qed.

End Euclid.


