Require Export GeoCoq.Elements.OriginalProofs.proposition_35A.
Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelPasch.

Section Euclid.

Context `{Ax:area}.

Lemma proposition_35 : 
   forall A B C D E F, 
   PG A B C D -> PG E B C F -> Col A D E -> Col A D F ->
   EF A B C D E B C F.
Proof.
intros.
assert ((Par A B C D /\ Par A D B C)) by (conclude_def PG ).
assert ((Par E B C F /\ Par E F B C)) by (conclude_def PG ).
assert (Par A B D C) by (forward_using lemma_parallelflip).
assert (Par E B F C) by (forward_using lemma_parallelflip).
assert (Par F C E B) by (conclude lemma_parallelsymmetric).
assert (Cong A D B C) by (forward_using proposition_34).
assert (Cong E F B C) by (forward_using proposition_34).
assert (Cong B C E F) by (conclude lemma_congruencesymmetric).
assert (Cong A D E F) by (conclude lemma_congruencetransitive).
assert (neq A D) by (conclude_def Par ).
assert (neq E F) by (conclude_def Par ).
assert (neq D A) by (conclude lemma_inequalitysymmetric).
assert (~ ~ EF A B C D E B C F).
 {
 intro.
 assert (~ BetS A D F).
  {
  intro.
  assert (Col A D F) by (conclude_def Col ).
  assert (Col D A F) by (forward_using lemma_collinearorder).
  assert (Col D A E) by (forward_using lemma_collinearorder).
  assert (Col A F E) by (conclude lemma_collinear4).
  assert (Col A E F) by (forward_using lemma_collinearorder).
  assert (EF A B C D E B C F) by (conclude proposition_35A).
  contradict.
  }
 assert (~ BetS A D E).
  {
  intro.
  rename_H H;
  let Tf:=fresh in
  assert (Tf:exists H, (BetS B H E /\ BetS C H D)) by (conclude lemma_parallelPasch);destruct Tf as [H];spliter.
  assert (BetS D H C) by (conclude axiom_betweennesssymmetry).
  assert (Col B H E) by (conclude_def Col ).
  assert (Col B E H) by (forward_using lemma_collinearorder).
  assert (nCol A D B) by (forward_using lemma_parallelNC).
  assert (Col A D E) by (conclude_def Col ).
  assert (eq D D) by (conclude cn_equalityreflexive).
  assert (Col A D D) by (conclude_def Col ).
  assert (neq D E) by (forward_using lemma_betweennotequal).
  assert (nCol D E B) by (conclude lemma_NChelper).
  assert (nCol B E D) by (forward_using lemma_NCorder).
  assert (TS D B E C) by (conclude_def TS ).
  assert (TS C B E D) by (conclude lemma_oppositesidesymmetric).
  assert (Par F C B E) by (forward_using lemma_parallelflip).
  assert (Par B E F C) by (conclude lemma_parallelsymmetric).
  assert (TP B E F C) by (conclude lemma_paralleldef2B).
  assert (OS F C B E) by (conclude_def TP ).
  assert (TS F B E D) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists e, (BetS F e D /\ Col B E e /\ nCol B E F)) by (conclude_def TS );destruct Tf as [e];spliter.
  assert (neq F D) by (forward_using lemma_betweennotequal).
  assert (Col F e D) by (conclude_def Col ).
  assert (~ neq e E).
   {
   intro.
   assert (neq A D) by (forward_using lemma_betweennotequal).
   assert (Col D E F) by (conclude lemma_collinear4).
   assert (Col F D E) by (forward_using lemma_collinearorder).
   assert (Col F D e) by (forward_using lemma_collinearorder).
   assert (Col D E e) by (conclude lemma_collinear4).
   assert (Col e E D) by (forward_using lemma_collinearorder).
   assert (Col e E B) by (forward_using lemma_collinearorder).
   assert (Col E D B) by (conclude lemma_collinear4).
   assert (Col B E D) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS F E D) by (conclude cn_equalitysub).
  assert (BetS D E F) by (conclude axiom_betweennesssymmetry).
  assert (BetS A D F) by (conclude lemma_3_7b).
  contradict.
  }
 assert (Par B A D C) by (forward_using lemma_parallelflip).
 assert (Par D C B A) by (conclude lemma_parallelsymmetric).
 assert (Par D A C B) by (forward_using lemma_parallelflip).
 assert (PG D C B A) by (conclude_def PG ).
 assert (Par B E F C) by (forward_using lemma_parallelflip).
 assert (Par F C B E) by (conclude lemma_parallelsymmetric).
 assert (Par F E C B) by (forward_using lemma_parallelflip).
 assert (PG F C B E) by (conclude_def PG ).
 assert (~ BetS E A D).
  {
  intro.
  assert (BetS D A E) by (conclude axiom_betweennesssymmetry).
  assert (Col D A E) by (conclude_def Col ).
  assert (Col A D E) by (forward_using lemma_collinearorder).
  assert (neq A D) by (forward_using lemma_betweennotequal).
  assert (Col D E F) by (conclude lemma_collinear4).
  assert (Col D F E) by (forward_using lemma_collinearorder).
  assert (EF D C B A F C B E) by (conclude proposition_35A).
  assert (EF D C B A E B C F) by (forward_using axiom_EFpermutation).
  assert (EF E B C F D C B A) by (conclude axiom_EFsymmetric).
  assert (EF E B C F A B C D) by (forward_using axiom_EFpermutation).
  assert (EF A B C D E B C F) by (conclude axiom_EFsymmetric).
  contradict.
  }
 assert (~ BetS D A F).
  {
  intro.
  rename_H H;
  let Tf:=fresh in
  assert (Tf:exists H, (BetS C H F /\ BetS B H A)) by (conclude lemma_parallelPasch);destruct Tf as [H];spliter.
  assert (BetS A H B) by (conclude axiom_betweennesssymmetry).
  assert (Col C H F) by (conclude_def Col ).
  assert (Col C F H) by (forward_using lemma_collinearorder).
  assert (nCol D A C) by (forward_using lemma_parallelNC).
  assert (Col D A F) by (conclude_def Col ).
  assert (eq A A) by (conclude cn_equalityreflexive).
  assert (Col D A A) by (conclude_def Col ).
  assert (neq A F) by (forward_using lemma_betweennotequal).
  assert (nCol A F C) by (conclude lemma_NChelper).
  assert (nCol C F A) by (forward_using lemma_NCorder).
  assert (TS A C F B) by (conclude_def TS ).
  assert (TS B C F A) by (conclude lemma_oppositesidesymmetric).
  assert (Par E B C F) by (forward_using lemma_parallelflip).
  assert (Par C F E B) by (conclude lemma_parallelsymmetric).
  assert (TP C F E B) by (conclude lemma_paralleldef2B).
  assert (OS E B C F) by (conclude_def TP ).
  assert (TS E C F A) by (conclude lemma_planeseparation).
  let Tf:=fresh in
  assert (Tf:exists e, (BetS E e A /\ Col C F e /\ nCol C F E)) by (conclude_def TS );destruct Tf as [e];spliter.
  assert (neq E A) by (forward_using lemma_betweennotequal).
  assert (~ neq e F).
   {
   intro.
   assert (Col D A E) by (forward_using lemma_collinearorder).
   assert (neq D A) by (forward_using lemma_betweennotequal).
   assert (Col A F E) by (conclude lemma_collinear4).
   assert (Col E A F) by (forward_using lemma_collinearorder).
   assert (Col E e A) by (conclude_def Col ).
   assert (Col E A e) by (forward_using lemma_collinearorder).
   assert (Col A F e) by (conclude lemma_collinear4).
   assert (Col e F A) by (forward_using lemma_collinearorder).
   assert (Col e F C) by (forward_using lemma_collinearorder).
   assert (Col F A C) by (conclude lemma_collinear4).
   assert (Col C F A) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (BetS E F A) by (conclude cn_equalitysub).
  assert (BetS A F E) by (conclude axiom_betweennesssymmetry).
  assert (BetS D A E) by (conclude lemma_3_7b).
  assert (BetS E A D) by (conclude axiom_betweennesssymmetry).
  contradict.
  }
 assert ((eq A D \/ eq A F \/ eq D F \/ BetS D A F \/ BetS A D F \/ BetS A F D)) by (conclude_def Col ).
 assert ((eq A D \/ eq A E \/ eq D E \/ BetS D A E \/ BetS A D E \/ BetS A E D)) by (conclude_def Col ).
 assert (~ eq A F).
  {
  intro.
  assert ((eq F D \/ eq F E \/ eq D E \/ BetS D A E \/ BetS A D E \/ BetS A E D)) by (conclude cn_equalitysub).
  assert (neq A F).
  by cases on (eq F D \/ eq F E \/ eq D E \/ BetS D A E \/ BetS A D E \/ BetS A E D).
  {
   assert (eq A D) by (conclude cn_equalitysub).
   assert (~ eq A F).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ eq A F).
    {
    intro.
    assert (neq F E) by (conclude lemma_inequalitysymmetric).
    contradict.
    }
   close.
   }
  {
   assert (~ eq A F).
    {
    intro.
    let Tf:=fresh in
    assert (Tf:exists p, (BetS E p C /\ BetS B p F)) by (conclude lemma_diagonalsmeet);destruct Tf as [p];spliter.
    assert (Col E p C) by (conclude_def Col ).
    assert (Col B p F) by (conclude_def Col ).
    assert (Col F B p) by (forward_using lemma_collinearorder).
    assert (Col E C p) by (forward_using lemma_collinearorder).
    assert (nCol E F C) by (forward_using lemma_parallelNC).
    assert (neq E C) by (forward_using lemma_NCdistinct).
    assert (nCol E F B) by (forward_using lemma_parallelNC).
    assert (neq F B) by (forward_using lemma_NCdistinct).
    assert (Meet E C F B) by (conclude_def Meet ).
    assert (Meet D C F B) by (conclude cn_equalitysub).
    assert (Meet D C A B) by (conclude cn_equalitysub).
    assert (Par D C A B) by (conclude lemma_parallelsymmetric).
    assert (~ Meet D C A B) by (conclude_def Par ).
    contradict.
    }
   close.
   }
  {
   assert (~ eq A F).
    {
    intro.
    assert (BetS E A D) by (conclude axiom_betweennesssymmetry).
    contradict.
    }
   close.
   }
  {
   assert (~ eq A F).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ eq A F).
    {
    intro.
    assert (Cong A E A E) by (conclude cn_congruencereflexive).
    assert (Cong F E A E) by (conclude cn_equalitysub).
    assert (Cong A E F E) by (conclude lemma_congruencesymmetric).
    assert (Lt F E A D) by (conclude_def Lt ).
    assert (Lt F E E F) by (conclude lemma_lessthancongruence).
    assert (Cong E F F E) by (conclude cn_equalityreverse).
    assert (Lt F E F E) by (conclude lemma_lessthancongruence).
    assert (~ Lt F E F E) by (conclude lemma_trichotomy2).
    contradict.
    }
   close.
   }
(** cases *)
  contradict.
  }
 assert (~ eq D F).
  {
  intro.
  assert ((eq A F \/ eq A E \/ eq F E \/ BetS D A E \/ BetS A D E \/ BetS A E D)) by (conclude cn_equalitysub).
  assert (neq D F).
  by cases on (eq A F \/ eq A E \/ eq F E \/ BetS D A E \/ BetS A D E \/ BetS A E D).
  {
   assert (~ eq D F).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ eq D F).
    {
    intro.
    let Tf:=fresh in
    assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude lemma_diagonalsmeet);destruct Tf as [M];spliter.
    assert (~ Col A B C).
     {
     intro.
     assert (eq C C) by (conclude cn_equalityreflexive).
     assert (Col C D C) by (conclude_def Col ).
     assert (neq A B) by (conclude_def Par ).
     assert (neq C D) by (conclude_def Par ).
     assert (Meet A B C D) by (conclude_def Meet ).
     assert (~ Meet A B C D) by (conclude_def Par ).
     contradict.
     }
    assert (EF A B C D A B C D) by (conclude lemma_EFreflexive).
    assert (EF A B C D E B C D) by (conclude cn_equalitysub).
    assert (EF A B C D E B C F) by (conclude cn_equalitysub).
    contradict.
    }
   close.
   }
  {
   assert (~ eq D F).
    {
    intro.
    assert (eq F E) by (conclude cn_equalitysub).
    assert (eq E F) by (conclude lemma_equalitysymmetric).
    contradict.
    }
   close.
   }
  {
   assert (~ eq D F).
    {
    intro.
    assert (BetS E A D) by (conclude axiom_betweennesssymmetry).
    contradict.
    }
   close.
   }
  {
   assert (~ eq D F).
    {
    intro.
    contradict.
    }
   close.
   }
  {
   assert (~ eq D F).
    {
    intro.
    assert (BetS D E A) by (conclude axiom_betweennesssymmetry).
    assert (Cong D E D E) by (conclude cn_congruencereflexive).
    assert (Lt D E D A) by (conclude_def Lt ).
    assert (Cong D E F E) by (conclude cn_equalitysub).
    assert (Lt F E D A) by (conclude lemma_lessthancongruence2).
    assert (Cong F E E F) by (conclude cn_equalityreverse).
    assert (Lt E F D A) by (conclude lemma_lessthancongruence2).
    assert (Cong D A A D) by (conclude cn_equalityreverse).
    assert (Lt E F A D) by (conclude lemma_lessthancongruence).
    assert (Lt E F E F) by (conclude lemma_lessthancongruence).
    assert (~ Lt E F E F) by (conclude lemma_trichotomy2).
    contradict.
    }
   close.
   }
(** cases *)
  contradict.
  }
 assert (BetS A F D).
 by cases on (eq A D \/ eq A F \/ eq D F \/ BetS D A F \/ BetS A D F \/ BetS A F D).
 {
  assert (~ ~ BetS A F D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A F D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A F D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A F D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A F D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  close.
  }
(** cases *)
 assert (BetS A E D).
 by cases on (eq A D \/ eq A E \/ eq D E \/ BetS D A E \/ BetS A D E \/ BetS A E D).
 {
  assert (~ ~ BetS A E D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A E D).
   {
   intro.
   assert (Cong A F A F) by (conclude cn_congruencereflexive).
   assert (Cong A F E F) by (conclude cn_equalitysub).
   assert (Lt E F A D) by (conclude_def Lt ).
   assert (Lt E F E F) by (conclude lemma_lessthancongruence).
   assert (~ Lt E F E F) by (conclude lemma_trichotomy2).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A E D).
   {
   intro.
   assert (BetS D F A) by (conclude axiom_betweennesssymmetry).
   assert (Cong D F D F) by (conclude cn_congruencereflexive).
   assert (Lt D F D A) by (conclude_def Lt ).
   assert (Lt E F D A) by (conclude cn_equalitysub).
   assert (Cong D A E F) by (forward_using lemma_congruenceflip).
   assert (Lt E F E F) by (conclude lemma_lessthancongruence).
   assert (~ Lt E F E F) by (conclude lemma_trichotomy2).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A E D).
   {
   intro.
   assert (BetS E A D) by (conclude axiom_betweennesssymmetry).
   contradict.
   }
  close.
  }
 {
  assert (~ ~ BetS A E D).
   {
   intro.
   contradict.
   }
  close.
  }
 {
  close.
  }
(** cases *)
 assert (~ BetS A E F).
  {
  intro.
  assert (BetS E F D) by (conclude lemma_3_6a).
  assert (Cong E F E F) by (conclude cn_congruencereflexive).
  assert (Lt E F E D) by (conclude_def Lt ).
  assert (BetS D E A) by (conclude axiom_betweennesssymmetry).
  assert (Cong D E D E) by (conclude cn_congruencereflexive).
  assert (Lt D E D A) by (conclude_def Lt ).
  assert (Cong E D D E) by (conclude cn_equalityreverse).
  assert (Lt E F D E) by (conclude lemma_lessthancongruence).
  assert (Lt E F D A) by (conclude lemma_lessthantransitive).
  assert (Cong D A A D) by (conclude cn_equalityreverse).
  assert (Lt E F A D) by (conclude lemma_lessthancongruence).
  assert (Lt E F E F) by (conclude lemma_lessthancongruence).
  assert (~ Lt E F E F) by (conclude lemma_trichotomy2).
  contradict.
  }
 assert (~ BetS A F E).
  {
  intro.
  assert (BetS F E D) by (conclude lemma_3_6a).
  assert (Cong F E F E) by (conclude cn_congruencereflexive).
  assert (Lt F E F D) by (conclude_def Lt ).
  assert (BetS D F A) by (conclude axiom_betweennesssymmetry).
  assert (Cong D F D F) by (conclude cn_congruencereflexive).
  assert (Lt D F D A) by (conclude_def Lt ).
  assert (Cong F D D F) by (conclude cn_equalityreverse).
  assert (Lt F E D F) by (conclude lemma_lessthancongruence).
  assert (Lt F E D A) by (conclude lemma_lessthantransitive).
  assert (Cong D A A D) by (conclude cn_equalityreverse).
  assert (Lt F E A D) by (conclude lemma_lessthancongruence).
  assert (Cong A D F E) by (forward_using lemma_congruenceflip).
  assert (Lt F E F E) by (conclude lemma_lessthancongruence).
  assert (~ Lt F E F E) by (conclude lemma_trichotomy2).
  contradict.
  }
 assert (eq E F) by (conclude axiom_connectivity).
 contradict.
 }
close.
Qed.

End Euclid.


