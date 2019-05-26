Require Export GeoCoq.Elements.OriginalProofs.proposition_12.
Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.
Require Export GeoCoq.Elements.OriginalProofs.lemma_droppedperpendicularunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_fiveline.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_07 : 
   forall A B C D, 
   neq A B -> Cong C A D A -> Cong C B D B -> OS C D A B ->
   eq C D.
Proof.
intros.
assert (nCol A B C) by (conclude_def OS ).
let Tf:=fresh in
assert (Tf:exists F, Perp_at C F A B F) by (conclude proposition_12);destruct Tf as [F];spliter.
rename_H H;
let Tf:=fresh in
assert (Tf:exists H, (Col C F F /\ Col A B F /\ Col A B H /\ Per H F C)) by (conclude_def Perp_at );destruct Tf as [H];spliter.
assert (~ eq C F).
 {
 intro.
 assert (Col A B C) by (conclude cn_equalitysub).
 contradict.
 }
assert (neq F C) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists E, (BetS C F E /\ Cong F E F C)) by (conclude lemma_extension);destruct Tf as [E];spliter.
assert (Cong A C A E).
by cases on (eq A F \/ neq A F).
{
 assert (Cong A E A C) by (conclude cn_equalitysub).
 assert (Cong A C A E) by (conclude lemma_congruencesymmetric).
 close.
 }
{
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Col B A F) by (forward_using lemma_collinearorder).
 assert (Col B A H) by (forward_using lemma_collinearorder).
 assert (Col A F H) by (conclude lemma_collinear4).
 assert (Col H F A) by (forward_using lemma_collinearorder).
 assert (Per A F C) by (conclude lemma_collinearright).
 assert (Per C F A) by (conclude lemma_8_2).
 let Tf:=fresh in
 assert (Tf:exists P, (BetS C F P /\ Cong C F P F /\ Cong C A P A /\ neq F A)) by (conclude_def Per );destruct Tf as [P];spliter.
 assert (Cong F E C F) by (forward_using lemma_congruenceflip).
 assert (Cong F E P F) by (conclude lemma_congruencetransitive).
 assert (Cong F E F P) by (forward_using lemma_congruenceflip).
 assert (eq E P) by (conclude lemma_extensionunique).
 assert (Cong C A E A) by (conclude cn_equalitysub).
 assert (Cong A C A E) by (forward_using lemma_congruenceflip).
 close.
 }
(** cases *)
assert (Cong B C B E).
by cases on (eq B F \/ neq B F).
{
 assert (Cong B E B C) by (conclude cn_equalitysub).
 assert (Cong B C B E) by (conclude lemma_congruencesymmetric).
 close.
 }
{
 assert (Col B A F) by (forward_using lemma_collinearorder).
 assert (Col B A H) by (forward_using lemma_collinearorder).
 assert (Col A B F) by (forward_using lemma_collinearorder).
 assert (Col A B H) by (forward_using lemma_collinearorder).
 assert (Col B F H) by (conclude lemma_collinear4).
 assert (Col H F B) by (forward_using lemma_collinearorder).
 assert (Per B F C) by (conclude lemma_collinearright).
 assert (Per C F B) by (conclude lemma_8_2).
 let Tf:=fresh in
 assert (Tf:exists P, (BetS C F P /\ Cong C F P F /\ Cong C B P B /\ neq F B)) by (conclude_def Per );destruct Tf as [P];spliter.
 assert (Cong F E C F) by (forward_using lemma_congruenceflip).
 assert (Cong F E P F) by (conclude lemma_congruencetransitive).
 assert (Cong F E F P) by (forward_using lemma_congruenceflip).
 assert (eq E P) by (conclude lemma_extensionunique).
 assert (Cong C B E B) by (conclude cn_equalitysub).
 assert (Cong B C B E) by (forward_using lemma_congruenceflip).
 close.
 }
(** cases *)
assert (TS C A B E) by (conclude_def TS ).
assert (OS D C A B) by (forward_using lemma_samesidesymmetric).
assert (TS D A B E) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists G, (BetS D G E /\ Col A B G /\ nCol A B D)) by (conclude_def TS );destruct Tf as [G];spliter.
assert (Cong E A C A) by (forward_using lemma_doublereverse).
assert (Cong A E C A) by (forward_using lemma_congruenceflip).
assert (Cong A E D A) by (conclude lemma_congruencetransitive).
assert (Cong A E A D) by (forward_using lemma_congruenceflip).
assert (Cong A D A E) by (conclude lemma_congruencesymmetric).
assert (Cong B D B C) by (forward_using lemma_doublereverse).
assert (Cong B D B E) by (conclude lemma_congruencetransitive).
assert (Cong A G A G) by (conclude cn_congruencereflexive).
assert (Cong G B G B) by (conclude cn_congruencereflexive).
assert ((eq A B \/ eq A G \/ eq B G \/ BetS B A G \/ BetS A B G \/ BetS A G B)) by (conclude_def Col ).
assert (Cong G D G E).
by cases on (eq A B \/ eq A G \/ eq B G \/ BetS B A G \/ BetS A B G \/ BetS A G B).
{
 assert (~ ~ Cong G D G E).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (Cong A D A E) by (conclude lemma_congruencesymmetric).
 assert (Cong G D G E) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong G D G E) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong B A B A) by (conclude cn_congruencereflexive).
 assert (Cong A G A G) by (conclude cn_congruencereflexive).
 assert (Cong A D A E) by (conclude lemma_congruencesymmetric).
 assert (Cong D G E G)
  by (auto using (axiom_5_line B A G D B A G E)). 
 assert (Cong G D G E) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (Cong A B A B) by (conclude cn_congruencereflexive).
 assert (Cong B G B G) by (conclude cn_congruencereflexive).
 assert (Cong D G E G) by (auto using (axiom_5_line A B G D A B G E)).
 assert (Cong G D G E) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (Cong A G A G) by (conclude cn_congruencereflexive).
 assert (Cong G B G B) by (conclude cn_congruencereflexive).
 assert (Cong G D G E) by (conclude lemma_interior5).
 close.
 }
(** cases *)
assert (Cong D A E A) by (forward_using lemma_congruenceflip).
assert (eq F G).
by cases on (eq A G \/ neq A G).
{
 assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
 assert (Cong E G D G) by (forward_using lemma_doublereverse).
 assert (Cong E B D B) by (forward_using lemma_doublereverse).
 assert (~ eq G B).
  {
  intro.
  assert (eq A B) by (conclude cn_equalitysub).
  contradict.
  }
 assert (Per E G B) by (conclude_def Per ).
 assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
 assert (Cong E F C F) by (forward_using lemma_doublereverse).
 assert (Cong E B C B) by (forward_using lemma_doublereverse).
 assert (~ eq F B).
  {
  intro.
  assert (Cong A E A D) by (forward_using lemma_congruenceflip).
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (BetS E A D) by (conclude cn_equalitysub).
  assert (Cong E A D A) by (forward_using lemma_congruenceflip).
  assert (Per E A B) by (conclude_def Per ).
  assert (Per B A E) by (conclude lemma_8_2).
  assert (BetS E B C) by (conclude cn_equalitysub).
  assert (Per E B A) by (conclude_def Per ).
  let Tf:=fresh in
  assert (Tf:exists J, (BetS B A J /\ Cong A J A B)) by (conclude lemma_extension);destruct Tf as [J];spliter.
  assert (Out B A J) by (conclude lemma_ray4).
  assert (Per E B J) by (conclude lemma_8_3).
  assert (Per J B E) by (conclude lemma_8_2).
  assert (Col A B J) by (conclude_def Col ).
  assert (Col B A J) by (forward_using lemma_collinearorder).
  assert (Per B A E) by (conclude lemma_8_2).
  assert (neq A J) by (forward_using lemma_betweennotequal).
  assert (neq J A) by (conclude lemma_inequalitysymmetric).
  assert (Per J A E) by (conclude lemma_collinearright).
  assert (Col J A B) by (forward_using lemma_collinearorder).
  assert (eq A B) by (conclude lemma_droppedperpendicularunique).
  contradict.
  }
 assert (Per E F B) by (conclude_def Per ).
 assert (Per B G E) by (conclude lemma_8_2).
 assert (Per B F E) by (conclude lemma_8_2).
 assert (Col B G F) by (conclude lemma_collinear4).
 assert (eq G F) by (conclude lemma_droppedperpendicularunique).
 assert (eq F G) by (conclude lemma_equalitysymmetric).
 close.
 }
{
 assert (eq F G).
 by cases on (eq A F \/ neq A F).
 {
  assert (neq F B) by (conclude cn_equalitysub).
  assert (Cong E F C F) by (forward_using lemma_congruenceflip).
  assert (Cong E B C B) by (forward_using lemma_doublereverse).
  assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
  assert (Per E F B) by (conclude_def Per ).
  assert (Per B F E) by (conclude lemma_8_2).
  assert (~ eq B G).
   {
   intro.
   assert (eq F A) by (conclude lemma_equalitysymmetric).
   assert (Cong A E A C) by (forward_using lemma_congruenceflip).
   assert (Cong A C A D) by (forward_using lemma_congruenceflip).
   assert (Cong A E A D) by (conclude lemma_congruencetransitive).
   assert (Cong B E B D) by (conclude lemma_congruencesymmetric).
   assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
   assert (BetS E B D) by (conclude cn_equalitysub).
   assert (Cong E B D B) by (forward_using lemma_congruenceflip).
   assert (Cong E A D A) by (conclude lemma_congruencesymmetric).
   assert (neq B A) by (conclude lemma_inequalitysymmetric).
   assert (Per E B A) by (conclude_def Per ).
   assert (Per A B E) by (conclude lemma_8_2).
   assert (BetS E A C) by (conclude cn_equalitysub).
   assert (Per E A B) by (conclude_def Per ).
   assert (Per B A E) by (conclude lemma_8_2).
   let Tf:=fresh in
   assert (Tf:exists K, (BetS A B K /\ Cong B K B A)) by (conclude lemma_extension);destruct Tf as [K];spliter.
   assert (Out A B K) by (conclude lemma_ray4).
   assert (Per E A K) by (conclude lemma_8_3).
   assert (Per K A E) by (conclude lemma_8_2).
   assert (Col B A K) by (conclude_def Col ).
   assert (Col A B K) by (forward_using lemma_collinearorder).
   assert (Per A B E) by (conclude lemma_8_2).
   assert (neq B K) by (forward_using lemma_betweennotequal).
   assert (neq K B) by (conclude lemma_inequalitysymmetric).
   assert (Per K B E) by (conclude lemma_collinearright).
   assert (Col A B K) by (conclude_def Col ).
   assert (Col K B A) by (forward_using lemma_collinearorder).
   assert (eq B A) by (conclude lemma_droppedperpendicularunique).
   assert (neq B A) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  assert (neq G B) by (conclude lemma_inequalitysymmetric).
  assert (Cong E G D G) by (forward_using lemma_doublereverse).
  assert (Cong E B D B) by (forward_using lemma_doublereverse).
  assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
  assert (Per E G B) by (conclude_def Per ).
  assert (Per B G E) by (conclude lemma_8_2).
  assert (Col F B G) by (conclude cn_equalitysub).
  assert (Col B G F) by (forward_using lemma_collinearorder).
  assert (eq G F) by (conclude lemma_droppedperpendicularunique).
  assert (eq F G) by (conclude lemma_equalitysymmetric).
  close.
  }
 {
  assert (neq F A) by (conclude lemma_inequalitysymmetric).
  assert (Cong E F C F) by (forward_using lemma_doublereverse).
  assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
  assert (Per E F A) by (conclude_def Per ).
  assert (Per A F E) by (conclude lemma_8_2).
  assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
  assert (Cong E G D G) by (forward_using lemma_doublereverse).
  assert (Cong E A D A) by (conclude lemma_congruencesymmetric).
  assert (neq G A) by (conclude lemma_inequalitysymmetric).
  assert (Per E G A) by (conclude_def Per ).
  assert (Per A G E) by (conclude lemma_8_2).
  assert (Col B A F) by (forward_using lemma_collinearorder).
  assert (Col B A G) by (forward_using lemma_collinearorder).
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (Col A F G) by (conclude lemma_collinear4).
  assert (eq F G) by (conclude lemma_droppedperpendicularunique).
  close.
  }
(** cases *)
 close.
 }
(** cases *)
assert (Cong A F A F) by (conclude cn_congruencereflexive).
assert (Cong B F B F) by (conclude cn_congruencereflexive).
assert (Cong A F A G) by (conclude cn_equalitysub).
assert (Cong B F B G) by (conclude cn_equalitysub).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Col A F B) by (forward_using lemma_collinearorder).
assert (Cong F B F B) by (conclude cn_congruencereflexive).
assert (Cong F B G B) by (conclude cn_equalitysub).
assert (Cong A C A D) by (forward_using lemma_congruenceflip).
assert (Cong B C B D) by (forward_using lemma_congruenceflip).
assert (Cong A B A B) by (conclude cn_congruencereflexive).
assert (Cong F C G D) by (conclude lemma_fiveline).
assert (Cong F C F D) by (conclude cn_equalitysub).
assert (BetS E F C) by (conclude axiom_betweennesssymmetry).
assert (BetS E G D) by (conclude axiom_betweennesssymmetry).
assert (BetS E F D) by (conclude cn_equalitysub).
assert (Out F D C) by (conclude_def Out ).
assert (eq D D) by (conclude cn_equalityreflexive).
assert (~ eq F D).
 {
 intro.
 assert (Col A B F) by (forward_using lemma_collinearorder).
 assert (Col A B D) by (conclude cn_equalitysub).
 contradict.
 }
assert (Out F D D) by (conclude lemma_ray4).
assert (eq C D) by (conclude lemma_layoffunique).
close.
Qed.

End Euclid.


