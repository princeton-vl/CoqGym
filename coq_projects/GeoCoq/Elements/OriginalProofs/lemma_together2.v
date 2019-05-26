Require Export GeoCoq.Elements.OriginalProofs.lemma_tworays.
Require Export GeoCoq.Elements.OriginalProofs.lemma_together.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthanadditive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthantransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_rayimpliescollinear.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_together2 : 
   forall A B C F G M N a b c, 
   TG A a C c B b -> Cong F G B b -> Out F G M -> Cong F M A a -> Out G F N -> Cong G N C c ->
   Out M F N.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS A a J /\ Cong a J C c /\ Lt B b A J)) by (conclude_def TG );destruct Tf as [J];spliter.
assert (neq a J) by (forward_using lemma_betweennotequal).
assert (neq C c) by (conclude axiom_nocollapse).
assert (~ eq M N).
 {
 intro.
 assert (Out F G N) by (conclude cn_equalitysub).
 assert (Out G F M) by (conclude cn_equalitysub).
 assert (BetS F M G) by (conclude lemma_tworays).
 assert (Cong G M C c) by (conclude cn_equalitysub).
 assert (Cong M G C c) by (forward_using lemma_congruenceflip).
 assert (Lt F G F G) by (conclude lemma_together).
 assert (~ Lt F G F G) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (neq F M) by (conclude lemma_raystrict).
assert (neq M F) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists D, (BetS M F D /\ Cong F D M F)) by (conclude lemma_extension);destruct Tf as [D];spliter.
assert ((BetS F M G \/ eq G M \/ BetS F G M)) by (conclude lemma_ray1).
assert (BetS G F D).
by cases on (BetS F M G \/ eq G M \/ BetS F G M).
{
 assert (BetS G M F) by (conclude axiom_betweennesssymmetry).
 assert (BetS G F D) by (conclude lemma_3_7a).
 close.
 }
{
 assert (BetS G F D) by (conclude cn_equalitysub).
 close.
 }
{
 assert (BetS M G F) by (conclude axiom_betweennesssymmetry).
 assert (BetS G F D) by (conclude lemma_3_6a).
 close.
 }
(** cases *)
assert (BetS D F M) by (conclude axiom_betweennesssymmetry).
assert (BetS D F G) by (conclude axiom_betweennesssymmetry).
assert (~ BetS F M N).
 {
 intro.
 assert (neq F M) by (forward_using lemma_betweennotequal).
 let Tf:=fresh in
 assert (Tf:exists P, (BetS F M P /\ Cong M P C c)) by (conclude lemma_extension);destruct Tf as [P];spliter.
 assert (Lt F G F P) by (conclude lemma_together).
 assert (Cong C c G N) by (conclude lemma_congruencesymmetric).
 assert (Cong C c N G) by (forward_using lemma_congruenceflip).
 assert (Cong M P N G) by (conclude lemma_congruencetransitive).
 assert (Cong F M F M) by (conclude cn_congruencereflexive).
 assert (Lt F M F N) by (conclude_def Lt ).
 assert (~ BetS F N G).
  {
  intro.
  assert (Lt F P F G) by (conclude lemma_lessthanadditive).
  assert (Lt F G F G) by (conclude lemma_lessthantransitive).
  assert (~ Lt F G F G) by (conclude lemma_trichotomy2).
  contradict.
  }
 assert (~ BetS G N F).
  {
  intro.
  assert (BetS F N G) by (conclude axiom_betweennesssymmetry).
  contradict.
  }
 assert ((BetS G N F \/ eq F N \/ BetS G F N)) by (conclude lemma_ray1).
 assert (neq F N) by (forward_using lemma_betweennotequal).
 assert (~ ~ BetS G F N).
  {
  intro.
  contradict.
  }
 assert (BetS N F G) by (conclude axiom_betweennesssymmetry).
 assert (~ ~ BetS N F M).
  {
  intro.
  assert (~ BetS F M G).
   {
   intro.
   assert (BetS N F M) by (conclude axiom_innertransitivity).
   contradict.
   }
  assert (~ BetS F G M).
   {
   intro.
   assert (BetS N F M) by (conclude lemma_3_7b).
   contradict.
   }
  assert (eq G M) by (conclude lemma_outerconnectivity).
  assert (BetS N F M) by (conclude cn_equalitysub).
  contradict.
  }
 assert (BetS N F N) by (conclude lemma_3_7b).
 assert (~ BetS N F N) by (conclude axiom_betweennessidentity).
 contradict.
 }
assert (Col G F N) by (conclude lemma_rayimpliescollinear).
assert (Col F G M) by (conclude lemma_rayimpliescollinear).
assert (Col G F M) by (forward_using lemma_collinearorder).
assert (neq F G) by (forward_using lemma_betweennotequal).
assert (neq G F) by (conclude lemma_inequalitysymmetric).
assert (Col F N M) by (conclude lemma_collinear4).
assert (Col M F N) by (forward_using lemma_collinearorder).
assert ((eq M F \/ eq M N \/ eq F N \/ BetS F M N \/ BetS M F N \/ BetS M N F)) by (conclude_def Col ).
assert (Out M F N).
by cases on (eq M F \/ eq M N \/ eq F N \/ BetS F M N \/ BetS M F N \/ BetS M N F).
{
 assert (~ ~ Out M F N).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out M F N).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (eq N F) by (conclude lemma_equalitysymmetric).
 assert (Out M F N) by (conclude lemma_ray4).
 close.
 }
{
 assert (~ ~ Out M F N).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (Out M F N) by (conclude lemma_ray4).
 close.
 }
{
 assert (Out M F N) by (conclude lemma_ray4).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


