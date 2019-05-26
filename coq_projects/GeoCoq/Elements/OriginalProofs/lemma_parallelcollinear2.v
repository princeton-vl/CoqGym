Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelcollinear2 : 
   forall A B C c d, 
   TP A B c d -> BetS c C d ->
   TP A B C d.
Proof.
intros.
assert (BetS d C c) by (conclude axiom_betweennesssymmetry).
assert ((neq A B /\ neq c d /\ ~ Meet A B c d /\ OS c d A B)) by (conclude_def TP ).
let Tf:=fresh in
assert (Tf:exists p q r, (Col A B p /\ Col A B r /\ BetS c p q /\ BetS d r q /\ nCol A B c /\ nCol A B d)) by (conclude_def OS );destruct Tf as [p[q[r]]];spliter.
assert (neq C d) by (forward_using lemma_betweennotequal).
assert (BetS q p c) by (conclude axiom_betweennesssymmetry).
assert (BetS q r d) by (conclude axiom_betweennesssymmetry).
assert (BetS d C c) by (conclude axiom_betweennesssymmetry).
assert (BetS q p c) by (conclude axiom_betweennesssymmetry).
assert (Col q p c) by (conclude_def Col ).
assert (~ eq p r).
 {
 intro.
 assert (Col q r d) by (conclude_def Col ).
 assert (Col q p c) by (conclude_def Col ).
 assert (Col q p d) by (conclude cn_equalitysub).
 assert (neq q p) by (forward_using lemma_betweennotequal).
 assert (Col p c d) by (conclude lemma_collinear4).
 assert (Col c d p) by (forward_using lemma_collinearorder).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (nCol p r c) by (conclude lemma_NChelper).
assert (nCol p r d) by (conclude lemma_NChelper).
assert (nCol r d p) by (forward_using lemma_NCorder).
assert (Col q r d) by (conclude_def Col ).
assert (Col r d q) by (forward_using lemma_collinearorder).
assert (eq d d) by (conclude cn_equalityreflexive).
assert (Col r d d) by (conclude_def Col ).
assert (neq q d) by (forward_using lemma_betweennotequal).
assert (nCol q d p) by (conclude lemma_NChelper).
assert (nCol q p d) by (forward_using lemma_NCorder).
assert (Col q p c) by (conclude_def Col ).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (~ eq c p).
 {
 intro.
 assert (eq p c) by (conclude lemma_equalitysymmetric).
 assert (Col p r c) by (conclude_def Col ).
 contradict.
 }
assert (eq p p) by (conclude cn_equalityreflexive).
assert (Col q p p) by (conclude_def Col ).
assert (nCol c p d) by (conclude lemma_NChelper).
assert (Col c p q) by (forward_using lemma_collinearorder).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (Col c p c) by (conclude_def Col ).
assert (neq q c) by (forward_using lemma_betweennotequal).
assert (nCol q c d) by (conclude lemma_NChelper).
assert (BetS q p c) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists E, (BetS q E C /\ BetS d E p)) by (conclude postulate_Pasch_inner);destruct Tf as [E];spliter.
assert (BetS p E d) by (conclude axiom_betweennesssymmetry).
assert (BetS q r d) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists F, (BetS q F E /\ BetS p F r)) by (conclude postulate_Pasch_inner);destruct Tf as [F];spliter.
assert (Col p r F) by (conclude_def Col ).
assert (Col B r p) by (conclude lemma_collinear4).
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col B A r) by (forward_using lemma_collinearorder).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Col B p r) by (forward_using lemma_collinearorder).
assert (Col B p A) by (forward_using lemma_collinearorder).
assert (~ Col A B C).
 {
 intro.
 assert (Col c C d) by (conclude_def Col ).
 assert (Col c d C) by (forward_using lemma_collinearorder).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (BetS q F C) by (conclude lemma_3_6b).
assert (BetS C F q) by (conclude axiom_betweennesssymmetry).
assert (~ ~ OS C d A B).
 {
 intro.
 assert (~ neq B p).
  {
  intro.
  assert (Col p r A) by (conclude lemma_collinear4).
  assert (Col A p r) by (forward_using lemma_collinearorder).
  assert (Col A p B) by (forward_using lemma_collinearorder).
  assert (~ neq A p).
   {
   intro.
   assert (Col p r B) by (conclude lemma_collinear4).
   assert (Col A B F) by (conclude lemma_collinear5).
   assert (OS C d A B) by (conclude_def OS ).
   contradict.
   }
  assert (Col A r F) by (conclude cn_equalitysub).
  assert (Col r A F) by (forward_using lemma_collinearorder).
  assert (Col r A B) by (forward_using lemma_collinearorder).
  assert (~ eq r A).
   {
   intro.
   assert (eq r p) by (conclude cn_equalitysub).
   assert (neq p r) by (forward_using lemma_betweennotequal).
   assert (neq r p) by (conclude lemma_inequalitysymmetric).
   contradict.
   }
  assert (Col A F B) by (conclude lemma_collinear4).
  assert (Col A B F) by (forward_using lemma_collinearorder).
  assert (OS C d A B) by (conclude_def OS ).
  contradict.
  }
 assert (neq A p) by (conclude cn_equalitysub).
 assert (Col A p B) by (forward_using lemma_collinearorder).
 assert (eq A A) by (conclude cn_equalityreflexive).
 assert (Col B A A) by (conclude_def Col ).
 assert (Col B A p) by (forward_using lemma_collinearorder).
 assert (Col B A r) by (forward_using lemma_collinearorder).
 assert (Col A p r) by (conclude lemma_collinear5).
 assert (Col p B r) by (conclude lemma_collinear4).
 assert (Col p r B) by (forward_using lemma_collinearorder).
 assert (Col p r A) by (forward_using lemma_collinearorder).
 assert (Col A B F) by (conclude lemma_collinear5).
 assert (OS C d A B) by (conclude_def OS ).
 contradict.
 }
assert (~ Meet A B C d).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists R, (neq A B /\ neq C d /\ Col A B R /\ Col C d R)) by (conclude_def Meet );destruct Tf as [R];spliter.
 assert (Col c C d) by (conclude_def Col ).
 assert (Col C d c) by (forward_using lemma_collinearorder).
 assert (neq C d) by (forward_using lemma_betweennotequal).
 assert (Col d c R) by (conclude lemma_collinear4).
 assert (Col c d R) by (forward_using lemma_collinearorder).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (TP A B C d) by (conclude_def TP ).
close.
Qed.

End Euclid.


