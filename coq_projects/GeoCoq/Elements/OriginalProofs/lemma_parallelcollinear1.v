Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearbetween.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NChelper.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCorder.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_parallelcollinear1 : 
   forall A B C c d, 
   TP A B c d -> BetS C c d ->
   TP A B C d.
Proof.
intros.
assert (Col C c d) by (conclude_def Col ).
assert (neq C c) by (forward_using lemma_betweennotequal).
assert (neq c d) by (forward_using lemma_betweennotequal).
assert (neq C d) by (forward_using lemma_betweennotequal).
assert ((neq A B /\ neq c d /\ ~ Meet A B c d /\ OS c d A B)) by (conclude_def TP ).
let Tf:=fresh in
assert (Tf:exists p q r, (Col A B p /\ Col A B r /\ BetS c p q /\ BetS d r q /\ nCol A B c /\ nCol A B d)) by (conclude_def OS );destruct Tf as [p[q[r]]];spliter.
assert (BetS q r d) by (conclude axiom_betweennesssymmetry).
assert (Col C c d) by (conclude_def Col ).
assert (Col c d C) by (forward_using lemma_collinearorder).
assert (BetS d c C) by (conclude axiom_betweennesssymmetry).
assert (BetS q p c) by (conclude axiom_betweennesssymmetry).
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
assert (Col q p c) by (conclude_def Col ).
assert (~ Col q d C).
 {
 intro.
 assert (Col d c C) by (conclude_def Col ).
 assert (Col C d c) by (forward_using lemma_collinearorder).
 assert (Col C d q) by (forward_using lemma_collinearorder).
 assert (neq C d) by (forward_using lemma_betweennotequal).
 assert (Col d c q) by (conclude lemma_collinear4).
 assert (Col c q d) by (forward_using lemma_collinearorder).
 assert (Col c q p) by (forward_using lemma_collinearorder).
 assert (neq q c) by (forward_using lemma_betweennotequal).
 assert (neq c q) by (conclude lemma_inequalitysymmetric).
 assert (Col q d p) by (conclude lemma_collinear4).
 assert (Col q r d) by (conclude_def Col ).
 assert (Col q d r) by (forward_using lemma_collinearorder).
 assert (neq q d) by (forward_using lemma_betweennotequal).
 assert (Col d p r) by (conclude lemma_collinear4).
 assert (Col B p r) by (conclude lemma_collinear4).
 assert (Col B A p) by (forward_using lemma_collinearorder).
 assert (Col B p A) by (forward_using lemma_collinearorder).
 assert (Col B A r) by (forward_using lemma_collinearorder).
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Col A p r) by (conclude lemma_collinear4).
 assert (~ neq B p).
  {
  intro.
  assert (Col p r A) by (conclude lemma_collinear4).
  assert (Col p r d) by (forward_using lemma_collinearorder).
  assert (Col r A d) by (conclude lemma_collinear4).
  assert (Col r A B) by (forward_using lemma_collinearorder).
  assert (~ neq r A).
   {
   intro.
   assert (Col A d B) by (conclude lemma_collinear4).
   assert (Col A B d) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (Col p A d) by (conclude cn_equalitysub).
  assert (Col p A B) by (forward_using lemma_collinearorder).
  assert (~ neq p A).
   {
   intro.
   assert (Col A d B) by (conclude lemma_collinear4).
   assert (Col A B d) by (forward_using lemma_collinearorder).
   contradict.
   }
  assert (eq A p) by (conclude lemma_equalitysymmetric).
  assert (eq r p) by (conclude cn_equalitytransitive).
  assert (Col q p d) by (conclude cn_equalitysub).
  assert (neq q p) by (forward_using lemma_betweennotequal).
  assert (Col p c d) by (conclude lemma_collinear4).
  assert (Col c d p) by (forward_using lemma_collinearorder).
  assert (Meet A B c d) by (conclude_def Meet ).
  contradict.
  }
 assert (neq A p) by (conclude cn_equalitysub).
 assert (Col A p B) by (forward_using lemma_collinearorder).
 assert (~ eq r A).
  {
  intro.
  assert (Col d p A) by (conclude cn_equalitysub).
  assert (Col d B A) by (conclude cn_equalitysub).
  assert (Col A B d) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (Col r A B) by (forward_using lemma_collinearorder).
 assert (Col d B r) by (conclude cn_equalitysub).
 assert (Col r B d) by (forward_using lemma_collinearorder).
 assert (Col r B A) by (forward_using lemma_collinearorder).
 assert (~ neq r B).
  {
  intro.
  assert (Col B d A) by (conclude lemma_collinear4).
  assert (Col A B d) by (forward_using lemma_collinearorder).
  contradict.
  }
 assert (eq B r) by (conclude lemma_equalitysymmetric).
 assert (eq p B) by (conclude lemma_equalitysymmetric).
 assert (eq p r) by (conclude cn_equalitytransitive).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists E, (BetS q E c /\ BetS C E r)) by (conclude postulate_Pasch_inner);destruct Tf as [E];spliter.
assert (BetS r E C) by (conclude axiom_betweennesssymmetry).
assert (Col q E c) by (conclude_def Col ).
assert (Col q c p) by (forward_using lemma_collinearorder).
assert (Col q c E) by (forward_using lemma_collinearorder).
assert (neq q c) by (forward_using lemma_betweennotequal).
assert (Col c p E) by (conclude lemma_collinear4).
assert (Col c E p) by (forward_using lemma_collinearorder).
assert (neq r p) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists J, (BetS r p J /\ Cong p J r p)) by (conclude lemma_extension);destruct Tf as [J];spliter.
assert (BetS J p r) by (conclude axiom_betweennesssymmetry).
assert (Col J p r) by (conclude_def Col ).
assert (neq J r) by (forward_using lemma_betweennotequal).
assert (neq p r) by (forward_using lemma_betweennotequal).
assert (neq J p) by (forward_using lemma_betweennotequal).
assert (Col B p r) by (conclude lemma_collinear4).
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col B A r) by (forward_using lemma_collinearorder).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Col A p r) by (conclude lemma_collinear4).
assert (Col p r A) by (forward_using lemma_collinearorder).
assert (Col p r B) by (forward_using lemma_collinearorder).
assert (~ Meet C d J r).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists K, (neq C d /\ neq J r /\ Col C d K /\ Col J r K)) by (conclude_def Meet );destruct Tf as [K];spliter.
 assert (Col C c d) by (conclude_def Col ).
 assert (Col C d c) by (forward_using lemma_collinearorder).
 assert (neq c d) by (forward_using lemma_betweennotequal).
 assert (neq d c) by (conclude lemma_inequalitysymmetric).
 assert (Col d c K) by (conclude lemma_collinear4).
 assert (Col c d K) by (forward_using lemma_collinearorder).
 assert (Col r p J) by (conclude_def Col ).
 assert (Col r J p) by (forward_using lemma_collinearorder).
 assert (neq r J) by (forward_using lemma_betweennotequal).
 assert (Col r J K) by (forward_using lemma_collinearorder).
 assert (Col J p K) by (conclude lemma_collinear4).
 assert (Col J p r) by (forward_using lemma_collinearorder).
 assert (neq p J) by (forward_using lemma_betweennotequal).
 assert (neq J p) by (conclude lemma_inequalitysymmetric).
 assert (Col p K r) by (conclude lemma_collinear4).
 assert (Col p r K) by (forward_using lemma_collinearorder).
 assert (Col A B K) by (conclude lemma_collinear5).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (BetS c E p) by (conclude lemma_collinearbetween).
assert (BetS p E c) by (conclude axiom_betweennesssymmetry).
assert (BetS q p E) by (conclude axiom_innertransitivity).
assert (nCol p r c) by (conclude lemma_NChelper).
assert (nCol p c r) by (forward_using lemma_NCorder).
assert (Col q p c) by (conclude_def Col ).
assert (Col p c q) by (forward_using lemma_collinearorder).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (Col p c c) by (conclude_def Col ).
assert (neq q c) by (forward_using lemma_betweennotequal).
assert (nCol q c r) by (conclude lemma_NChelper).
assert (nCol q r c) by (forward_using lemma_NCorder).
assert (neq q d) by (forward_using lemma_betweennotequal).
assert (Col q r d) by (conclude_def Col ).
assert (eq q q) by (conclude cn_equalityreflexive).
assert (Col q r q) by (conclude_def Col ).
assert (nCol q d c) by (conclude lemma_NChelper).
assert (nCol d c q) by (forward_using lemma_NCorder).
assert (Col C c d) by (conclude_def Col ).
assert (Col d c C) by (forward_using lemma_collinearorder).
assert (eq d d) by (conclude cn_equalityreflexive).
assert (Col d c d) by (conclude_def Col ).
assert (neq C d) by (forward_using lemma_betweennotequal).
assert (neq d C) by (conclude lemma_inequalitysymmetric).
assert (nCol d C q) by (conclude lemma_NChelper).
assert (nCol d q C) by (forward_using lemma_NCorder).
assert (Col q r d) by (conclude_def Col ).
assert (Col d q r) by (forward_using lemma_collinearorder).
assert (Col d q q) by (conclude_def Col ).
assert (~ eq r C).
 {
 intro.
 assert (Col A B C) by (conclude cn_equalitysub).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (~ eq r q).
 {
 intro.
 assert (Col r q c) by (conclude_def Col ).
 assert (Col q r c) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (nCol r q C) by (conclude lemma_NChelper).
assert (nCol r C q) by (forward_using lemma_NCorder).
assert (BetS r E C) by (conclude axiom_betweennesssymmetry).
let Tf:=fresh in
assert (Tf:exists F, (BetS q F C /\ BetS r p F)) by (conclude postulate_Pasch_outer);destruct Tf as [F];spliter.
assert (BetS C F q) by (conclude axiom_betweennesssymmetry).
assert (Col r p F) by (conclude_def Col ).
assert (Col r p A) by (forward_using lemma_collinearorder).
assert (Col r p B) by (forward_using lemma_collinearorder).
assert (Col A B F) by (conclude lemma_collinear5).
assert (eq r r) by (conclude cn_equalityreflexive).
assert (Col d q r) by (conclude_def Col ).
assert (neq q r) by (forward_using lemma_betweennotequal).
assert (nCol q r C) by (conclude lemma_NChelper).
assert (nCol q C r) by (forward_using lemma_NCorder).
assert (Col q F C) by (conclude_def Col ).
assert (Col q C F) by (forward_using lemma_collinearorder).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col q C C) by (conclude_def Col ).
assert (neq F C) by (forward_using lemma_betweennotequal).
assert (nCol F C r) by (conclude lemma_NChelper).
assert (nCol F r C) by (forward_using lemma_NCorder).
assert (Col B r p) by (conclude lemma_collinear4).
assert (Col B p r) by (forward_using lemma_collinearorder).
assert (Col B p A) by (forward_using lemma_collinearorder).
assert (Col B A r) by (forward_using lemma_collinearorder).
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col A r p) by (conclude lemma_collinear4).
assert (Col p r A) by (forward_using lemma_collinearorder).
assert (Col p r F) by (forward_using lemma_collinearorder).
assert (neq p r) by (forward_using lemma_betweennotequal).
assert (Col r A F) by (conclude lemma_collinear4).
assert (Col F r A) by (forward_using lemma_collinearorder).
assert (Col B A r) by (forward_using lemma_collinearorder).
assert (Col B A p) by (forward_using lemma_collinearorder).
assert (Col A r p) by (conclude lemma_collinear4).
assert (Col A p r) by (forward_using lemma_collinearorder).
assert (Col A p B) by (forward_using lemma_collinearorder).
assert (Col A B r) by (forward_using lemma_collinearorder).
assert (Col A B p) by (forward_using lemma_collinearorder).
assert (Col B r p) by (conclude lemma_collinear4).
assert (Col p r B) by (forward_using lemma_collinearorder).
assert (Col r B F) by (conclude lemma_collinear4).
assert (Col F r B) by (forward_using lemma_collinearorder).
assert (nCol A B C) by (conclude lemma_NChelper).
assert (TS C A B q) by (conclude_def TS ).
assert (OS C d A B) by (conclude_def OS ).
assert (~ Meet A B C d).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists K, (neq A B /\ neq C d /\ Col A B K /\ Col C d K)) by (conclude_def Meet );destruct Tf as [K];spliter.
 assert (Col C c d) by (conclude_def Col ).
 assert (Col C d c) by (forward_using lemma_collinearorder).
 assert (neq C d) by (forward_using lemma_betweennotequal).
 assert (Col d c K) by (conclude lemma_collinear4).
 assert (Col c d K) by (forward_using lemma_collinearorder).
 assert (Meet A B c d) by (conclude_def Meet ).
 contradict.
 }
assert (neq C d) by (forward_using lemma_betweennotequal).
assert (TP A B C d) by (conclude_def TP ).
close.
Qed.

End Euclid.


