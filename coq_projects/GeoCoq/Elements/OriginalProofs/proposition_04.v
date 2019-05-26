Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglesNC.
Require Export GeoCoq.Elements.OriginalProofs.lemma_layoffunique.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray5.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray3.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_04 : 
   forall A B C a b c, 
   Cong A B a b -> Cong A C a c -> CongA B A C b a c ->
   Cong B C b c /\ CongA A B C a b c /\ CongA A C B a c b.
Proof.
intros.
assert (nCol b a c) by (conclude lemma_equalanglesNC).
let Tf:=fresh in
assert (Tf:exists U V u v, (Out A B U /\ Out A C V /\ Out a b u /\ Out a c v /\ Cong A U a u /\ Cong A V a v /\ Cong U V u v /\ nCol B A C)) by (conclude_def CongA );destruct Tf as [U[V[u[v]]]];spliter.
assert (neq a b) by (conclude lemma_ray2).
assert (neq b a) by (conclude lemma_inequalitysymmetric).
assert (~ Col A B C).
 {
 intro.
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq A B).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (~ eq A C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq C A) by (conclude lemma_inequalitysymmetric).
assert (~ eq a c).
 {
 intro.
 assert (Col b a c) by (conclude_def Col ).
 contradict.
 }
assert (neq c a) by (conclude lemma_inequalitysymmetric).
assert (~ eq b c).
 {
 intro.
 assert (Col b a c) by (conclude_def Col ).
 contradict.
 }
assert (neq c b) by (conclude lemma_inequalitysymmetric).
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 assert (Col B A C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (neq C B) by (conclude lemma_inequalitysymmetric).
assert ((BetS A U B \/ eq B U \/ BetS A B U)) by (conclude lemma_ray1).
assert (Cong B V b v).
by cases on (BetS A U B \/ eq B U \/ BetS A B U).
{
 assert (Cong A U A U) by (conclude cn_congruencereflexive).
 assert (Lt A U A B) by (conclude_def Lt ).
 assert (Lt A U a b) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists w, (BetS a w b /\ Cong a w A U)) by (conclude_def Lt );destruct Tf as [w];spliter.
 assert (Cong a w a u) by (conclude lemma_congruencetransitive).
 assert (neq a b) by (forward_using lemma_betweennotequal).
 assert (Out a b w) by (conclude lemma_ray4).
 assert (Cong a w a u) by (conclude lemma_congruencetransitive).
 assert (eq w u) by (conclude lemma_layoffunique).
 assert (BetS a u b) by (conclude cn_equalitysub).
 assert (Cong U B u b) by (conclude lemma_differenceofparts).
 assert (Cong V B v b) by (eapply (axiom_5_line) with (B0:=U) (b0:=u) (A0:=A) (a0:=a);assumption) .
 assert (Cong B V b v) by (forward_using lemma_congruenceflip).
 close.
 }
{
 assert (Cong B V u v) by (conclude cn_equalitysub).
 assert (Cong a b A B) by (conclude lemma_congruencesymmetric).
 assert (Cong A B A B) by (conclude cn_congruencereflexive).
 assert (Cong A B A U) by (conclude cn_equalitysub).
 assert (Cong a b A U) by (conclude lemma_congruencetransitive).
 assert (Cong a b a u) by (conclude lemma_congruencetransitive).
 assert ((BetS a u b \/ eq b u \/ BetS a b u)) by (conclude lemma_ray1).
 assert (eq b u).
 by cases on (BetS a u b \/ eq b u \/ BetS a b u).
 {
  assert (~ neq b u).
   {
   intro.
   assert (~ Cong a u a b) by (conclude lemma_partnotequalwhole).
   assert (Cong a u a b) by (conclude lemma_congruencesymmetric).
   contradict.
   }
  close.
  }
 {
  close.
  }
 {
  assert (~ neq b u).
   {
   intro.
   assert (~ Cong a b a u) by (conclude lemma_partnotequalwhole).
   assert (Cong a b A B) by (conclude lemma_congruencesymmetric).
   assert (Cong A B A B) by (conclude cn_congruencereflexive).
   assert (Cong A B A U) by (conclude cn_equalitysub).
   assert (Cong A B a u) by (conclude lemma_congruencetransitive).
   assert (Cong a b a u) by (conclude lemma_congruencetransitive).
   contradict.
   }
  close.
  }
(** cases *)
 assert (Cong B V b v) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong A B A B) by (conclude cn_congruencereflexive).
 assert (Lt A B A U) by (conclude_def Lt ).
 assert (Lt A B a u) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists f, (BetS a f u /\ Cong a f A B)) by (conclude_def Lt );destruct Tf as [f];spliter.
 assert (neq a u) by (forward_using lemma_betweennotequal).
 assert (Out a u f) by (conclude lemma_ray4).
 assert (Out a u b) by (conclude lemma_ray5).
 assert (Out a b f) by (conclude lemma_ray3).
 assert (Cong a f a b) by (conclude lemma_congruencetransitive).
 assert (eq f b) by (conclude lemma_layoffunique).
 assert (BetS a b u) by (conclude cn_equalitysub).
 assert (Cong B U b u) by (conclude lemma_differenceofparts).
 assert (BetS a b u) by (conclude lemma_betweennesspreserved).
 assert (Cong B U b u) by (conclude lemma_differenceofparts).
 assert (Cong B V b v) by (conclude lemma_interior5).
 close.
 }
(** cases *)
assert ((BetS A V C \/ eq C V \/ BetS A C V)) by (conclude lemma_ray1).
assert (Cong B C b c).
by cases on (BetS A V C \/ eq C V \/ BetS A C V).
{
 assert (Cong A V A V) by (conclude cn_congruencereflexive).
 assert (Lt A V A C) by (conclude_def Lt ).
 assert (Lt A V a c) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists g, (BetS a g c /\ Cong a g A V)) by (conclude_def Lt );destruct Tf as [g];spliter.
 assert (neq a g) by (forward_using lemma_betweennotequal).
 assert (Out a g c) by (conclude lemma_ray4).
 assert (Out a c g) by (conclude lemma_ray5).
 assert (Cong a g a v) by (conclude lemma_congruencetransitive).
 assert (eq g v) by (conclude lemma_layoffunique).
 assert (BetS a v c) by (conclude cn_equalitysub).
 assert (Cong V C v c) by (conclude lemma_differenceofparts).
 assert (Cong V B v b) by (forward_using lemma_congruenceflip).
 
 assert (Cong B C b c) by (eauto using  (axiom_5_line _ _ _ _ _ _ _ _ H37 H H38)).
 close.
 }
{
 assert (Cong A C a v) by (conclude cn_equalitysub).
 assert (Cong a c A C) by (conclude lemma_congruencesymmetric).
 assert (Cong a c a v) by (conclude lemma_congruencetransitive).
 assert (neq a c) by (conclude lemma_ray2).
 assert (eq c c) by (conclude cn_equalityreflexive).
 assert (Out a c c) by (conclude lemma_ray4).
 assert (eq c v) by (conclude lemma_layoffunique).
 assert (Cong B C b v) by (conclude cn_equalitysub).
 assert (Cong B C b c) by (conclude cn_equalitysub).
 close.
 }
{
 assert (Cong A C A C) by (conclude cn_congruencereflexive).
 assert (Lt A C A V) by (conclude_def Lt ).
 assert (Lt A C a v) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists g, (BetS a g v /\ Cong a g A C)) by (conclude_def Lt );destruct Tf as [g];spliter.
 assert (neq a g) by (forward_using lemma_betweennotequal).
 assert (Out a g v) by (conclude lemma_ray4).
 assert (Out a v g) by (conclude lemma_ray5).
 assert (Cong a g a c) by (conclude lemma_congruencetransitive).
 assert (Cong a c a g) by (conclude lemma_congruencesymmetric).
 assert (Out a v c) by (conclude lemma_ray5).
 assert (eq c g) by (conclude lemma_layoffunique).
 assert (BetS a c v) by (conclude cn_equalitysub).
 assert (Cong C V c v) by (conclude lemma_differenceofparts).
 assert (Cong V B v b) by (forward_using lemma_congruenceflip).
 assert (Cong C B c b) by (conclude lemma_interior5).
 assert (Cong B C b c) by (forward_using lemma_congruenceflip).
 close.
 }
(** cases *)
assert (eq A A) by (conclude cn_equalityreflexive).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (eq a a) by (conclude cn_equalityreflexive).
assert (eq c c) by (conclude cn_equalityreflexive).
assert (eq B B) by (conclude cn_equalityreflexive).
assert (eq b b) by (conclude cn_equalityreflexive).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (Out B A A) by (conclude lemma_ray4).
assert (Out B C C) by (conclude lemma_ray4).
assert (Out b a a) by (conclude lemma_ray4).
assert (Out b c c) by (conclude lemma_ray4).
assert (Cong B A b a) by (forward_using lemma_congruenceflip).
assert (CongA A B C a b c) by (conclude_def CongA ).
assert (Out C A A) by (conclude lemma_ray4).
assert (Out C B B) by (conclude lemma_ray4).
assert (Out c a a) by (conclude lemma_ray4).
assert (Out c b b) by (conclude lemma_ray4).
assert (Cong C A c a) by (forward_using lemma_congruenceflip).
assert (Cong C B c b) by (forward_using lemma_congruenceflip).
assert (~ Col A C B).
 {
 intro.
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
assert (CongA A C B a c b) by (conclude_def CongA ).
close.
Qed.

End Euclid.


