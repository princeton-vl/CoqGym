Require Export GeoCoq.Elements.OriginalProofs.lemma_parallelcollinear.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_paralleldef2B : 
   forall A B C D, 
   Par A B C D ->
   TP A B C D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d e, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a e d /\ BetS c e b)) by (conclude_def Par );destruct Tf as [a[b[c[d[e]]]]];spliter.
assert (neq b a) by (conclude lemma_inequalitysymmetric).
assert (neq e b) by (forward_using lemma_betweennotequal).
assert (~ Meet a b C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists R, (neq a b /\ neq C D /\ Col a b R /\ Col C D R)) by (conclude_def Meet );destruct Tf as [R];spliter.
 assert (Col b a R) by (forward_using lemma_collinearorder).
 assert (Col B a b) by (conclude lemma_collinear4).
 assert (Col b a B) by (forward_using lemma_collinearorder).
 assert (Col a B R) by (conclude lemma_collinear4).
 assert (Col a B A) by (forward_using lemma_collinearorder).
 assert (Col A B R).
 by cases on (neq a B \/ eq a B).
 {
  assert (Col B R A) by (conclude lemma_collinear4).
  assert (Col A B R) by (forward_using lemma_collinearorder).
  close.
  }
 {
  assert (neq A a) by (conclude cn_equalitysub).
  assert (Col B A a) by (forward_using lemma_collinearorder).
  assert (Col B A b) by (forward_using lemma_collinearorder).
  assert (neq B A) by (conclude lemma_inequalitysymmetric).
  assert (Col A a b) by (conclude lemma_collinear4).
  assert (Col b a A) by (forward_using lemma_collinearorder).
  assert (Col a A R) by (conclude lemma_collinear4).
  assert (Col a A B) by (forward_using lemma_collinearorder).
  assert (neq A a) by (conclude cn_equalitysub).
  assert (neq a A) by (conclude lemma_inequalitysymmetric).
  assert (Col A R B) by (conclude lemma_collinear4).
  assert (Col A B R) by (forward_using lemma_collinearorder).
  close.
  }
(** cases *)
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists P, (BetS e b P /\ Cong b P e b)) by (conclude lemma_extension);destruct Tf as [P];spliter.
assert (BetS P b e) by (conclude axiom_betweennesssymmetry).
assert (BetS b e c) by (conclude axiom_betweennesssymmetry).
assert (BetS P b c) by (conclude lemma_3_7b).
assert (BetS c b P) by (conclude axiom_betweennesssymmetry).
assert (~ Col a d P).
 {
 intro.
 assert (Col a e d) by (conclude_def Col ).
 assert (Col a d e) by (forward_using lemma_collinearorder).
 assert (neq a d) by (forward_using lemma_betweennotequal).
 assert (Col d P e) by (conclude lemma_collinear4).
 assert (Col e P d) by (forward_using lemma_collinearorder).
 assert (Col e b P) by (conclude_def Col ).
 assert (Col e P b) by (forward_using lemma_collinearorder).
 assert (neq e P) by (forward_using lemma_betweennotequal).
 assert (Col P d b) by (conclude lemma_collinear4).
 assert (Col d P b) by (forward_using lemma_collinearorder).
 assert (Col d P a) by (forward_using lemma_collinearorder).
 assert (~ eq d P).
  {
  intro.
  assert (Col c b P) by (conclude_def Col ).
  assert (Col c b d) by (conclude cn_equalitysub).
  assert (Col b e c) by (conclude_def Col ).
  assert (Col c b e) by (forward_using lemma_collinearorder).
  assert (neq c b) by (forward_using lemma_betweennotequal).
  assert (Col b d e) by (conclude lemma_collinear4).
  assert (Col a e d) by (conclude_def Col ).
  assert (Col d e a) by (forward_using lemma_collinearorder).
  assert (Col d e b) by (forward_using lemma_collinearorder).
  assert (neq e d) by (forward_using lemma_betweennotequal).
  assert (neq d e) by (conclude lemma_inequalitysymmetric).
  assert (Col e a b) by (conclude lemma_collinear4).
  assert (Col a e d) by (conclude_def Col ).
  assert (Col e a d) by (forward_using lemma_collinearorder).
  assert (neq a e) by (forward_using lemma_betweennotequal).
  assert (neq e a) by (conclude lemma_inequalitysymmetric).
  assert (Col a b d) by (conclude lemma_collinear4).
  assert (Meet a b C D) by (conclude_def Meet ).
  contradict.
  }
 assert (Col P b a) by (conclude lemma_collinear4).
 assert (Col P b c) by (conclude_def Col ).
 assert (neq b P) by (forward_using lemma_betweennotequal).
 assert (neq P b) by (conclude lemma_inequalitysymmetric).
 assert (Col b a c) by (conclude lemma_collinear4).
 assert (Col B a b) by (conclude lemma_collinear4).
 assert (Col b a B) by (forward_using lemma_collinearorder).
 assert (Col a b c) by (forward_using lemma_collinearorder).
 assert (eq c c) by (conclude cn_equalityreflexive).
 assert (Meet a b C D) by (conclude_def Meet ).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS P M d /\ BetS a b M)) by (conclude postulate_Pasch_outer);destruct Tf as [M];spliter.
assert (BetS M b a) by (conclude axiom_betweennesssymmetry).
assert (BetS P b c) by (conclude axiom_betweennesssymmetry).
assert (Col a b M) by (conclude_def Col ).
assert (Col B a b) by (conclude lemma_collinear4).
assert (Col b a B) by (forward_using lemma_collinearorder).
assert (Col b a M) by (forward_using lemma_collinearorder).
assert (neq b a) by (conclude lemma_inequalitysymmetric).
assert (Col a B M) by (conclude lemma_collinear4).
assert (Col a B A) by (forward_using lemma_collinearorder).
assert (Col A B M).
by cases on (neq a B \/ eq a B).
{
 assert (Col B M A) by (conclude lemma_collinear4).
 assert (Col A B M) by (forward_using lemma_collinearorder).
 close.
 }
{
 assert (neq A a) by (conclude cn_equalitysub).
 assert (Col A a b) by (conclude cn_equalitysub).
 assert (Col b a A) by (forward_using lemma_collinearorder).
 assert (Col a A M) by (conclude lemma_collinear4).
 assert (Col a A B) by (forward_using lemma_collinearorder).
 assert (neq a A) by (conclude lemma_inequalitysymmetric).
 assert (Col A M B) by (conclude lemma_collinear4).
 assert (Col A B M) by (forward_using lemma_collinearorder).
 close.
 }
(** cases *)
assert (BetS c b P) by (conclude axiom_betweennesssymmetry).
assert (BetS d M P) by (conclude axiom_betweennesssymmetry).
assert (~ Col A B c).
 {
 intro.
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Col A B d).
 {
 intro.
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (OS c d A B) by (conclude_def OS ).
assert (~ Meet A B c d).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists R, (neq A B /\ neq c d /\ Col A B R /\ Col c d R)) by (conclude_def Meet );destruct Tf as [R];spliter.
 assert (Col D c d) by (conclude lemma_collinear4).
 assert (Col D C c) by (forward_using lemma_collinearorder).
 assert (Col D C d) by (forward_using lemma_collinearorder).
 assert (neq D C) by (conclude lemma_inequalitysymmetric).
 assert (Col C c d) by (conclude lemma_collinear4).
 assert (Col c d C) by (forward_using lemma_collinearorder).
 assert (Col c d D) by (forward_using lemma_collinearorder).
 assert (Col C D R) by (conclude lemma_collinear5).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (TP A B c d) by (conclude_def TP ).
assert (eq C C) by (conclude cn_equalityreflexive).
assert (Col C D C) by (conclude_def Col ).
assert (Col c d C) by (conclude lemma_collinear5).
assert (~ ~ TP A B C D).
 {
 intro.
 assert (neq D C) by (conclude lemma_inequalitysymmetric).
 assert (~ neq C d).
  {
  intro.
  assert (TP A B C d) by (conclude lemma_parallelcollinear).
  assert (TP A B d C) by (forward_using lemma_tarskiparallelflip).
  assert (Col d C D) by (forward_using lemma_collinearorder).
  assert (TP A B D C) by (conclude lemma_parallelcollinear).
  assert (TP A B C D) by (forward_using lemma_tarskiparallelflip).
  contradict.
  }
 assert (TP A B c C) by (conclude cn_equalitysub).
 assert (Col c C D) by (forward_using lemma_collinearorder).
 assert (TP A B D C) by (conclude lemma_parallelcollinear).
 assert (TP A B C D) by (forward_using lemma_tarskiparallelflip).
 contradict.
 }
close.
Qed.

End Euclid.


