Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_7.
Require Export GeoCoq.Elements.OriginalProofs.lemma_legsmallerhypotenuse.
Require Export GeoCoq.Elements.OriginalProofs.lemma_trichotomy2.
Require Export GeoCoq.Elements.OriginalProofs.lemma_tworays.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_altitudeofrighttriangle : 
   forall A B C M p, 
   Per B A C -> Per A M p -> Col B C p -> Col B C M ->
   BetS B M C.
Proof.
intros.
assert (nCol B A C) by (conclude lemma_rightangleNC).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (~ eq B M).
 {
 intro.
 assert (Per A B p) by (conclude cn_equalitysub).
 assert (Col p B C) by (forward_using lemma_collinearorder).
 assert (Per p B A) by (conclude lemma_8_2).
 assert (Per C B A) by (conclude lemma_collinearright).
 assert (~ Per C B A) by (conclude lemma_8_7).
 contradict.
 }
assert (Per p M A) by (conclude lemma_8_2).
assert (Col C B p) by (forward_using lemma_collinearorder).
assert (Col C B M) by (forward_using lemma_collinearorder).
assert (nCol B A C) by (conclude lemma_rightangleNC).
assert (neq C B) by (forward_using lemma_NCdistinct).
assert (Col B p M) by (conclude lemma_collinear4).
assert (Col p M B) by (forward_using lemma_collinearorder).
assert (Per B M A) by (conclude lemma_collinearright).
assert (Col B C p) by (forward_using lemma_collinearorder).
assert (Col B C M) by (forward_using lemma_collinearorder).
assert (neq B C) by (conclude lemma_inequalitysymmetric).
assert (Col C p M) by (conclude lemma_collinear4).
assert (Col p M C) by (forward_using lemma_collinearorder).
assert (Per C A B) by (conclude lemma_8_2).
assert (~ eq C M).
 {
 intro.
 assert (Per A C p) by (conclude cn_equalitysub).
 assert (Col p C B) by (forward_using lemma_collinearorder).
 assert (Per p C A) by (conclude lemma_8_2).
 assert (Per B C A) by (conclude lemma_collinearright).
 assert (~ Per B C A) by (conclude lemma_8_7).
 contradict.
 }
assert (Per C M A) by (conclude lemma_collinearright).
assert (Per A M B) by (conclude lemma_8_2).
assert (Per A M C) by (conclude lemma_8_2).
assert (Lt M B A B) by (conclude lemma_legsmallerhypotenuse).
assert (Lt B A B C) by (conclude lemma_legsmallerhypotenuse).
assert (Cong B A A B) by (conclude cn_equalityreverse).
assert (Lt A B B C) by (conclude lemma_lessthancongruence2).
assert (Lt M B B C) by (conclude lemma_lessthantransitive).
assert (Cong M B B M) by (conclude cn_equalityreverse).
assert (Lt B M B C) by (conclude lemma_lessthancongruence2).
assert (Lt M C A C) by (conclude lemma_legsmallerhypotenuse).
assert (Cong M C C M) by (conclude cn_equalityreverse).
assert (Lt C M A C) by (conclude lemma_lessthancongruence2).
assert (Lt A C B C) by (conclude lemma_legsmallerhypotenuse).
assert (Lt C M B C) by (conclude lemma_lessthantransitive).
assert (~ BetS M B C).
 {
 intro.
 assert (BetS C B M) by (conclude axiom_betweennesssymmetry).
 assert (Cong C B C B) by (conclude cn_congruencereflexive).
 assert (Lt C B C M) by (conclude_def Lt ).
 assert (Cong C B B C) by (conclude cn_equalityreverse).
 assert (Lt B C C M) by (conclude lemma_lessthancongruence2).
 assert (~ Lt C M B C) by (conclude lemma_trichotomy2).
 contradict.
 }
assert ((eq B C \/ eq B M \/ eq C M \/ BetS C B M \/ BetS B C M \/ BetS B M C)) by (conclude_def Col ).
assert (Out B C M).
by cases on (eq B C \/ eq B M \/ eq C M \/ BetS C B M \/ BetS B C M \/ BetS B M C).
{
 assert (~ ~ Out B C M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out B C M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out B C M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out B C M).
  {
  intro.
  assert (BetS M B C) by (conclude axiom_betweennesssymmetry).
  contradict.
  }
 close.
 }
{
 assert (Out B C M) by (conclude lemma_ray4).
 close.
 }
{
 assert (Out B M C) by (conclude lemma_ray4).
 assert (Out B C M) by (conclude lemma_ray5).
 close.
 }
(** cases *)
assert (~ BetS B C M).
 {
 intro.
 assert (Cong B C B C) by (conclude cn_congruencereflexive).
 assert (Lt B C B M) by (conclude_def Lt ).
 assert (~ Lt B M B C) by (conclude lemma_trichotomy2).
 contradict.
 }
assert (Out C B M).
by cases on (eq B C \/ eq B M \/ eq C M \/ BetS C B M \/ BetS B C M \/ BetS B M C).
{
 assert (~ ~ Out C B M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out C B M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (~ ~ Out C B M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (Out C B M) by (conclude lemma_ray4).
 close.
 }
{
 assert (~ ~ Out C B M).
  {
  intro.
  contradict.
  }
 close.
 }
{
 assert (BetS C M B) by (conclude axiom_betweennesssymmetry).
 assert (Out C M B) by (conclude lemma_ray4).
 assert (Out C B M) by (conclude lemma_ray5).
 close.
 }
(** cases *)
assert (BetS B M C) by (conclude lemma_tworays).
close.
Qed.

End Euclid.


