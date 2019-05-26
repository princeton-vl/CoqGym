Require Export GeoCoq.Elements.OriginalProofs.lemma_layoff.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ray4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_layoffunique.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_lessthantransitive : 
   forall A B C D E F, 
   Lt A B C D -> Lt C D E F ->
   Lt A B E F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists G, (BetS C G D /\ Cong C G A B)) by (conclude_def Lt );destruct Tf as [G];spliter.
rename_H H;
let Tf:=fresh in
assert (Tf:exists H, (BetS E H F /\ Cong E H C D)) by (conclude_def Lt );destruct Tf as [H];spliter.
assert (neq E H) by (forward_using lemma_betweennotequal).
assert (neq C G) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists K, (Out E H K /\ Cong E K C G)) by (conclude lemma_layoff);destruct Tf as [K];spliter.
assert (Cong E K A B) by (conclude lemma_congruencetransitive).
assert ((BetS E K H \/ eq H K \/ BetS E H K)) by (conclude lemma_ray1).
assert (BetS E K H).
by cases on (BetS E K H \/ eq H K \/ BetS E H K).
{
 close.
 }
{
 assert (Cong C G E K) by (conclude lemma_congruencesymmetric).
 assert (Cong C G E H) by (conclude cn_equalitysub).
 assert (Cong C G C D) by (conclude lemma_congruencetransitive).
 assert (Out C G D) by (conclude lemma_ray4).
 assert (eq G G) by (conclude cn_equalityreflexive).
 assert (Out C G G) by (conclude lemma_ray4).
 assert (~ ~ BetS E K H).
  {
  intro.
  assert (eq G D) by (conclude lemma_layoffunique).
  assert (neq G D) by (forward_using lemma_betweennotequal).
  contradict.
  }
 close.
 }
{
 assert (Cong C D E H) by (conclude lemma_congruencesymmetric).
 assert (Cong C G E K) by (conclude lemma_congruencesymmetric).
 assert (neq C D) by (forward_using lemma_betweennotequal).
 assert (neq H K) by (forward_using lemma_betweennotequal).
 let Tf:=fresh in
 assert (Tf:exists J, (BetS C D J /\ Cong D J H K)) by (conclude lemma_extension);destruct Tf as [J];spliter.
 assert (Out C D J) by (conclude lemma_ray4).
 assert (Out C D G) by (conclude lemma_ray4).
 assert (Cong C J E K) by (conclude cn_sumofparts).
 assert (Cong C J C G) by (conclude lemma_congruencetransitive).
 assert (eq J G) by (conclude lemma_layoffunique).
 assert (BetS G D J) by (conclude lemma_3_6a).
 assert (~ ~ BetS E K H).
  {
  intro.
  assert (neq G J) by (forward_using lemma_betweennotequal).
  assert (neq J G) by (conclude lemma_inequalitysymmetric).
  contradict.
  }
 close.
 }
(** cases *)
assert (BetS E K F) by (conclude lemma_3_6b).
assert (Lt A B E F) by (conclude_def Lt ).
close.
Qed.

End Euclid.


