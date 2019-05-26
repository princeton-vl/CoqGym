Require Export GeoCoq.Elements.OriginalProofs.lemma_raystrict.
Require Export GeoCoq.Elements.OriginalProofs.lemma_collinear4.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_crossbar : 
   forall A B C E U V, 
   Triangle A B C -> BetS A E C -> Out B A U -> Out B C V ->
   exists X, Out B E X /\ BetS U X V.
Proof.
intros.
assert (nCol A B C) by (conclude_def Triangle ).
assert (~ eq B E).
 {
 intro.
 assert (~ BetS A B C).
  {
  intro.
  assert (Col A B C) by (conclude_def Col ).
  contradict.
  }
 assert (BetS A B C) by (conclude cn_equalitysub).
 contradict.
 }
assert (~ eq B A).
 {
 intro.
 assert (eq A B) by (conclude lemma_equalitysymmetric).
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (~ eq B C).
 {
 intro.
 assert (Col A B C) by (conclude_def Col ).
 contradict.
 }
assert (neq B U) by (conclude lemma_raystrict).
assert (neq B V) by (conclude lemma_raystrict).
let Tf:=fresh in
assert (Tf:exists P, (BetS B A P /\ Cong A P B U)) by (conclude lemma_extension);destruct Tf as [P];spliter.
let Tf:=fresh in
assert (Tf:exists Q, (BetS B C Q /\ Cong C Q B V)) by (conclude lemma_extension);destruct Tf as [Q];spliter.
assert (~ Col B Q A).
 {
 intro.
 assert (Col Q B A) by (forward_using lemma_collinearorder).
 assert (Col B C Q) by (conclude_def Col ).
 assert (Col Q B C) by (forward_using lemma_collinearorder).
 assert (neq B Q) by (forward_using lemma_betweennotequal).
 assert (neq Q B) by (conclude lemma_inequalitysymmetric).
 assert (Col B A C) by (conclude lemma_collinear4).
 assert (Col A B C) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists F, (BetS A F Q /\ BetS B E F)) by (conclude postulate_Pasch_outer);destruct Tf as [F];spliter.
assert (BetS Q F A) by (conclude axiom_betweennesssymmetry).
assert (~ Col B P Q).
 {
 intro.
 assert (Col P B Q) by (forward_using lemma_collinearorder).
 assert (Col B A P) by (conclude_def Col ).
 assert (Col P B A) by (forward_using lemma_collinearorder).
 assert (neq B P) by (forward_using lemma_betweennotequal).
 assert (neq P B) by (conclude lemma_inequalitysymmetric).
 assert (Col B Q A) by (conclude lemma_collinear4).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists W, (BetS Q W P /\ BetS B F W)) by (conclude postulate_Pasch_outer);destruct Tf as [W];spliter.
assert (BetS B E W) by (conclude lemma_3_6b).
let Tf:=fresh in
assert (Tf:exists J, (BetS J B U /\ BetS J B A)) by (conclude_def Out );destruct Tf as [J];spliter.
assert (Cong A P P A) by (conclude cn_equalityreverse).
assert (Cong B U A P) by (conclude lemma_congruencesymmetric).
assert (Cong B U P A) by (conclude lemma_congruencetransitive).
assert (Cong P A B U) by (conclude lemma_congruencesymmetric).
assert (BetS P A B) by (conclude axiom_betweennesssymmetry).
assert (Lt B U P B) by (conclude_def Lt ).
assert (Cong P B B P) by (conclude cn_equalityreverse).
assert (Lt B U B P) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists S, (BetS B S P /\ Cong B S B U)) by (conclude_def Lt );destruct Tf as [S];spliter.
assert (BetS J B P) by (conclude lemma_3_7b).
assert (BetS J B S) by (conclude axiom_innertransitivity).
assert (eq S U) by (conclude lemma_extensionunique).
assert (BetS B U P) by (conclude cn_equalitysub).
let Tf:=fresh in
assert (Tf:exists K, (BetS K B V /\ BetS K B C)) by (conclude_def Out );destruct Tf as [K];spliter.
assert (Cong B V C Q) by (conclude lemma_congruencesymmetric).
assert (Cong C Q Q C) by (conclude cn_equalityreverse).
assert (Cong B V Q C) by (conclude lemma_congruencetransitive).
assert (Cong Q C B V) by (conclude lemma_congruencesymmetric).
assert (BetS Q C B) by (conclude axiom_betweennesssymmetry).
assert (Lt B V Q B) by (conclude_def Lt ).
assert (Cong Q B B Q) by (conclude cn_equalityreverse).
assert (Lt B V B Q) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists R, (BetS B R Q /\ Cong B R B V)) by (conclude_def Lt );destruct Tf as [R];spliter.
assert (BetS K B Q) by (conclude lemma_3_7b).
assert (BetS K B R) by (conclude axiom_innertransitivity).
assert (eq R V) by (conclude lemma_extensionunique).
assert (BetS B V Q) by (conclude cn_equalitysub).
assert (~ Col Q P B).
 {
 intro.
 assert (Col B P Q) by (forward_using lemma_collinearorder).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS Q M U /\ BetS B M W)) by (conclude postulate_Pasch_inner);destruct Tf as [M];spliter.
assert (BetS U M Q) by (conclude axiom_betweennesssymmetry).
assert (~ Col U Q B).
 {
 intro.
 assert (Col B U P) by (conclude_def Col ).
 assert (Col B U Q) by (forward_using lemma_collinearorder).
 assert (neq B U) by (forward_using lemma_betweennotequal).
 assert (Col U B P) by (forward_using lemma_collinearorder).
 assert (Col U B Q) by (forward_using lemma_collinearorder).
 assert (neq U B) by (conclude lemma_inequalitysymmetric).
 assert (Col B P Q) by (conclude lemma_collinear4).
 assert (Col Q P B) by (forward_using lemma_collinearorder).
 contradict.
 }
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS U H V /\ BetS B H M)) by (conclude postulate_Pasch_inner);destruct Tf as [H];spliter.
assert (~ eq E B).
 {
 intro.
 assert (eq B E) by (conclude lemma_equalitysymmetric).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists N, (BetS E B N /\ Cong B N B E)) by (conclude lemma_extension);destruct Tf as [N];spliter.
assert (BetS N B E) by (conclude axiom_betweennesssymmetry).
assert (BetS B H W) by (conclude lemma_3_6b).
assert (BetS N B W) by (conclude lemma_3_7b).
assert (BetS N B H) by (conclude axiom_innertransitivity).
assert (Out B E H) by (conclude_def Out ).
close.
Qed.

End Euclid.


