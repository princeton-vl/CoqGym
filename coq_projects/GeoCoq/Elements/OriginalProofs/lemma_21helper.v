Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthanbetween.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthanadditive.

Section Euclid.
Context `{Ax:euclidean_neutral_ruler_compass}.
Lemma lemma_21helper : 
   forall A B C E, 
   TG B A A E B E -> BetS A E C ->
   TT B A A C B E E C.
Proof.
intros.
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS B A H /\ Cong A H A E /\ Lt B E B H)) by (conclude_def TG );destruct Tf as [H];spliter.
assert (neq B A) by (forward_using lemma_betweennotequal).
assert (~ eq B E).
 {
 intro.
 assert (Lt B B B H) by (conclude cn_equalitysub).
 let Tf:=fresh in
 assert (Tf:exists K, (BetS B K H /\ Cong B K B B)) by (conclude_def Lt );destruct Tf as [K];spliter.
 assert (~ neq B K).
  {
  intro.
  assert (neq B B) by (conclude axiom_nocollapse).
  assert (eq B B) by (conclude cn_equalityreflexive).
  contradict.
  }
 assert (BetS B B H) by (conclude cn_equalitysub).
 assert (neq B B) by (forward_using lemma_betweennotequal).
 assert (eq B B) by (conclude cn_equalityreflexive).
 contradict.
 }
assert (neq A C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists F, (BetS B A F /\ Cong A F A C)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (neq E C) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists G, (BetS B E G /\ Cong E G E C)) by (conclude lemma_extension);destruct Tf as [G];spliter.
assert (Cong A C A F) by (conclude lemma_congruencesymmetric).
assert (Cong A E A H) by (conclude lemma_congruencesymmetric).
assert (Cong A E A E) by (conclude cn_congruencereflexive).
assert (Lt A E A C) by (conclude_def Lt ).
assert (Lt A E A F) by (conclude lemma_lessthancongruence).
assert (Lt A H A F) by (conclude lemma_lessthancongruence2).
assert (Out A H F) by (conclude_def Out ).
assert (BetS A H F) by (conclude lemma_lessthanbetween).
assert (Cong E C H F) by (conclude lemma_differenceofparts).
assert (Cong E G H F) by (conclude lemma_congruencetransitive).
assert (BetS B H F) by (conclude lemma_3_7a).
assert (Lt B G B F) by (conclude lemma_lessthanadditive).
assert (TG B A A C B G) by (conclude_def TG ).
assert (TT B A A C B E E C) by (conclude_def TT ).
close.
Qed.

End Euclid.
