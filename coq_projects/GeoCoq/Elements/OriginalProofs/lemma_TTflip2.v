Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTflip2 : 
   forall A B C D E F G H, 
   TT A B C D E F G H ->
   TT A B C D H G F E.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS E F J /\ Cong F J G H /\ TG A B C D E J)) by (conclude_def TT );destruct Tf as [J];spliter.
let Tf:=fresh in
assert (Tf:exists K, (BetS A B K /\ Cong B K C D /\ Lt E J A K)) by (conclude_def TG );destruct Tf as [K];spliter.
assert (neq F J) by (forward_using lemma_betweennotequal).
assert (neq G H) by (conclude axiom_nocollapse).
assert (neq H G) by (conclude lemma_inequalitysymmetric).
assert (neq E F) by (forward_using lemma_betweennotequal).
assert (neq F E) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists L, (BetS H G L /\ Cong G L F E)) by (conclude lemma_extension);destruct Tf as [L];spliter.
assert (Cong L G E F) by (forward_using lemma_congruenceflip).
assert (Cong G H F J) by (conclude lemma_congruencesymmetric).
assert (BetS L G H) by (conclude axiom_betweennesssymmetry).
assert (Cong L H E J) by (conclude cn_sumofparts).
assert (Cong H L L H) by (conclude cn_equalityreverse).
assert (Cong H L E J) by (conclude lemma_congruencetransitive).
assert (Cong E J H L) by (conclude lemma_congruencesymmetric).
assert (Lt H L A K) by (conclude lemma_lessthancongruence2).
assert (TG A B C D H L) by (conclude_def TG ).
assert (TT A B C D H G F E) by (conclude_def TT ).
close.
Qed.

End Euclid.