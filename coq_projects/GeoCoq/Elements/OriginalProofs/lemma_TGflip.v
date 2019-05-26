Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TGflip : 
   forall A B C a b c, 
   TG A a B b C c ->
   TG a A B b C c /\ TG A a B b c C.
Proof.
intros.
rename_H H;let Tf:=fresh in
assert (Tf:exists H, (BetS A a H /\ Cong a H B b /\ Lt C c A H)) by (conclude_def TG );destruct Tf as [H];spliter.
assert (neq A a) by (forward_using lemma_betweennotequal).
assert (neq a A) by (conclude lemma_inequalitysymmetric).
assert (neq a H) by (forward_using lemma_betweennotequal).
assert (neq B b) by (conclude axiom_nocollapse).
let Tf:=fresh in
assert (Tf:exists h, (BetS a A h /\ Cong A h B b)) by (conclude lemma_extension);destruct Tf as [h];spliter.
assert (Cong A a a A) by (conclude cn_equalityreverse).
assert (Cong B b A h) by (conclude lemma_congruencesymmetric).
assert (Cong a H A h) by (conclude lemma_congruencetransitive).
assert (Cong A H a h) by (conclude cn_sumofparts).
assert (Lt C c a h) by (conclude lemma_lessthancongruence).
assert (TG a A B b C c) by (conclude_def TG ).
assert (Cong C c c C) by (conclude cn_equalityreverse).
assert (Lt c C A H) by (conclude lemma_lessthancongruence2).
assert (TG A a B b c C) by (conclude_def TG ).
assert (Lt C c a h) by (conclude lemma_lessthancongruence).
close.
Qed.

End Euclid.


