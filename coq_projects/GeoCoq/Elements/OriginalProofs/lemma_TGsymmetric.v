Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TGsymmetric : 
   forall A B C a b c, 
   TG A a B b C c ->
   TG B b A a C c.
Proof.
intros.
rename_H H;
let Tf:=fresh in
assert (Tf:exists H, (BetS A a H /\ Cong a H B b /\ Lt C c A H)) by (conclude_def TG );destruct Tf as [H];spliter.
assert (neq a H) by (forward_using lemma_betweennotequal).
assert (neq B b) by (conclude axiom_nocollapse).
assert (neq A a) by (forward_using lemma_betweennotequal).
let Tf:=fresh in
assert (Tf:exists F, (BetS B b F /\ Cong b F A a)) by (conclude lemma_extension);destruct Tf as [F];spliter.
assert (Cong a A F b) by (forward_using lemma_doublereverse).
assert (Cong A a F b) by (forward_using lemma_congruenceflip).
assert (Cong a H b B) by (forward_using lemma_congruenceflip).
assert (BetS F b B) by (conclude axiom_betweennesssymmetry).
assert (Cong A H F B) by (conclude cn_sumofparts).
assert (Cong A H B F) by (forward_using lemma_congruenceflip).
assert (Lt C c B F) by (conclude lemma_lessthancongruence).
assert (TG B b A a C c) by (conclude_def TG ).
close.
Qed.

End Euclid.


