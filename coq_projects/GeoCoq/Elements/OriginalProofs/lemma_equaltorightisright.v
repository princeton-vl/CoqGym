Require Export GeoCoq.Elements.OriginalProofs.lemma_8_3.
Require Export GeoCoq.Elements.OriginalProofs.lemma_8_2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_equaltorightisright : 
   forall A B C a b c, 
   Per A B C -> CongA a b c A B C ->
   Per a b c.
Proof.
intros.
assert (CongA A B C a b c) by (conclude lemma_equalanglessymmetric).
let Tf:=fresh in
assert (Tf:exists E F e f, (Out B A E /\ Out B C F /\ Out b a e /\ Out b c f /\ Cong B E b e /\ Cong B F b f /\ Cong E F e f /\ nCol A B C)) by (conclude_def CongA );destruct Tf as [E[F[e[f]]]];spliter.
assert (Per A B F) by (conclude lemma_8_3).
assert (Per F B A) by (conclude lemma_8_2).
assert (Per F B E) by (conclude lemma_8_3).
assert (Per E B F) by (conclude lemma_8_2).
assert (neq B E) by (conclude lemma_raystrict).
assert (neq E B) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists W, (BetS E B W /\ Cong E B W B /\ Cong E F W F /\ neq B F)) by (conclude_def Per );destruct Tf as [W];spliter.
assert (neq b e) by (conclude axiom_nocollapse).
assert (neq e b) by (conclude lemma_inequalitysymmetric).
let Tf:=fresh in
assert (Tf:exists w, (BetS e b w /\ Cong b w e b)) by (conclude lemma_extension);destruct Tf as [w];spliter.
assert (Cong e b E B) by (forward_using lemma_doublereverse).
assert (Cong b w E B) by (conclude lemma_congruencetransitive).
assert (Cong E B B W) by (forward_using lemma_congruenceflip).
assert (Cong b w B W) by (conclude lemma_congruencetransitive).
assert (Cong b f B F) by (conclude lemma_congruencesymmetric).
assert (Cong e f E F) by (conclude lemma_congruencesymmetric).
assert (Cong e w E W) by (conclude cn_sumofparts).
assert (Cong f w F W) by (conclude (axiom_5_line e b w f E B W F)).
assert (Cong e b B W) by (conclude lemma_congruencetransitive).
assert (Cong B W b w) by (conclude lemma_congruencesymmetric).
assert (Cong e b b w) by (conclude lemma_congruencetransitive).
assert (Cong e b w b) by (forward_using lemma_congruenceflip).
assert (Cong e f W F) by (conclude lemma_congruencetransitive).
assert (Cong W F w f) by (forward_using lemma_doublereverse).
assert (Cong e f w f) by (conclude lemma_congruencetransitive).
assert (neq b f) by (conclude lemma_raystrict).
assert (Per e b f) by (conclude_def Per ).
assert (Out b f c) by (conclude lemma_ray5).
assert (Per e b c) by (conclude lemma_8_3).
assert (Per c b e) by (conclude lemma_8_2).
assert (Out b e a) by (conclude lemma_ray5).
assert (Per c b a) by (conclude lemma_8_3).
assert (Per a b c) by (conclude lemma_8_2).
close.
Qed.

End Euclid.


