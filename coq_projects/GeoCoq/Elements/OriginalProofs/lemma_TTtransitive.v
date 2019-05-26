Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthantransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTtransitive : 
   forall A B C D E F G H P Q R S, 
   TT A B C D E F G H -> TT E F G H P Q R S ->
   TT A B C D P Q R S.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists K, (BetS E F K /\ Cong F K G H /\ TG A B C D E K)) by (conclude_def TT );destruct Tf as [K];spliter.
let Tf:=fresh in
assert (Tf:exists J, (BetS A B J /\ Cong B J C D /\ Lt E K A J)) by (conclude_def TG );destruct Tf as [J];spliter.
let Tf:=fresh in
assert (Tf:exists L, (BetS P Q L /\ Cong Q L R S /\ TG E F G H P L)) by (conclude_def TT );destruct Tf as [L];spliter.
let Tf:=fresh in
assert (Tf:exists M, (BetS E F M /\ Cong F M G H /\ Lt P L E M)) by (conclude_def TG );destruct Tf as [M];spliter.
assert (eq K K) by (conclude cn_equalityreflexive).
assert (neq F K) by (forward_using lemma_betweennotequal).
assert (neq F M) by (forward_using lemma_betweennotequal).
assert (Out F K M) by (conclude_def Out ).
assert (Out F K K) by (conclude lemma_ray4).
assert (Cong G H F M) by (conclude lemma_congruencesymmetric).
assert (Cong F K F M) by (conclude lemma_congruencetransitive).
assert (eq K M) by (conclude lemma_layoffunique).
assert (Lt P L E K) by (conclude cn_equalitysub).
assert (Lt P L A J) by (conclude lemma_lessthantransitive).
assert (TG A B C D P L) by (conclude_def TG ).
assert (TT A B C D P Q R S) by (conclude_def TT ).
close.
Qed.

End Euclid.