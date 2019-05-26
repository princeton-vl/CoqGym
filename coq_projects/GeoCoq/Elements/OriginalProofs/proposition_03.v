Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_03 : 
   forall A B C D E F, 
   Lt C D A B -> Cong E F A B ->
   exists X, BetS E X F /\ Cong E X C D.
Proof.
intros.
assert (Cong A B E F) by (conclude lemma_congruencesymmetric).
assert (Lt C D E F) by (conclude lemma_lessthancongruence).
let Tf:=fresh in
assert (Tf:exists G, (BetS E G F /\ Cong E G C D)) by (conclude_def Lt );destruct Tf as [G];spliter.
close.
Qed.

End Euclid.


