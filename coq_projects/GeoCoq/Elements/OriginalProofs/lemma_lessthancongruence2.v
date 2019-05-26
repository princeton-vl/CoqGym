Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_lessthancongruence2 : 
   forall A B C D E F, 
   Lt A B C D -> Cong A B E F ->
   Lt E F C D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists G, (BetS C G D /\ Cong C G A B)) by (conclude_def Lt );destruct Tf as [G];spliter.
assert (Cong C G E F) by (conclude lemma_congruencetransitive).
assert (Lt E F C D) by (conclude_def Lt ).
close.
Qed.

End Euclid.


