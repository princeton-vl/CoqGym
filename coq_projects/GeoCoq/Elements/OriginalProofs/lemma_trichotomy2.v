Require Export GeoCoq.Elements.OriginalProofs.lemma_lessthancongruence.
Require Export GeoCoq.Elements.OriginalProofs.lemma_3_6b.
Require Export GeoCoq.Elements.OriginalProofs.lemma_partnotequalwhole.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_trichotomy2 : 
   forall A B C D, 
   Lt A B C D ->
   ~ Lt C D A B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E, (BetS C E D /\ Cong C E A B)) by (conclude_def Lt );destruct Tf as [E];spliter.
assert (Cong A B C E) by (conclude lemma_congruencesymmetric).
assert (~ Lt C D A B).
 {
 intro.
 assert (Lt C D C E) by (conclude lemma_lessthancongruence).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS C F E /\ Cong C F C D)) by (conclude_def Lt );destruct Tf as [F];spliter.
 assert (BetS C F D) by (conclude lemma_3_6b).
 assert (~ Cong C F C D) by (conclude lemma_partnotequalwhole).
 contradict.
 }
close.
Qed.

End Euclid.


