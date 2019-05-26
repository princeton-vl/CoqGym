Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_angleorderrespectscongruence2 : 
   forall A B C D E F a b c, 
   LtA A B C D E F -> CongA a b c A B C ->
   LtA a b c D E F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists P Q R, (BetS P Q R /\ Out E D P /\ Out E F R /\ CongA A B C D E Q)) by (conclude_def LtA );destruct Tf as [P[Q[R]]];spliter.
assert (CongA a b c D E Q) by (conclude lemma_equalanglestransitive).
assert (LtA a b c D E F) by (conclude_def LtA ).
close.
Qed.

End Euclid.


