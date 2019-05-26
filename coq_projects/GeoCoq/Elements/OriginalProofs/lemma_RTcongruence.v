Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_RTcongruence : 
   forall A B C D E F P Q R, 
   RT A B C D E F -> CongA A B C P Q R ->
   RT P Q R D E F.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d e, (Supp a b c d e /\ CongA A B C a b c /\ CongA D E F d b e)) by (conclude_def RT );destruct Tf as [a[b[c[d[e]]]]];spliter.
assert (CongA P Q R A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA P Q R a b c) by (conclude lemma_equalanglestransitive).
assert (RT P Q R D E F) by (conclude_def RT ).
close.
Qed.

End Euclid.


