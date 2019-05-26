Require Export GeoCoq.Elements.OriginalProofs.lemma_supplementsymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_ABCequalsCBA.
Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_RTsymmetric : 
   forall A B C D E F, 
   RT A B C D E F ->
   RT D E F A B C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d e, (Supp a b c d e /\ CongA A B C a b c /\ CongA D E F d b e)) by (conclude_def RT );destruct Tf as [a[b[c[d[e]]]]];spliter.
assert (Supp e b d c a) by (conclude lemma_supplementsymmetric).
assert (nCol d b e) by (conclude lemma_equalanglesNC).
assert (CongA d b e e b d) by (conclude lemma_ABCequalsCBA).
assert (nCol a b c) by (conclude lemma_equalanglesNC).
assert (CongA a b c c b a) by (conclude lemma_ABCequalsCBA).
assert (CongA D E F e b d) by (conclude lemma_equalanglestransitive).
assert (CongA A B C c b a) by (conclude lemma_equalanglestransitive).
assert (RT D E F A B C) by (conclude_def RT ).
close.
Qed.

End Euclid.


