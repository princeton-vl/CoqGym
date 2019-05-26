Require Export GeoCoq.Elements.OriginalProofs.lemma_equalanglestransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_supplements.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_supplements2 : 
   forall A B C D E F J K L P Q R, 
   RT A B C P Q R -> CongA A B C J K L -> RT J K L D E F ->
   CongA P Q R D E F /\ CongA D E F P Q R.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d e, (Supp a b c d e /\ CongA A B C a b c /\ CongA P Q R d b e)) by (conclude_def RT );destruct Tf as [a[b[c[d[e]]]]];spliter.
let Tf:=fresh in
assert (Tf:exists j k l m n, (Supp j k l m n /\ CongA J K L j k l /\ CongA D E F m k n)) by (conclude_def RT );destruct Tf as [j[k[l[m[n]]]]];spliter.
assert (CongA a b c A B C) by (conclude lemma_equalanglessymmetric).
assert (CongA a b c J K L) by (conclude lemma_equalanglestransitive).
assert (CongA a b c j k l) by (conclude lemma_equalanglestransitive).
assert (CongA d b e m k n) by (conclude lemma_supplements).
assert (CongA P Q R m k n) by (conclude lemma_equalanglestransitive).
assert (CongA m k n D E F) by (conclude lemma_equalanglessymmetric).
assert (CongA P Q R D E F) by (conclude lemma_equalanglestransitive).
assert (CongA D E F P Q R) by (conclude lemma_equalanglessymmetric).
close.
Qed.

End Euclid.


