Require Export GeoCoq.Elements.OriginalProofs.lemma_TGsymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTorder : 
   forall A B C D E F G H, 
   TT A B C D E F G H ->
   TT C D A B E F G H.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS E F J /\ Cong F J G H /\ TG A B C D E J)) by (conclude_def TT );destruct Tf as [J];spliter.
assert (TG C D A B E J) by (conclude lemma_TGsymmetric).
assert (TT C D A B E F G H) by (conclude_def TT ).
close.
Qed.

End Euclid.