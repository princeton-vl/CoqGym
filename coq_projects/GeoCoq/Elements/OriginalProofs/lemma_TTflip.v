Require Export GeoCoq.Elements.OriginalProofs.lemma_TGflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_TGsymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_TTflip : 
   forall A B C D E F G H, 
   TT A B C D E F G H ->
   TT B A D C E F G H.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists J, (BetS E F J /\ Cong F J G H /\ TG A B C D E J)) by (conclude_def TT );destruct Tf as [J];spliter.
assert (TG B A C D E J) by (forward_using lemma_TGflip).
assert (TG C D B A E J) by (conclude lemma_TGsymmetric).
assert (TG D C B A E J) by (forward_using lemma_TGflip).
assert (TG B A D C E J) by (conclude lemma_TGsymmetric).
assert (TT B A D C E F G H) by (conclude_def TT ).
close.
Qed.

End Euclid.