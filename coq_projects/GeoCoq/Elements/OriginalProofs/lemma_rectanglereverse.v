Require Export GeoCoq.Elements.OriginalProofs.lemma_8_2.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_rectanglereverse : 
   forall A B C D, 
   RE A B C D ->
   RE D C B A.
Proof.
intros.
assert ((Per D A B /\ Per A B C /\ Per B C D /\ Per C D A /\ CR A C B D)) by (conclude_def RE ).
assert (Per A D C) by (conclude lemma_8_2).
assert (Per D C B) by (conclude lemma_8_2).
assert (Per C B A) by (conclude lemma_8_2).
assert (Per B A D) by (conclude lemma_8_2).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (BetS D M B) by (conclude axiom_betweennesssymmetry).
assert (CR D B C A) by (conclude_def CR ).
assert (RE D C B A) by (conclude_def RE ).
close.
Qed.

End Euclid.


