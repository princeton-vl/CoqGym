Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax1:area}.

Lemma lemma_rectanglerotate : 
   forall A B C D, 
   RE A B C D ->
   RE B C D A.
Proof.
intros.
assert ((Per D A B /\ Per A B C /\ Per B C D /\ Per C D A /\ CR A C B D)) by (conclude_def RE ).
let Tf:=fresh in
assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (BetS C M A) by (conclude axiom_betweennesssymmetry).
assert (CR B D C A) by (conclude_def CR ).
assert (RE B C D A) by (conclude_def RE ).
close.
Qed.

End Euclid.


