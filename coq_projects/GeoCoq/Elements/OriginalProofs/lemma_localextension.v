Require Export GeoCoq.Elements.OriginalProofs.euclidean_defs.
Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.


Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_localextension : 
   forall A B Q, 
   neq A B -> neq B Q ->
   exists X, BetS A B X /\ Cong B X B Q.
Proof.
intros.
assert (eq B B) by (conclude cn_equalityreflexive).
let Tf:=fresh in
assert (Tf:exists J, CI J B B Q) by (conclude postulate_Euclid3);destruct Tf as [J];spliter.
assert (InCirc B J) by (conclude_def InCirc ).
let Tf:=fresh in
assert (Tf:exists C E, (Col A B C /\ BetS A B E /\ OnCirc C J /\ OnCirc E J /\ BetS C B E)) by (conclude postulate_line_circle);destruct Tf as [C[E]];spliter.
assert (Cong B E B Q) by (conclude axiom_circle_center_radius).
close.
Unshelve.
exact A.
exact A.
Qed.

End Euclid.
