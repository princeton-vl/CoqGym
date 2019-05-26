Require Export GeoCoq.Elements.OriginalProofs.lemma_planeseparation.

Section Euclid.

Context `{Ax1:euclidean_neutral_ruler_compass}.

Lemma lemma_samesidetransitive : 
   forall A B P Q R, 
   OS P Q A B -> OS Q R A B ->
   OS P R A B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E F G, (Col A B E /\ Col A B F /\ BetS Q E G /\ BetS R F G /\ nCol A B Q /\ nCol A B R)) by (conclude_def OS );destruct Tf as [E[F[G]]];spliter.
assert (TS Q A B G) by (conclude_def TS ).
assert (TS P A B G) by (conclude lemma_planeseparation).
let Tf:=fresh in
assert (Tf:exists M, (BetS P M G /\ Col A B M /\ nCol A B P)) by (conclude_def TS );destruct Tf as [M];spliter.
assert (OS P R A B) by (conclude_def OS ).
close.
Qed.

End Euclid.


