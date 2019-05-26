Require Export GeoCoq.Elements.OriginalProofs.proposition_31.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma proposition_31short : 
   forall A B C D, 
   BetS B D C -> nCol B C A ->
   exists X Y Z, BetS X A Y /\ CongA X A D A D C /\ Par X Y B C /\ BetS X Z C /\ BetS A Z D.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists E F S, (BetS E A F /\ CongA F A D A D B /\ CongA F A D B D A /\ CongA D A F B D A /\ CongA E A D A D C /\ CongA E A D C D A /\ CongA D A E C D A /\ Par E F B C /\ Cong E A D C /\ Cong A F B D /\ Cong A S S D /\ Cong E S S C /\ Cong B S S F /\ BetS E S C /\ BetS B S F /\ BetS A S D)) by (conclude proposition_31);destruct Tf as [E[F[S]]];spliter.
close.
Qed.

End Euclid.


