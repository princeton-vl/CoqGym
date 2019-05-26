Require Export GeoCoq.Elements.OriginalProofs.lemma_samenotopposite.
Require Export GeoCoq.Elements.OriginalProofs.lemma_crisscross.
Require Export GeoCoq.Elements.OriginalProofs.proposition_33.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma proposition_33B : 
   forall A B C D, 
   Par A B C D -> Cong A B C D -> OS A C B D ->
   Par A C B D /\ Cong A C B D.
Proof.
intros.
assert (~ CR A C B D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists M, (BetS A M C /\ BetS B M D)) by (conclude_def CR );destruct Tf as [M];spliter.
 assert (Col B M D) by (conclude_def Col ).
 assert (Col B D M) by (forward_using lemma_collinearorder).
 assert (nCol A B D) by (forward_using lemma_parallelNC).
 assert (nCol B D A) by (forward_using lemma_NCorder).
 assert (TS A B D C) by (conclude_def TS ).
 assert (~ TS A B D C) by (conclude lemma_samenotopposite).
 contradict.
 }
assert (CR A D C B) by (conclude lemma_crisscross).
let Tf:=fresh in
assert (Tf:exists m, (BetS A m D /\ BetS C m B)) by (conclude_def CR );destruct Tf as [m];spliter.
assert (BetS B m C) by (conclude axiom_betweennesssymmetry).
assert ((Par A C B D /\ Cong A C B D)) by (conclude proposition_33).
close.
Qed.

End Euclid.


