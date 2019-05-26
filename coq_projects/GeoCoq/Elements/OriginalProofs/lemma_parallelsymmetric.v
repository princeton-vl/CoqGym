Require Export GeoCoq.Elements.OriginalProofs.euclidean_tactics.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_parallelsymmetric : 
   forall A B C D, 
   Par A B C D ->
   Par C D A B.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists a b c d m, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a m d /\ BetS c m b)) by (conclude_def Par );destruct Tf as [a[b[c[d[m]]]]];spliter.
assert (~ Meet C D A B).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq C D /\ neq A B /\ Col C D P /\ Col A B P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (Par C D A B) by (conclude_def Par ).
close.
Qed.

End Euclid.


