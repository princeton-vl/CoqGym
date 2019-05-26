Require Export GeoCoq.Elements.OriginalProofs.lemma_collinearorder.
Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax:euclidean_neutral}.

Lemma lemma_parallelflip : 
   forall A B C D, 
   Par A B C D ->
   Par B A C D /\ Par A B D C /\ Par B A D C.
Proof.
intros.
let Tf:=fresh in
assert (Tf:exists M a b c d, (neq A B /\ neq C D /\ Col A B a /\ Col A B b /\ neq a b /\ Col C D c /\ Col C D d /\ neq c d /\ ~ Meet A B C D /\ BetS a M d /\ BetS c M b)) by (conclude_def Par );destruct Tf as [M[a[b[c[d]]]]];spliter.
assert (Col B A a) by (forward_using lemma_collinearorder).
assert (Col B A b) by (forward_using lemma_collinearorder).
assert (Col D C c) by (forward_using lemma_collinearorder).
assert (Col D C d) by (forward_using lemma_collinearorder).
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (BetS d M a) by (conclude axiom_betweennesssymmetry).
assert (BetS b M c) by (conclude axiom_betweennesssymmetry).
assert (neq d c) by (conclude lemma_inequalitysymmetric).
assert (neq b a) by (conclude lemma_inequalitysymmetric).
assert (~ Meet A B D C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq A B /\ neq D C /\ Col A B P /\ Col D C P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (Col C D P) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Meet B A C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq B A /\ neq C D /\ Col B A P /\ Col C D P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (Col A B P) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (~ Meet B A D C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists P, (neq B A /\ neq D C /\ Col B A P /\ Col D C P)) by (conclude_def Meet );destruct Tf as [P];spliter.
 assert (Col A B P) by (forward_using lemma_collinearorder).
 assert (Col C D P) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (Par B A C D) by (conclude_def Par ).
assert (Par A B D C) by (conclude_def Par ).
assert (Par B A D C) by (conclude_def Par ).
close.
Qed.

End Euclid.


