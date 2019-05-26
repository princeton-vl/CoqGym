Require Export GeoCoq.Elements.OriginalProofs.lemma_samesidesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_inequalitysymmetric.

Section Euclid.

Context `{Ax1:euclidean_neutral}.

Lemma lemma_tarskiparallelflip : 
   forall A B C D, 
   TP A B C D ->
   TP B A C D /\ TP A B D C /\ TP B A D C.
Proof.
intros.
assert ((neq A B /\ neq C D /\ ~ Meet A B C D /\ OS C D A B)) by (conclude_def TP ).
assert (OS D C A B) by (forward_using lemma_samesidesymmetric).
assert (neq D C) by (conclude lemma_inequalitysymmetric).
assert (~ Meet A B D C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists T, (neq A B /\ neq D C /\ Col A B T /\ Col D C T)) by (conclude_def Meet );destruct Tf as [T];spliter.
 assert (Col C D T) by (forward_using lemma_collinearorder).
 assert (neq C D) by (conclude lemma_inequalitysymmetric).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (TP A B D C) by (conclude_def TP ).
assert (~ Meet B A C D).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists T, (neq B A /\ neq C D /\ Col B A T /\ Col C D T)) by (conclude_def Meet );destruct Tf as [T];spliter.
 assert (Col A B T) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (neq B A) by (conclude lemma_inequalitysymmetric).
assert (OS D C A B) by (forward_using lemma_samesidesymmetric).
assert (OS C D B A) by (forward_using lemma_samesidesymmetric).
assert (OS D C B A) by (forward_using lemma_samesidesymmetric).
assert (TP B A C D) by (conclude_def TP ).
assert (~ Meet B A D C).
 {
 intro.
 let Tf:=fresh in
 assert (Tf:exists T, (neq B A /\ neq D C /\ Col B A T /\ Col D C T)) by (conclude_def Meet );destruct Tf as [T];spliter.
 assert (Col A B T) by (forward_using lemma_collinearorder).
 assert (Col C D T) by (forward_using lemma_collinearorder).
 assert (Meet A B C D) by (conclude_def Meet ).
 contradict.
 }
assert (TP B A D C) by (conclude_def TP ).
let Tf:=fresh in
assert (Tf:exists Q P R, (Col A B P /\ Col A B R /\ BetS C P Q /\ BetS D R Q /\ nCol A B C /\ nCol A B D)) by (conclude_def OS );destruct Tf as [P[Q[R]]];spliter.
close.
Qed.

End Euclid.


