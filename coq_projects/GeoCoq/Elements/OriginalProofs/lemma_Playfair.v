Require Export GeoCoq.Elements.OriginalProofs.lemma_Playfairhelper2.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfair : 
   forall A B C D E, 
   Par A B C D -> Par A B C E ->
   Col C D E.
Proof.
intros.
assert (neq A B) by (conclude_def Par ).
assert (neq C D) by (conclude_def Par ).
assert (~ ~ (CR A D B C \/ CR A C B D)).
 {
 intro.
 assert (Par A B D C) by (forward_using lemma_parallelflip).
 assert (CR A C D B) by (conclude lemma_crisscross).
 let Tf:=fresh in
 assert (Tf:exists p, (BetS A p C /\ BetS D p B)) by (conclude_def CR );destruct Tf as [p];spliter.
 assert (neq D B) by (forward_using lemma_betweennotequal).
 assert (neq B D) by (conclude lemma_inequalitysymmetric).
 assert (BetS B p D) by (conclude axiom_betweennesssymmetry).
 assert (CR A C B D) by (conclude_def CR ).
 contradict.
 }
assert (Col C D E).
by cases on (CR A D B C \/ CR A C B D).
{
 assert (Col C D E) by (conclude lemma_Playfairhelper2).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists p, (BetS A p C /\ BetS B p D)) by (conclude_def CR );destruct Tf as [p];spliter.
 assert (CR B D A C) by (conclude_def CR ).
 assert (Par B A C D) by (forward_using lemma_parallelflip).
 assert (Par B A C E) by (forward_using lemma_parallelflip).
 assert (Col C D E) by (conclude lemma_Playfairhelper2).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


