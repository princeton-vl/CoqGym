Require Export GeoCoq.Elements.OriginalProofs.lemma_crisscross.
Require Export GeoCoq.Elements.OriginalProofs.lemma_Playfairhelper.

Section Euclid.

Context `{Ax:euclidean_euclidean}.

Lemma lemma_Playfairhelper2 : 
   forall A B C D E, 
   Par A B C D -> Par A B C E -> CR A D B C ->
   Col C D E.
Proof.
intros.
assert (neq A B) by (conclude_def Par ).
assert (neq C D) by (conclude_def Par ).
assert (~ ~ (CR A E B C \/ CR A C E B)).
 {
 intro.
 assert (Par A B E C) by (forward_using lemma_parallelflip).
 assert (CR A C E B) by (conclude lemma_crisscross).
 contradict.
 }
let Tf:=fresh in
assert (Tf:exists M, (BetS A M D /\ BetS B M C)) by (conclude_def CR );destruct Tf as [M];spliter.
assert (Col C D E).
by cases on (CR A E B C \/ CR A C E B).
{
 assert (Col C D E) by (conclude lemma_Playfairhelper).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists m, (BetS A m C /\ BetS E m B)) by (conclude_def CR );destruct Tf as [m];spliter.
 assert (BetS B m E) by (conclude axiom_betweennesssymmetry).
 assert (neq C E) by (conclude_def Par ).
 assert (neq E C) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists e, (BetS E C e /\ Cong C e E C)) by (conclude lemma_extension);destruct Tf as [e];spliter.
 assert (Col E C e) by (conclude_def Col ).
 assert (neq C e) by (forward_using lemma_betweennotequal).
 assert (neq e C) by (conclude lemma_inequalitysymmetric).
 assert (Par A B E C) by (forward_using lemma_parallelflip).
 assert (Par A B e C) by (conclude lemma_collinearparallel).
 assert (Par A B C e) by (forward_using lemma_parallelflip).
 assert (nCol A C D) by (forward_using lemma_parallelNC).
 assert (nCol A B C) by (forward_using lemma_parallelNC).
 assert (nCol B C A) by (forward_using lemma_NCorder).
 rename_H H;let Tf:=fresh in
 assert (Tf:exists H, (BetS B H m /\ BetS A H M)) by (conclude postulate_Pasch_inner);destruct Tf as [H];spliter.
 assert (nCol A E C) by (forward_using lemma_parallelNC).
 assert (Col E C e) by (conclude_def Col ).
 assert (Col C E e) by (forward_using lemma_collinearorder).
 assert (neq C E) by (conclude lemma_inequalitysymmetric).
 assert (nCol C E A) by (forward_using lemma_NCorder).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Col C E E) by (conclude_def Col ).
 assert (neq E e) by (forward_using lemma_betweennotequal).
 assert (nCol E e A) by (conclude lemma_NChelper).
 let Tf:=fresh in
 assert (Tf:exists F, (BetS A F e /\ BetS E m F)) by (conclude postulate_Pasch_outer);destruct Tf as [F];spliter.
 assert (BetS e F A) by (conclude axiom_betweennesssymmetry).
 assert (Col E m F) by (conclude_def Col ).
 assert (Col E m B) by (conclude_def Col ).
 assert (Col m E F) by (forward_using lemma_collinearorder).
 assert (Col m E B) by (forward_using lemma_collinearorder).
 assert (neq E m) by (forward_using lemma_betweennotequal).
 assert (neq m E) by (conclude lemma_inequalitysymmetric).
 assert (Col E F B) by (conclude lemma_collinear4).
 assert (Col E B F) by (forward_using lemma_collinearorder).
 assert (neq e E) by (conclude lemma_inequalitysymmetric).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Col e E E) by (conclude_def Col ).
 assert (eq B B) by (conclude cn_equalityreflexive).
 assert (Col B B A) by (conclude_def Col ).
 assert (neq B A) by (conclude lemma_inequalitysymmetric).
 assert (Par A B C E) by (forward_using lemma_parallelflip).
 assert (Col C E e) by (forward_using lemma_collinearorder).
 assert (Par A B e E) by (conclude lemma_collinearparallel).
 assert (Par e E A B) by (conclude lemma_parallelsymmetric).
 assert (Par e E B A) by (forward_using lemma_parallelflip).
 assert (~ Meet e E B A) by (conclude_def Par ).
 assert (BetS E F B) by (conclude lemma_collinearbetween).
 assert (BetS B F E) by (conclude axiom_betweennesssymmetry).
 assert (BetS e C E) by (conclude axiom_betweennesssymmetry).
 assert (nCol B E C) by (forward_using lemma_parallelNC).
 assert (nCol E C B) by (forward_using lemma_NCorder).
 assert (Col E C e) by (conclude_def Col ).
 assert (eq E E) by (conclude cn_equalityreflexive).
 assert (Col E C E) by (conclude_def Col ).
 assert (nCol E e B) by (conclude lemma_NChelper).
 assert (nCol B E e) by (forward_using lemma_NCorder).
 let Tf:=fresh in
 assert (Tf:exists K, (BetS B K C /\ BetS e K F)) by (conclude postulate_Pasch_inner);destruct Tf as [K];spliter.
 assert (BetS e F A) by (conclude axiom_betweennesssymmetry).
 assert (BetS e K A) by (conclude lemma_3_6b).
 assert (BetS A K e) by (conclude axiom_betweennesssymmetry).
 assert (neq A e) by (forward_using lemma_betweennotequal).
 assert (CR A e B C) by (conclude_def CR ).
 assert (Col C D e) by (conclude lemma_Playfairhelper).
 assert (Col e C D) by (forward_using lemma_collinearorder).
 assert (Col e C E) by (forward_using lemma_collinearorder).
 assert (neq C e) by (forward_using lemma_betweennotequal).
 assert (neq e C) by (conclude lemma_inequalitysymmetric).
 assert (Col C D E) by (conclude lemma_collinear4).
 close.
 }
(** cases *)
close.
Qed.

End Euclid.


