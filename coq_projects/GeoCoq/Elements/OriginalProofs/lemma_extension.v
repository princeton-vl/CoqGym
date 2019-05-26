Require Export GeoCoq.Elements.OriginalProofs.proposition_02.

Section Euclid.

Context `{Ax:euclidean_neutral_ruler_compass}.

Lemma lemma_extension : 
   forall A B P Q, 
   neq A B -> neq P Q ->
   exists X, BetS A B X /\ Cong B X P Q.
Proof.
intros.
assert (eq B B) by (conclude cn_equalityreflexive).
assert (exists D, Cong B D P Q). 
by cases on (eq B P \/ neq B P).
{
 assert (neq Q P) by (conclude lemma_inequalitysymmetric).
 assert (neq Q B) by (conclude cn_equalitysub).
 assert (neq B Q) by (conclude lemma_inequalitysymmetric).
 let Tf:=fresh in
 assert (Tf:exists D, Cong B D Q P) by (conclude proposition_02);destruct Tf as [D];spliter.
 assert (Cong B D P Q) by (forward_using lemma_congruenceflip).
 close.
 }
{
 let Tf:=fresh in
 assert (Tf:exists D, Cong B D P Q) by (conclude proposition_02);destruct Tf as [D];spliter.
 exists D;auto.
 }
destruct H2 as [D];spliter.
(* cases *)

assert (Cong P Q B D) by (conclude lemma_congruencesymmetric).
assert (neq B D) by (conclude axiom_nocollapse).
let Tf:=fresh in
assert (Tf:exists J, CI J B B D) by (conclude postulate_Euclid3);destruct Tf as [J];spliter.
assert (InCirc B J) by (conclude_def InCirc ).
let Tf:=fresh in
assert (Tf:exists C E, (Col A B C /\ BetS A B E /\ OnCirc C J /\ OnCirc E J /\ BetS C B E)) by (conclude postulate_line_circle);destruct Tf as [C[E]];spliter.
assert (Cong B E B D) by (conclude axiom_circle_center_radius).
assert (Cong B E P Q) by (conclude lemma_congruencetransitive).
close.
Unshelve.
exact A.
exact A.
Qed.

End Euclid.
